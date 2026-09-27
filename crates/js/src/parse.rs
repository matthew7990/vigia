//! Recursive-descent parser. Standard JS precedence, low to high:
//! assign < ternary < || < && < equality < relational(+in) < additive <
//! multiplicative < unary < postfix < call/member < primary.
//!
//! Statement end: `;` optional before `}`, EOF, or a token preceded by a
//! newline (ASI-lite). `return <newline>` means `return;`, like real ASI.

use std::rc::Rc;

use crate::ast::{
    ClassMember, Expr, FnDef, MemberKind, ObjEntry, ObjField, OptOp, Pat, Stmt, VarDecl,
};
use crate::eval::fmt_num;
use crate::lex::{lex, Tok, Token};
use crate::{err, JsError};

/// ~15 recursion frames per nested level; 400 stays well under the stack.
const MAX_DEPTH: u32 = 400;

pub fn parse_program(src: &str) -> Result<Vec<Stmt>, JsError> {
    let t = lex(src)?;
    let mut p = P {
        t,
        i: 0,
        depth: 0,
        in_fn: 0,
        in_loop: 0,
        in_switch: 0,
        in_label: 0,
        labels: Vec::new(),
        super_ok: false,
    };
    let mut stmts = Vec::new();
    while !p.at_eof() {
        stmts.push(p.stmt()?);
    }
    Ok(stmts)
}

struct P {
    t: Vec<Token>,
    i: usize,
    depth: u32,
    in_fn: u32,
    in_loop: u32,
    in_switch: u32,
    in_label: u32,
    /// Enclosing label names with the fn depth where they were declared
    /// (`break`/`continue` cannot cross a function boundary).
    labels: Vec<(String, u32)>,
    /// `super` parses only inside a derived class body (methods and
    /// field inits inherit it; plain functions reset it, arrows keep it).
    super_ok: bool,
}

type R<T> = Result<T, JsError>;

/// `(params, rest)` of a function or arrow head.
type Params = (Vec<(String, Option<Expr>)>, Option<String>);

/// Flatten `a.b[k](x)` into `a` + non-optional steps so an optional chain
/// keeps the receiver for `this`. `a.b?.()` becomes Chain(a, [Member(b),
/// Call?.]) instead of Chain(Member(a,b), [Call?.]).
fn split_chain(e: Expr) -> (Expr, Vec<OptOp>) {
    match e {
        Expr::Member(o, n) => {
            let (b, mut ops) = split_chain(*o);
            ops.push(OptOp::Member(n, false));
            (b, ops)
        }
        Expr::Index(o, k) => {
            let (b, mut ops) = split_chain(*o);
            ops.push(OptOp::Index(*k, false));
            (b, ops)
        }
        Expr::Call(c, a) => {
            let (b, mut ops) = split_chain(*c);
            ops.push(OptOp::Call(a, false));
            (b, ops)
        }
        other => (other, Vec::new()),
    }
}

impl P {
    fn peek(&self) -> &Tok {
        &self.t[self.i].t
    }

    fn pos(&self) -> usize {
        self.t[self.i].pos
    }

    fn nl(&self) -> bool {
        self.t[self.i].nl
    }

    fn at_p(&self, p: &str) -> bool {
        matches!(self.peek(), Tok::P(x) if *x == p)
    }

    fn at_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Kw(x) if *x == k)
    }

    /// Token after the current one is `(`: distinguishes `get()` (a
    /// method named get) from `get x()` (an accessor).
    fn next_is_paren(&self) -> bool {
        matches!(self.t.get(self.i + 1).map(|t| &t.t), Some(Tok::P("(")))
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek(), Tok::Eof)
    }

    fn bump(&mut self) -> Tok {
        let t = self.t[self.i].t.clone();
        self.i += 1;
        t
    }

    fn eat_p(&mut self, p: &str) -> bool {
        if self.at_p(p) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, k: &str) -> bool {
        if matches!(self.peek(), Tok::Kw(x) if *x == k) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn exp_p(&mut self, p: &str) -> R<()> {
        if self.eat_p(p) {
            Ok(())
        } else {
            Err(self.unexp(&format!("expected '{p}'")))
        }
    }

    fn unexp(&self, what: &str) -> JsError {
        err(format!(
            "{what}, got {:?} at byte {}",
            self.peek(),
            self.pos()
        ))
    }

    fn ident(&mut self) -> R<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.i += 1;
                Ok(s)
            }
            _ => Err(self.unexp("expected identifier")),
        }
    }

    /// Name after `.`: identifiers and keywords both allowed (`a.in`).
    fn prop_name(&mut self) -> R<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.i += 1;
                Ok(s)
            }
            Tok::Kw(k) => {
                self.i += 1;
                Ok(k.to_string())
            }
            _ => Err(self.unexp("expected property name")),
        }
    }

    /// Accessor/method name in literals: like prop_name plus strings and
    /// numbers (`get "x"()`, `{0() {}}`). No computed keys.
    fn acc_name(&mut self) -> R<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.i += 1;
                Ok(s)
            }
            Tok::Kw(k) => {
                self.i += 1;
                Ok(k.to_string())
            }
            Tok::Str(s) => {
                self.i += 1;
                Ok(s)
            }
            Tok::Num(n) => {
                self.i += 1;
                Ok(fmt_num(n))
            }
            _ => Err(self.unexp("expected accessor name")),
        }
    }

    /// ASI-lite: accept `;`, `}`, EOF, or a newline before the next token.
    fn semi(&mut self) -> R<()> {
        if self.eat_p(";") || self.at_p("}") || self.at_eof() || self.nl() {
            Ok(())
        } else {
            Err(self.unexp("expected ';'"))
        }
    }

    fn stmt(&mut self) -> R<Stmt> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(err("nesting too deep"));
        }
        let r = self.stmt_inner();
        self.depth -= 1;
        r
    }

    fn stmt_inner(&mut self) -> R<Stmt> {
        match self.peek().clone() {
            Tok::P(";") => {
                self.i += 1;
                Ok(Stmt::Block(vec![]))
            }
            Tok::P("{") => {
                self.i += 1;
                Ok(Stmt::Block(self.block_body()?))
            }
            Tok::Kw("var") | Tok::Kw("let") | Tok::Kw("const") => {
                self.i += 1;
                let d = self.var_decls()?;
                self.semi()?;
                Ok(Stmt::VarDecl(d))
            }
            Tok::Kw("function") => {
                self.i += 1;
                let n = self
                    .ident()
                    .map_err(|_| err("function declaration needs a name"))?;
                Ok(Stmt::FnDecl(self.fn_tail(Some(n), false)?))
            }
            Tok::Kw("async") => {
                self.i += 1;
                if !self.eat_kw("function") {
                    return Err(err("expected 'function' after 'async'"));
                }
                let n = self
                    .ident()
                    .map_err(|_| err("async function declaration needs a name"))?;
                Ok(Stmt::FnDecl(self.fn_tail(Some(n), true)?))
            }
            Tok::Kw("return") => {
                if self.in_fn == 0 {
                    return Err(err("return outside function"));
                }
                self.i += 1;
                let e = if self.at_p(";") || self.at_p("}") || self.at_eof() || self.nl() {
                    None
                } else {
                    Some(self.expr()?)
                };
                self.semi()?;
                Ok(Stmt::Return(e))
            }
            Tok::Kw("if") => {
                self.i += 1;
                self.exp_p("(")?;
                let c = self.expr()?;
                self.exp_p(")")?;
                let t = Box::new(self.stmt()?);
                let e = if self.eat_kw("else") {
                    Some(Box::new(self.stmt()?))
                } else {
                    None
                };
                Ok(Stmt::If(c, t, e))
            }
            Tok::Kw("while") => {
                self.i += 1;
                self.exp_p("(")?;
                let c = self.expr()?;
                self.exp_p(")")?;
                self.in_loop += 1;
                let b = self.stmt();
                self.in_loop -= 1;
                Ok(Stmt::While(c, Box::new(b?)))
            }
            Tok::Kw("do") => {
                self.i += 1;
                self.in_loop += 1;
                let b = self.stmt();
                self.in_loop -= 1;
                let b = b?;
                if !self.eat_kw("while") {
                    return Err(err("expected 'while' after 'do' body"));
                }
                self.exp_p("(")?;
                let c = self.expr()?;
                self.exp_p(")")?;
                self.semi()?;
                Ok(Stmt::DoWhile(Box::new(b), c))
            }
            Tok::Kw("for") => self.for_stmt(),
            Tok::Kw("switch") => self.switch_stmt(),
            Tok::Kw("class") => {
                self.i += 1;
                let n = self
                    .ident()
                    .map_err(|_| err("class declaration needs a name"))?;
                let c = self.parse_class(Some(n.clone()))?;
                Ok(Stmt::ClassDecl(n, c))
            }
            Tok::Kw("throw") => {
                self.i += 1;
                // real ASI: a newline between throw and its expr is an error
                if self.nl() {
                    return Err(err("newline after 'throw'"));
                }
                if self.at_p(";") || self.at_p("}") || self.at_eof() {
                    return Err(err("throw needs an expression"));
                }
                let e = self.expr()?;
                self.semi()?;
                Ok(Stmt::Throw(e))
            }
            Tok::Kw("try") => self.try_stmt(),
            Tok::Kw("break") | Tok::Kw("continue") => {
                let is_break = matches!(self.peek(), Tok::Kw("break"));
                self.i += 1;
                // `break foo` / `continue foo`: label on the same line.
                let label = match self.peek().clone() {
                    Tok::Ident(s) if !self.nl() => {
                        self.i += 1;
                        Some(s)
                    }
                    _ => None,
                };
                if let Some(ref l) = label {
                    if !self.labels.iter().any(|(n, d)| n == l && *d == self.in_fn) {
                        return Err(err(format!("no such label: {l}")));
                    }
                }
                // Unlabeled `break` also escapes a switch or a labeled
                // block; unlabeled `continue` needs a real loop.
                let ok = if label.is_some() {
                    true
                } else if is_break {
                    self.in_loop > 0 || self.in_switch > 0 || self.in_label > 0
                } else {
                    self.in_loop > 0
                };
                if !ok {
                    return Err(err("break/continue outside loop"));
                }
                self.semi()?;
                Ok(if is_break {
                    Stmt::Break(label)
                } else {
                    Stmt::Continue(label)
                })
            }
            Tok::Ident(n) if matches!(self.t.get(self.i + 1).map(|t| &t.t), Some(Tok::P(":"))) => {
                // `name: stmt` - a labeled statement, break/continue target.
                self.i += 2;
                self.in_label += 1;
                self.labels.push((n.clone(), self.in_fn));
                let b = self.stmt();
                self.labels.pop();
                self.in_label -= 1;
                Ok(Stmt::Label(n, Box::new(b?)))
            }
            _ => {
                let e = self.expr()?;
                self.semi()?;
                Ok(Stmt::Expr(e))
            }
        }
    }

    /// try {} [catch[(ident)] {}] [finally {}] - at least one clause is
    /// required; the catch binding (when present) is a single identifier.
    fn try_stmt(&mut self) -> R<Stmt> {
        self.i += 1; // 'try'
        self.exp_p("{")?;
        let body = self.block_body()?;
        let catch = if self.eat_kw("catch") {
            let param = if self.eat_p("(") {
                let p = self.ident()?;
                self.exp_p(")")?;
                Some(p)
            } else {
                None
            };
            self.exp_p("{")?;
            Some((param, self.block_body()?))
        } else {
            None
        };
        let finally = if self.eat_kw("finally") {
            self.exp_p("{")?;
            Some(self.block_body()?)
        } else {
            None
        };
        if catch.is_none() && finally.is_none() {
            return Err(err("'try' needs 'catch' or 'finally'"));
        }
        Ok(Stmt::Try {
            body,
            catch,
            finally,
        })
    }

    /// Body of a `{ ... }` block; `{` already consumed.
    fn block_body(&mut self) -> R<Vec<Stmt>> {
        let mut v = Vec::new();
        while !self.eat_p("}") {
            if self.at_eof() {
                return Err(err("unterminated block"));
            }
            v.push(self.stmt()?);
        }
        Ok(v)
    }

    fn var_decls(&mut self) -> R<Vec<VarDecl>> {
        let mut v = Vec::new();
        loop {
            if self.at_p("[") || self.at_p("{") {
                let pat = self.pattern()?;
                self.exp_p("=")?;
                let init = self.assign()?;
                v.push(VarDecl::Pat(pat, init));
            } else {
                let name = self.ident()?;
                let init = if self.eat_p("=") {
                    Some(self.assign()?)
                } else {
                    None
                };
                v.push(VarDecl::Plain(name, init));
            }
            if !self.eat_p(",") {
                break;
            }
        }
        Ok(v)
    }

    /// `[a, , b=1, ...r]` or `{x, y: [z], w=2, ...rest}`. Leaves are plain
    /// identifiers (plus nested patterns); no computed keys, no member
    /// targets.
    fn pattern(&mut self) -> R<Pat> {
        if self.eat_p("[") {
            let mut els: Vec<Option<(Pat, Option<Expr>)>> = Vec::new();
            let mut rest = None;
            if !self.at_p("]") {
                loop {
                    if self.eat_p(",") {
                        els.push(None);
                        if self.eat_p("]") {
                            break;
                        }
                        continue;
                    }
                    if self.eat_p("...") {
                        rest = Some(self.ident()?);
                        self.exp_p("]")?;
                        break;
                    }
                    let p = self.pattern_leaf()?;
                    let d = if self.eat_p("=") {
                        Some(self.assign()?)
                    } else {
                        None
                    };
                    els.push(Some((p, d)));
                    if self.eat_p("]") {
                        break;
                    }
                    self.exp_p(",")?;
                    if self.eat_p("]") {
                        break; // trailing comma
                    }
                }
            } else {
                self.eat_p("]");
            }
            Ok(Pat::Arr(els, rest))
        } else if self.eat_p("{") {
            let mut fields = Vec::new();
            let mut rest = None;
            if !self.eat_p("}") {
                loop {
                    if self.eat_p("...") {
                        rest = Some(self.ident()?);
                        self.exp_p("}")?;
                        break;
                    }
                    let key = match self.bump() {
                        Tok::Ident(s) => s,
                        Tok::Kw(k) => k.to_string(),
                        Tok::Str(s) => s,
                        Tok::Num(n) => fmt_num(n),
                        t => return Err(err(format!("expected field name, got {t:?}"))),
                    };
                    let (pat, default) = if self.eat_p(":") {
                        let p = self.pattern_leaf()?;
                        let d = if self.eat_p("=") {
                            Some(self.assign()?)
                        } else {
                            None
                        };
                        (p, d)
                    } else {
                        // Shorthand: `{x}` = `{x: x}`, plus `{x = d}`.
                        let d = if self.eat_p("=") {
                            Some(self.assign()?)
                        } else {
                            None
                        };
                        (Pat::Ident(key.clone()), d)
                    };
                    fields.push(ObjField { key, pat, default });
                    if self.eat_p("}") {
                        break;
                    }
                    self.exp_p(",")?;
                    if self.eat_p("}") {
                        break; // trailing comma
                    }
                }
            }
            Ok(Pat::Obj(fields, rest))
        } else {
            Err(err("expected pattern"))
        }
    }

    /// One pattern position: nested pattern or a bare identifier.
    fn pattern_leaf(&mut self) -> R<Pat> {
        if self.at_p("[") || self.at_p("{") {
            self.pattern()
        } else {
            Ok(Pat::Ident(self.ident()?))
        }
    }

    /// `(params) { body }` shared by fn declarations and fn expressions.
    /// `is_async` marks `async function` bodies (enables `await`, wraps the
    /// return value in a promise at call time).
    fn fn_tail(&mut self, name: Option<String>, is_async: bool) -> R<Rc<FnDef>> {
        self.exp_p("(")?;
        let (params, rest) = self.param_list()?;
        self.exp_p(")")?;
        self.exp_p("{")?;
        self.in_fn += 1;
        // Plain functions never see `super` (arrows inherit the flag).
        let save_super = self.super_ok;
        self.super_ok = false;
        let body = self.block_body();
        self.super_ok = save_super;
        self.in_fn -= 1;
        Ok(Rc::new(FnDef {
            name,
            params,
            body: body?,
            is_async,
            is_arrow: false,
            rest,
            cls: None,
        }))
    }

    /// `(a, b=1, ...r)`: plain idents, `=` defaults, one trailing rest.
    fn param_list(&mut self) -> R<Params> {
        let mut params = Vec::new();
        let mut rest = None;
        if !self.at_p(")") {
            loop {
                if self.eat_p("...") {
                    rest = Some(self.ident()?);
                    break;
                }
                let n = self.ident()?;
                let d = if self.eat_p("=") {
                    Some(self.assign()?)
                } else {
                    None
                };
                params.push((n, d));
                if !self.eat_p(",") {
                    break;
                }
                if self.at_p(")") {
                    break;
                }
            }
        }
        if rest.is_some() && !self.at_p(")") {
            return Err(err("rest param must be last"));
        }
        Ok((params, rest))
    }

    /// `x => e`, `(a,b) => e`, `(a) => { stmts }`, plus `async` variants.
    /// Returns None without consuming when the head is not an arrow.
    fn try_arrow(&mut self) -> R<Option<Expr>> {
        let save = self.i;
        let save_fn = self.in_fn;
        let is_async = if matches!(self.peek(), Tok::Kw("async")) {
            // `async function` is not an arrow.
            if matches!(
                self.t.get(self.i + 1).map(|t| &t.t),
                Some(Tok::Kw("function"))
            ) {
                return Ok(None);
            }
            self.i += 1;
            // `async` newline `x =>` still counts; `async` alone does not.
            if matches!(self.peek(), Tok::Eof) {
                self.i = save;
                return Ok(None);
            }
            true
        } else {
            false
        };
        let (params, rest) = if matches!(self.peek(), Tok::Ident(_)) {
            let n = self.ident()?;
            // `x =>` only: `x + 1` must fall back to normal assign.
            if !self.at_p("=>") {
                self.i = save;
                return Ok(None);
            }
            (vec![(n, None)], None)
        } else if self.at_p("(") {
            self.i += 1;
            let (ps, rest) = match self.param_list() {
                // Not a param list (or a bad rest): not an arrow; let the
                // normal expression parse report it.
                Err(_) => {
                    self.i = save;
                    return Ok(None);
                }
                Ok(v) => v,
            };
            if !self.eat_p(")") || !self.at_p("=>") {
                self.i = save;
                return Ok(None);
            }
            (ps, rest)
        } else {
            self.i = save;
            return Ok(None);
        };
        // Consume `=>`.
        self.i += 1;
        self.in_fn += 1;
        let body = if self.at_p("{") {
            self.i += 1;
            let b = self.block_body()?;
            self.in_fn -= 1;
            b
        } else {
            // Expression body: implicit return. A nested arrow stays
            // right-assoc because expr body parses via assign().
            let e = self.assign()?;
            self.in_fn = save_fn;
            return Ok(Some(Expr::Func(Rc::new(FnDef {
                name: None,
                params,
                body: vec![Stmt::Return(Some(e))],
                is_async,
                is_arrow: true,
                rest,
                cls: None,
            }))));
        };
        Ok(Some(Expr::Func(Rc::new(FnDef {
            name: None,
            params,
            body,
            is_async,
            is_arrow: true,
            rest,
            cls: None,
        }))))
    }

    /// `switch (d) { case e: stmts...; default: stmts... }`. One default
    /// max; clauses run to `}` (the next `case`/`default` starts another).
    fn switch_stmt(&mut self) -> R<Stmt> {
        self.i += 1; // 'switch'
        self.exp_p("(")?;
        let disc = self.expr()?;
        self.exp_p(")")?;
        self.exp_p("{")?;
        let mut cases: Vec<(Option<Expr>, Vec<Stmt>)> = Vec::new();
        let mut defaulted = false;
        self.in_switch += 1;
        loop {
            if self.eat_p("}") {
                break;
            }
            if self.at_eof() {
                return Err(err("unterminated switch"));
            }
            let test = if self.eat_kw("case") {
                Some(self.expr()?)
            } else if self.eat_kw("default") {
                if defaulted {
                    return Err(err("duplicate default in switch"));
                }
                defaulted = true;
                None
            } else {
                return Err(self.unexp("expected 'case' or 'default'"));
            };
            self.exp_p(":")?;
            let mut body = Vec::new();
            while !self.at_p("}") && !self.at_kw("case") && !self.at_kw("default") && !self.at_eof()
            {
                body.push(self.stmt()?);
            }
            cases.push((test, body));
        }
        self.in_switch -= 1;
        Ok(Stmt::Switch { disc, cases })
    }

    /// `class Name extends Sup { ... }`. Members: constructor, methods,
    /// statics, get/set, fields. No computed keys, no `#private`, no
    /// static blocks, no decorators.
    fn parse_class(&mut self, name: Option<String>) -> R<Expr> {
        let parent = if self.eat_kw("extends") {
            Some(Box::new(self.class_parent()?))
        } else {
            None
        };
        self.exp_p("{")?;
        let mut members = Vec::new();
        let mut ctor_seen = false;
        let save_super = self.super_ok;
        self.super_ok = parent.is_some();
        macro_rules! bail {
            ($msg:literal) => {{
                self.super_ok = save_super;
                return Err(err($msg));
            }};
        }
        loop {
            if self.eat_p("}") {
                break;
            }
            if self.at_eof() {
                bail!("unterminated class");
            }
            if matches!(self.peek(), Tok::P(p) if *p == ";") {
                self.i += 1;
                continue;
            }
            // `static` modifier, or a member literally named `static`.
            let mut statik = false;
            if matches!(self.peek(), Tok::Ident(s) if s == "static") {
                self.i += 1;
                if self.at_p("{") {
                    bail!("static blocks unsupported");
                }
                if !self.at_p("(") && !self.at_p("=") && !self.at_p(";") && !self.nl() {
                    statik = true;
                } else if self.at_p("(") {
                    // Method named `static`.
                    let (params, rest) = self.method_params()?;
                    let body = self.method_body()?;
                    members.push(ClassMember {
                        statik: false,
                        kind: MemberKind::Method(
                            "static".into(),
                            Rc::new(FnDef {
                                name: Some("static".into()),
                                params,
                                body,
                                is_async: false,
                                is_arrow: false,
                                rest,
                                cls: None,
                            }),
                        ),
                    });
                    continue;
                } else {
                    // Field named `static`.
                    let init = self.field_init()?;
                    members.push(ClassMember {
                        statik: false,
                        kind: MemberKind::Field("static".into(), init),
                    });
                    continue;
                }
            }
            // `async m(){}` vs a member named `async` (`async()`,
            // `async = 1`, `async;`).
            let mut is_async = false;
            if matches!(self.peek(), Tok::Kw("async")) {
                let modifier = !matches!(
                    self.t.get(self.i + 1).map(|t| &t.t),
                    Some(Tok::P("(" | "=" | ";" | "}")) | Some(Tok::Eof) | None
                );
                if modifier {
                    self.i += 1;
                    is_async = true;
                }
            }
            if self.eat_p("*") {
                bail!("generators unsupported");
            }
            // get/set accessors (a `(` right after means a method named
            // get/set instead).
            if matches!(self.peek(), Tok::Ident(s) if s == "get" || s == "set")
                && !self.next_is_paren()
            {
                let is_get = matches!(self.peek(), Tok::Ident(s) if s == "get");
                self.i += 1;
                let prop = self.acc_name()?;
                if prop == "constructor" {
                    bail!("class constructor may not be an accessor");
                }
                self.exp_p("(")?;
                let (params, rest) = self.param_list()?;
                if rest.is_some() {
                    bail!("rest in accessor params");
                }
                self.exp_p(")")?;
                if is_async {
                    bail!("async accessor unsupported");
                }
                let body = self.method_body()?;
                if is_get {
                    if !params.is_empty() {
                        bail!("getter takes no params");
                    }
                    members.push(ClassMember {
                        statik,
                        kind: MemberKind::Get(
                            prop.clone(),
                            Rc::new(FnDef {
                                name: Some(prop),
                                params,
                                body,
                                is_async: false,
                                is_arrow: false,
                                rest,
                                cls: None,
                            }),
                        ),
                    });
                } else {
                    if params.len() != 1 || params[0].1.is_some() {
                        bail!("setter takes one plain param");
                    }
                    members.push(ClassMember {
                        statik,
                        kind: MemberKind::Set(
                            prop.clone(),
                            Rc::new(FnDef {
                                name: Some(prop),
                                params,
                                body,
                                is_async: false,
                                is_arrow: false,
                                rest,
                                cls: None,
                            }),
                        ),
                    });
                }
                // No separator needed after methods/accessors/ctors -
                // the loop top handles `}` and the next member follows.
                continue;
            }
            let key = self.acc_name()?;
            if key == "constructor" && !statik && self.at_p("(") {
                if ctor_seen {
                    bail!("duplicate constructor");
                }
                ctor_seen = true;
                if is_async {
                    bail!("async constructor unsupported");
                }
                self.exp_p("(")?;
                let (params, rest) = self.param_list()?;
                self.exp_p(")")?;
                let body = self.method_body()?;
                members.push(ClassMember {
                    statik: false,
                    kind: MemberKind::Ctor { params, rest, body },
                });
                continue;
            }
            if key == "constructor" && statik {
                bail!("static constructor unsupported");
            }
            if self.at_p("(") {
                self.exp_p("(")?;
                let (params, rest) = self.param_list()?;
                self.exp_p(")")?;
                let body = self.method_body()?;
                members.push(ClassMember {
                    statik,
                    kind: MemberKind::Method(
                        key.clone(),
                        Rc::new(FnDef {
                            name: Some(key),
                            params,
                            body,
                            is_async,
                            is_arrow: false,
                            rest,
                            cls: None,
                        }),
                    ),
                });
                continue;
            }
            // Field: `x = init`, `x;`, `x }` or `x <newline>`.
            let init = self.field_init()?;
            members.push(ClassMember {
                statik,
                kind: MemberKind::Field(key, init),
            });
        }
        self.super_ok = save_super;
        Ok(Expr::Class {
            name,
            parent,
            members,
        })
    }

    /// `(params)` of a class method named `static` (parens confirmed).
    fn method_params(&mut self) -> R<Params> {
        self.exp_p("(")?;
        let (params, rest) = self.param_list()?;
        self.exp_p(")")?;
        Ok((params, rest))
    }

    /// `{ stmts }` of a class method or constructor.
    fn method_body(&mut self) -> R<Vec<Stmt>> {
        self.exp_p("{")?;
        self.in_fn += 1;
        let body = self.block_body();
        self.in_fn -= 1;
        body
    }

    /// Initializer of a class field after the name: `= expr`, `;`,
    /// `}` or a newline ends it.
    fn field_init(&mut self) -> R<Option<Expr>> {
        if self.eat_p("=") {
            let e = self.assign()?;
            self.member_end()?;
            Ok(Some(e))
        } else {
            self.member_end()?;
            Ok(None)
        }
    }

    /// End of a class field/accessor: `;`, `}`, or a newline before next.
    fn member_end(&mut self) -> R<()> {
        if self.eat_p(";") || self.at_p("}") || self.nl() {
            Ok(())
        } else {
            Err(self.unexp("expected ';'"))
        }
    }

    /// Heritage expression: member chain with an optional call
    /// (`extends M(B)` for mixins). No arithmetic.
    fn class_parent(&mut self) -> R<Expr> {
        let mut c = self.primary()?;
        loop {
            if self.eat_p(".") {
                c = Expr::Member(Box::new(c), self.prop_name()?);
            } else if self.eat_p("[") {
                let k = self.expr()?;
                self.exp_p("]")?;
                c = Expr::Index(Box::new(c), Box::new(k));
            } else {
                break;
            }
        }
        self.call_tail(c)
    }

    fn try_for_of(&mut self) -> R<Option<Stmt>> {
        let save = self.i;
        let is_decl = matches!(
            self.peek(),
            Tok::Kw("var") | Tok::Kw("let") | Tok::Kw("const")
        );
        if is_decl {
            self.i += 1;
        }
        let name = match self.peek().clone() {
            Tok::Ident(s) => {
                self.i += 1;
                s
            }
            _ => {
                self.i = save;
                return Ok(None);
            }
        };
        let is_of = matches!(self.peek(), Tok::Ident(s) if s == "of");
        let is_in = matches!(self.peek(), Tok::Kw("in"))
            || matches!(self.peek(), Tok::Ident(s) if s == "in");
        if !is_of && !is_in {
            self.i = save;
            return Ok(None);
        }
        self.i += 1; // 'of' / 'in'
        let target = self.expr()?;
        self.exp_p(")")?;
        self.in_loop += 1;
        let b = self.stmt();
        self.in_loop -= 1;
        Ok(Some(if is_of {
            Stmt::ForOf {
                name,
                is_decl,
                iter: target,
                body: Box::new(b?),
            }
        } else {
            Stmt::ForIn {
                name,
                is_decl,
                obj: target,
                body: Box::new(b?),
            }
        }))
    }

    fn for_stmt(&mut self) -> R<Stmt> {
        self.i += 1; // 'for'
        self.exp_p("(")?;
        if let Some(f) = self.try_for_of()? {
            return Ok(f);
        }
        let init = if self.eat_p(";") {
            None
        } else if matches!(
            self.peek(),
            Tok::Kw("var") | Tok::Kw("let") | Tok::Kw("const")
        ) {
            self.i += 1;
            let d = self.var_decls()?;
            self.exp_p(";")?;
            Some(Box::new(Stmt::VarDecl(d)))
        } else {
            let e = self.expr()?;
            self.exp_p(";")?;
            Some(Box::new(Stmt::Expr(e)))
        };
        let test = if self.at_p(";") {
            None
        } else {
            Some(self.expr()?)
        };
        self.exp_p(";")?;
        let upd = if self.at_p(")") {
            None
        } else {
            Some(self.expr()?)
        };
        self.exp_p(")")?;
        self.in_loop += 1;
        let b = self.stmt();
        self.in_loop -= 1;
        Ok(Stmt::For(init, test, upd, Box::new(b?)))
    }

    // ---- expressions -------------------------------------------------

    fn expr(&mut self) -> R<Expr> {
        // Comma sequence (lowest precedence): `a, b` evals both, yields b.
        // Callers needing AssignmentExpression (args, array/obj literals,
        // var inits) call assign() directly so separators keep working.
        let mut l = self.assign()?;
        while self.eat_p(",") {
            let r = self.assign()?;
            l = Expr::Bin(",", Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn assign(&mut self) -> R<Expr> {
        if let Some(a) = self.try_arrow()? {
            return Ok(a);
        }
        let l = self.ternary()?;
        let op = match self.peek() {
            Tok::P(p) => *p,
            _ => return Ok(l),
        };
        if !matches!(
            op,
            "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" | ">>>="
        ) {
            return Ok(l);
        }
        if !matches!(l, Expr::Ident(_) | Expr::Member(..) | Expr::Index(..)) {
            return Err(err("bad assignment target"));
        }
        self.i += 1;
        let r = self.assign()?;
        Ok(Expr::Assign(op, Box::new(l), Box::new(r)))
    }

    fn ternary(&mut self) -> R<Expr> {
        let c = self.lor()?;
        if !self.eat_p("?") {
            return Ok(c);
        }
        let t = self.assign()?;
        self.exp_p(":")?;
        // False branch is AssignmentExpression (right-assoc nesting and
        // `a?b:c=d` both need assign, not ternary).
        let f = self.assign()?;
        Ok(Expr::Ternary(Box::new(c), Box::new(t), Box::new(f)))
    }

    fn lor(&mut self) -> R<Expr> {
        // `??` shares this level (permissive: mixing with || is allowed).
        self.binop(Self::land, &["||", "??"])
    }

    fn land(&mut self) -> R<Expr> {
        self.binop(Self::bor, &["&&"])
    }

    fn bor(&mut self) -> R<Expr> {
        self.binop(Self::bxor, &["|"])
    }

    fn bxor(&mut self) -> R<Expr> {
        self.binop(Self::band, &["^"])
    }

    fn band(&mut self) -> R<Expr> {
        self.binop(Self::eq, &["&"])
    }

    fn eq(&mut self) -> R<Expr> {
        self.binop(Self::rel, &["==", "!=", "===", "!=="])
    }

    fn rel(&mut self) -> R<Expr> {
        self.binop(Self::shift, &["<", "<=", ">", ">=", "in", "instanceof"])
    }

    fn shift(&mut self) -> R<Expr> {
        self.binop(Self::add, &["<<", ">>", ">>>"])
    }

    fn add(&mut self) -> R<Expr> {
        self.binop(Self::mul, &["+", "-"])
    }

    fn mul(&mut self) -> R<Expr> {
        self.binop(Self::unary, &["*", "/", "%"])
    }

    fn binop(&mut self, sub: fn(&mut Self) -> R<Expr>, ops: &[&'static str]) -> R<Expr> {
        let mut l = sub(self)?;
        loop {
            let op = match self.peek() {
                Tok::P(p) if ops.contains(p) => *p,
                Tok::Kw(k) if ops.contains(k) => *k,
                _ => break,
            };
            self.i += 1;
            let r = sub(self)?;
            l = Expr::Bin(op, Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn unary(&mut self) -> R<Expr> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(err("expression too deep"));
        }
        let r = self.unary_inner();
        self.depth -= 1;
        r
    }

    fn unary_inner(&mut self) -> R<Expr> {
        let op = match self.peek() {
            Tok::P(p) if matches!(*p, "!" | "~" | "+" | "-" | "++" | "--") => *p,
            Tok::Kw("typeof") => "typeof",
            // `await` parses everywhere; eval rejects it outside async fns.
            Tok::Kw("await") => "await",
            Tok::Kw("void") => "void",
            Tok::Kw("delete") => "delete",
            Tok::Kw("new") => "new",
            _ => "",
        };
        match op {
            "!" | "~" | "+" | "-" => {
                self.i += 1;
                Ok(Expr::Unary(op, Box::new(self.unary()?)))
            }
            "++" | "--" => {
                self.i += 1;
                let e = self.unary()?;
                if !matches!(e, Expr::Ident(_) | Expr::Member(..) | Expr::Index(..)) {
                    return Err(err("bad ++/-- target"));
                }
                Ok(Expr::Unary(op, Box::new(e)))
            }
            "typeof" | "await" | "void" | "delete" => {
                self.i += 1;
                Ok(Expr::Unary(op, Box::new(self.unary()?)))
            }
            "new" => {
                self.i += 1;
                let e = self.new_expr()?;
                self.call_tail(e)
            }
            _ => self.postfix(),
        }
    }

    /// `new` callee binds tighter than the call: `new a.b(1)` is
    /// New(Member(a,b), [1]), not Call on a New.
    fn new_expr(&mut self) -> R<Expr> {
        let mut c = self.primary()?;
        loop {
            if self.eat_p(".") {
                c = Expr::Member(Box::new(c), self.prop_name()?);
            } else if self.eat_p("[") {
                let k = self.expr()?;
                self.exp_p("]")?;
                c = Expr::Index(Box::new(c), Box::new(k));
            } else {
                break;
            }
        }
        let args = if self.at_p("(") {
            self.args()?
        } else {
            Vec::new()
        };
        Ok(Expr::New(Box::new(c), args))
    }

    fn postfix(&mut self) -> R<Expr> {
        let e = self.call()?;
        // a newline before ++/-- ends the statement (real ASI rule)
        let op = match self.peek() {
            Tok::P(p) if !self.nl() => *p,
            _ => return Ok(e),
        };
        if !matches!(op, "++" | "--") {
            return Ok(e);
        }
        if !matches!(e, Expr::Ident(_) | Expr::Member(..) | Expr::Index(..)) {
            return Err(err("bad ++/-- target"));
        }
        self.i += 1;
        Ok(Expr::Postfix(op, Box::new(e)))
    }

    fn call(&mut self) -> R<Expr> {
        let e = self.primary()?;
        self.call_tail(e)
    }

    fn call_tail(&mut self, mut e: Expr) -> R<Expr> {
        let mut base: Option<Expr> = None;
        let mut ops: Vec<OptOp> = Vec::new();
        loop {
            if matches!(self.peek(), Tok::Tpl { head: true, .. }) {
                return Err(err("tagged templates unsupported"));
            }
            if self.at_p("?.") {
                if base.is_none() {
                    let (b, mut prefix) = split_chain(e);
                    e = Expr::Undef;
                    base = Some(b);
                    ops.append(&mut prefix);
                }
                self.i += 1;
                if self.eat_p("[") {
                    let k = self.expr()?;
                    self.exp_p("]")?;
                    ops.push(OptOp::Index(k, true));
                } else if self.at_p("(") {
                    ops.push(OptOp::Call(self.args()?, true));
                } else {
                    ops.push(OptOp::Member(self.prop_name()?, true));
                }
            } else if base.is_some() {
                if self.at_p("(") {
                    ops.push(OptOp::Call(self.args()?, false));
                } else if self.eat_p(".") {
                    ops.push(OptOp::Member(self.prop_name()?, false));
                } else if self.eat_p("[") {
                    let k = self.expr()?;
                    self.exp_p("]")?;
                    ops.push(OptOp::Index(k, false));
                } else {
                    break;
                }
            } else if self.at_p("(") {
                e = Expr::Call(Box::new(e), self.args()?);
            } else if self.eat_p(".") {
                e = Expr::Member(Box::new(e), self.prop_name()?);
            } else if self.eat_p("[") {
                let k = self.expr()?;
                self.exp_p("]")?;
                e = Expr::Index(Box::new(e), Box::new(k));
            } else {
                break;
            }
        }
        if let Some(b) = base {
            Ok(Expr::OptChain(Box::new(b), ops))
        } else {
            Ok(e)
        }
    }

    fn args(&mut self) -> R<Vec<Expr>> {
        self.exp_p("(")?;
        let mut v = Vec::new();
        if !self.at_p(")") {
            loop {
                if self.eat_p("...") {
                    v.push(Expr::Spread(Box::new(self.assign()?)));
                } else {
                    v.push(self.assign()?);
                }
                if !self.eat_p(",") {
                    break;
                }
            }
        }
        self.exp_p(")")?;
        Ok(v)
    }

    fn primary(&mut self) -> R<Expr> {
        let pos = self.pos();
        match self.bump() {
            Tok::Num(n) => Ok(Expr::Num(n)),
            Tok::Str(s) => Ok(Expr::Str(s)),
            Tok::Ident(s) => Ok(Expr::Ident(s)),
            Tok::Kw("true") => Ok(Expr::Bool(true)),
            Tok::Kw("false") => Ok(Expr::Bool(false)),
            Tok::Kw("null") => Ok(Expr::Null),
            Tok::Kw("undefined") => Ok(Expr::Undef),
            Tok::Regex { pat, flags } => {
                crate::regex::compile(&pat, &flags)
                    .map_err(|m| err(format!("invalid regex: {m}")))?;
                Ok(Expr::Regex { pat, flags })
            }
            Tok::Tpl { cooked, expr, .. } => {
                if !expr {
                    return Ok(Expr::Str(cooked));
                }
                let mut parts = Vec::new();
                let mut head = cooked;
                loop {
                    let e = self.expr()?;
                    match self.bump() {
                        Tok::Tpl {
                            cooked: c2,
                            expr: e2,
                            ..
                        } => {
                            parts.push((std::mem::take(&mut head), e));
                            if !e2 {
                                return Ok(Expr::Tpl(parts, c2));
                            }
                            head = c2;
                        }
                        t => return Err(err(format!("expected template continuation, got {t:?}"))),
                    }
                }
            }
            Tok::Kw("function") => {
                let name = if matches!(self.peek(), Tok::Ident(_)) {
                    Some(self.ident()?)
                } else {
                    None
                };
                Ok(Expr::Func(self.fn_tail(name, false)?))
            }
            Tok::Kw("async") => {
                // async function expression; `async` alone is not a primary
                if !self.eat_kw("function") {
                    return Err(err(format!(
                        "expected 'function' after 'async' at byte {pos}"
                    )));
                }
                let name = if matches!(self.peek(), Tok::Ident(_)) {
                    Some(self.ident()?)
                } else {
                    None
                };
                Ok(Expr::Func(self.fn_tail(name, true)?))
            }
            Tok::Kw("class") => {
                let name = if matches!(self.peek(), Tok::Ident(_)) {
                    Some(self.ident()?)
                } else {
                    None
                };
                self.parse_class(name)
            }
            Tok::Kw("super") => {
                if !self.super_ok {
                    return Err(err("unexpected super"));
                }
                if self.at_p("(") {
                    Ok(Expr::SuperCall(self.args()?))
                } else if self.eat_p(".") {
                    Ok(Expr::SuperProp(Box::new(Expr::Ident(self.prop_name()?))))
                } else if self.eat_p("[") {
                    let k = self.expr()?;
                    self.exp_p("]")?;
                    Ok(Expr::SuperProp(Box::new(k)))
                } else {
                    Err(err("unexpected super"))
                }
            }
            Tok::P("(") => {
                let e = self.expr()?;
                self.exp_p(")")?;
                Ok(e)
            }
            Tok::P("[") => {
                let mut v = Vec::new();
                if !self.eat_p("]") {
                    loop {
                        if self.eat_p("...") {
                            v.push(Expr::Spread(Box::new(self.assign()?)));
                        } else {
                            v.push(self.assign()?);
                        }
                        if self.eat_p("]") {
                            break;
                        }
                        self.exp_p(",")?;
                        if self.eat_p("]") {
                            break; // trailing comma
                        }
                    }
                }
                Ok(Expr::Arr(v))
            }
            Tok::P("{") => {
                let mut v: Vec<ObjEntry> = Vec::new();
                if !self.eat_p("}") {
                    loop {
                        if self.eat_p("...") {
                            v.push(ObjEntry::Spread(self.assign()?));
                            if self.eat_p("}") {
                                break;
                            }
                            self.exp_p(",")?;
                            if self.eat_p("}") {
                                break; // trailing comma
                            }
                            continue;
                        }
                        // Computed `[kexpr]: v` key.
                        if self.eat_p("[") {
                            let k = self.expr()?;
                            self.exp_p("]")?;
                            self.exp_p(":")?;
                            let val = self.assign()?;
                            v.push(ObjEntry::Computed(k, val));
                            if self.eat_p("}") {
                                break;
                            }
                            self.exp_p(",")?;
                            if self.eat_p("}") {
                                break; // trailing comma
                            }
                            continue;
                        }
                        let key = match self.bump() {
                            Tok::Ident(s) => s,
                            Tok::Kw(k) => k.to_string(),
                            Tok::Str(s) => s,
                            Tok::Num(n) => fmt_num(n),
                            t => {
                                return Err(err(format!(
                                    "expected object key, got {t:?} at byte {pos}"
                                )))
                            }
                        };
                        // `get x() {}` / `set x(v) {}` (not `get: v`, and not
                        // a method literally named `get`/`set`).
                        if (key == "get" || key == "set") && !self.at_p(":") && !self.at_p("(") {
                            let prop = self.acc_name()?;
                            self.exp_p("(")?;
                            let (params, rest) = self.param_list()?;
                            if rest.is_some() {
                                return Err(err("rest in accessor params"));
                            }
                            self.exp_p(")")?;
                            self.exp_p("{")?;
                            self.in_fn += 1;
                            let body = self.block_body();
                            self.in_fn -= 1;
                            let def = Rc::new(FnDef {
                                name: Some(prop.clone()),
                                params,
                                body: body?,
                                is_async: false,
                                is_arrow: false,
                                rest: None,
                                cls: None,
                            });
                            if key == "get" {
                                if !def.params.is_empty() {
                                    return Err(err("getter takes no params"));
                                }
                                v.push(ObjEntry::Accessor {
                                    key: prop,
                                    get: Some(def),
                                    set: None,
                                });
                            } else {
                                if def.params.len() != 1 || def.params[0].1.is_some() {
                                    return Err(err("setter takes one plain param"));
                                }
                                v.push(ObjEntry::Accessor {
                                    key: prop,
                                    get: None,
                                    set: Some(def),
                                });
                            }
                            if self.eat_p("}") {
                                break;
                            }
                            self.exp_p(",")?;
                            if self.eat_p("}") {
                                break; // trailing comma
                            }
                            continue;
                        }
                        // `m() {}` method shorthand.
                        if self.at_p("(") {
                            self.exp_p("(")?;
                            let (params, rest) = self.param_list()?;
                            self.exp_p(")")?;
                            self.exp_p("{")?;
                            self.in_fn += 1;
                            let body = self.block_body();
                            self.in_fn -= 1;
                            let def = Rc::new(FnDef {
                                name: Some(key.clone()),
                                params,
                                body: body?,
                                is_async: false,
                                is_arrow: false,
                                rest,
                                cls: None,
                            });
                            v.push(ObjEntry::Pair(key, Expr::Func(def)));
                            if self.eat_p("}") {
                                break;
                            }
                            self.exp_p(",")?;
                            if self.eat_p("}") {
                                break; // trailing comma
                            }
                            continue;
                        }
                        // `{x}` shorthand = `{x: x}`
                        let val = if self.eat_p(":") {
                            self.assign()?
                        } else {
                            Expr::Ident(key.clone())
                        };
                        v.push(ObjEntry::Pair(key, val));
                        if self.eat_p("}") {
                            break;
                        }
                        self.exp_p(",")?;
                        if self.eat_p("}") {
                            break; // trailing comma
                        }
                    }
                }
                Ok(Expr::ObjLit(v))
            }
            t => Err(err(format!("unexpected {t:?} at byte {pos}"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expr(src: &str) -> Expr {
        match parse_program(src).unwrap().remove(0) {
            Stmt::Expr(e) => e,
            s => panic!("{s:?}"),
        }
    }

    #[test]
    fn precedence() {
        // 1+2*3 -> +(1, *(2,3))
        match expr("1+2*3") {
            Expr::Bin("+", _, r) => assert!(matches!(*r, Expr::Bin("*", _, _))),
            e => panic!("{e:?}"),
        }
        // a||b&&c -> ||(a, &&(b,c))
        match expr("a||b&&c") {
            Expr::Bin("||", _, r) => assert!(matches!(*r, Expr::Bin("&&", _, _))),
            e => panic!("{e:?}"),
        }
        // a=b=5 right-assoc
        match expr("a=b=5") {
            Expr::Assign("=", _, r) => assert!(matches!(*r, Expr::Assign("=", _, _))),
            e => panic!("{e:?}"),
        }
        // !x===false -> ===(!x, false)
        match expr("!x===false") {
            Expr::Bin("===", l, _) => assert!(matches!(*l, Expr::Unary("!", _))),
            e => panic!("{e:?}"),
        }
        // ternary right-assoc
        assert!(matches!(expr("a?b:c?d:e"), Expr::Ternary(..)));
        // a.b(1).c -> Member(Call(Member(a,b),[1]),c)
        match expr("a.b(1).c") {
            Expr::Member(l, _) => assert!(matches!(*l, Expr::Call(..))),
            e => panic!("{e:?}"),
        }
        // compound assign keeps member target
        assert!(matches!(expr("o.x+=1"), Expr::Assign("+=", _, _)));
    }

    #[test]
    fn asi() {
        assert_eq!(parse_program("var a=1\na+1").unwrap().len(), 2);
        assert!(parse_program("var a=1 var b=2").is_err());
        // x\n++y is two statements (real ASI)
        assert_eq!(parse_program("x\n++y").unwrap().len(), 2);
        assert_eq!(parse_program("var a=[1,2,];a.length").unwrap().len(), 2);
    }

    #[test]
    fn decls() {
        match parse_program("function f(a,b){return a}")
            .unwrap()
            .remove(0)
        {
            Stmt::FnDecl(d) => assert_eq!(d.params.len(), 2),
            s => panic!("{s:?}"),
        }
        match parse_program("var a=1,b=2").unwrap().remove(0) {
            Stmt::VarDecl(d) => assert_eq!(d.len(), 2),
            s => panic!("{s:?}"),
        }
        assert!(matches!(
            parse_program("for(var i=0;i<3;i++){x}").unwrap().remove(0),
            Stmt::For(..)
        ));
        match expr("(function(a){return a})") {
            Expr::Func(d) => assert!(d.name.is_none()),
            e => panic!("{e:?}"),
        }
        // {x} shorthand and trailing comma
        assert!(matches!(expr("({x,y:1,})"), Expr::ObjLit(_)));
    }

    #[test]
    fn errors() {
        assert!(parse_program("return 1").is_err());
        assert!(parse_program("break").is_err());
        assert!(parse_program("var =3").is_err());
        assert!(parse_program("a.b.").is_err());
        assert!(parse_program("(((((1").is_err());
        assert!(parse_program("1++").is_err());
    }

    #[test]
    fn try_throw() {
        assert!(matches!(
            parse_program("try{a()}catch(e){b()}finally{c()}")
                .unwrap()
                .remove(0),
            Stmt::Try { .. }
        ));
        // each clause optional, but at least one is required
        match parse_program("try{}catch(e){}").unwrap().remove(0) {
            Stmt::Try {
                catch: Some((Some(p), _)),
                finally: None,
                ..
            } => assert_eq!(p, "e"),
            s => panic!("{s:?}"),
        }
        match parse_program("try{}finally{}").unwrap().remove(0) {
            Stmt::Try {
                catch: None,
                finally: Some(_),
                ..
            } => {}
            s => panic!("{s:?}"),
        }
        // catch without a binding param
        match parse_program("try{}catch{}").unwrap().remove(0) {
            Stmt::Try {
                catch: Some((None, _)),
                ..
            } => {}
            s => panic!("{s:?}"),
        }
        assert!(parse_program("try{}").is_err());
        assert!(parse_program("try{}catch({a}){}").is_err()); // no destructuring
        assert!(matches!(
            parse_program("throw x").unwrap().remove(0),
            Stmt::Throw(Expr::Ident(_))
        ));
        assert!(parse_program("throw").is_err());
        assert!(parse_program("throw\n1").is_err()); // real ASI rule
                                                     // p.catch(...) member syntax unaffected by the new keyword
        assert_eq!(parse_program("p.catch(f)").unwrap().len(), 1);
    }
}
