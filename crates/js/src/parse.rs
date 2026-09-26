//! Recursive-descent parser. Standard JS precedence, low to high:
//! assign < ternary < || < && < equality < relational(+in) < additive <
//! multiplicative < unary < postfix < call/member < primary.
//!
//! Statement end: `;` optional before `}`, EOF, or a token preceded by a
//! newline (ASI-lite). `return <newline>` means `return;`, like real ASI.

use std::rc::Rc;

use crate::ast::{Expr, FnDef, Stmt};
use crate::eval::fmt_num;
use crate::lex::{lex, Tok, Token};
use crate::{err, JsError};

/// ~15 recursion frames per nested level; 400 stays well under the stack.
const MAX_DEPTH: u32 = 400;

pub fn parse_program(src: &str) -> Result<Vec<Stmt>, JsError> {
    let t = lex(src)?;
    let mut p = P { t, i: 0, depth: 0, in_fn: 0, in_loop: 0 };
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
}

type R<T> = Result<T, JsError>;

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
        err(format!("{what}, got {:?} at byte {}", self.peek(), self.pos()))
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
                Ok(Stmt::FnDecl(self.fn_tail(Some(n))?))
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
            Tok::Kw("for") => self.for_stmt(),
            Tok::Kw("break") | Tok::Kw("continue") => {
                if self.in_loop == 0 {
                    return Err(err("break/continue outside loop"));
                }
                let is_break = matches!(self.peek(), Tok::Kw("break"));
                self.i += 1;
                self.semi()?;
                Ok(if is_break { Stmt::Break } else { Stmt::Continue })
            }
            _ => {
                let e = self.expr()?;
                self.semi()?;
                Ok(Stmt::Expr(e))
            }
        }
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

    fn var_decls(&mut self) -> R<Vec<(String, Option<Expr>)>> {
        let mut v = Vec::new();
        loop {
            let name = self.ident()?;
            let init = if self.eat_p("=") { Some(self.expr()?) } else { None };
            v.push((name, init));
            if !self.eat_p(",") {
                break;
            }
        }
        Ok(v)
    }

    /// `(params) { body }` shared by fn declarations and fn expressions.
    fn fn_tail(&mut self, name: Option<String>) -> R<Rc<FnDef>> {
        self.exp_p("(")?;
        let mut params = Vec::new();
        if !self.at_p(")") {
            loop {
                params.push(self.ident()?);
                if !self.eat_p(",") {
                    break;
                }
            }
        }
        self.exp_p(")")?;
        self.exp_p("{")?;
        self.in_fn += 1;
        let body = self.block_body();
        self.in_fn -= 1;
        Ok(Rc::new(FnDef { name, params, body: body? }))
    }

    fn for_stmt(&mut self) -> R<Stmt> {
        self.i += 1; // 'for'
        self.exp_p("(")?;
        let init = if self.eat_p(";") {
            None
        } else if matches!(self.peek(), Tok::Kw("var") | Tok::Kw("let") | Tok::Kw("const")) {
            self.i += 1;
            let d = self.var_decls()?;
            self.exp_p(";")?;
            Some(Box::new(Stmt::VarDecl(d)))
        } else {
            let e = self.expr()?;
            self.exp_p(";")?;
            Some(Box::new(Stmt::Expr(e)))
        };
        let test = if self.at_p(";") { None } else { Some(self.expr()?) };
        self.exp_p(";")?;
        let upd = if self.at_p(")") { None } else { Some(self.expr()?) };
        self.exp_p(")")?;
        self.in_loop += 1;
        let b = self.stmt();
        self.in_loop -= 1;
        Ok(Stmt::For(init, test, upd, Box::new(b?)))
    }

    // ---- expressions -------------------------------------------------

    fn expr(&mut self) -> R<Expr> {
        self.assign()
    }

    fn assign(&mut self) -> R<Expr> {
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
        let f = self.ternary()?;
        Ok(Expr::Ternary(Box::new(c), Box::new(t), Box::new(f)))
    }

    fn lor(&mut self) -> R<Expr> {
        self.binop(Self::land, &["||"])
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
        self.binop(Self::shift, &["<", "<=", ">", ">=", "in"])
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
            "typeof" => {
                self.i += 1;
                Ok(Expr::Unary("typeof", Box::new(self.unary()?)))
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
        let args = if self.at_p("(") { self.args()? } else { Vec::new() };
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
        loop {
            if self.at_p("(") {
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
        Ok(e)
    }

    fn args(&mut self) -> R<Vec<Expr>> {
        self.exp_p("(")?;
        let mut v = Vec::new();
        if !self.at_p(")") {
            loop {
                v.push(self.expr()?);
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
            Tok::Kw("function") => {
                let name = if matches!(self.peek(), Tok::Ident(_)) {
                    Some(self.ident()?)
                } else {
                    None
                };
                Ok(Expr::Func(self.fn_tail(name)?))
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
                        v.push(self.expr()?);
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
                let mut v: Vec<(String, Expr)> = Vec::new();
                if !self.eat_p("}") {
                    loop {
                        let key = match self.bump() {
                            Tok::Ident(s) => s,
                            Tok::Kw(k) => k.to_string(),
                            Tok::Str(s) => s,
                            Tok::Num(n) => fmt_num(n),
                            t => return Err(err(format!("expected object key, got {t:?} at byte {pos}"))),
                        };
                        // `{x}` shorthand = `{x: x}`
                        let val = if self.eat_p(":") {
                            self.expr()?
                        } else {
                            Expr::Ident(key.clone())
                        };
                        v.push((key, val));
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
        match parse_program("function f(a,b){return a}").unwrap().remove(0) {
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
}
