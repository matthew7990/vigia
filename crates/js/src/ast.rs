//! AST. Rc appears only on FnDef so Obj::Func can share an immutable body.

use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Expr {
    Num(f64),
    Str(String),
    Bool(bool),
    Null,
    Undef,
    Ident(String),
    Arr(Vec<Expr>),
    ObjLit(Vec<ObjEntry>),
    /// `...x` in calls, arrays and object literals (expanded at eval).
    Spread(Box<Expr>),
    /// op: "!" "~" "+" "-" "typeof" "++" "--" (prefix)
    Unary(&'static str, Box<Expr>),
    /// op: "++" "--" (postfix)
    Postfix(&'static str, Box<Expr>),
    Bin(&'static str, Box<Expr>, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// op: "=" or a compound op ("+=", ...). lhs: Ident | Member | Index.
    Assign(&'static str, Box<Expr>, Box<Expr>),
    /// `[a, [b]] = e` / `{x} = e`: pattern assignment (plain `=` only).
    Destructure(Pat, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    /// Regex literal source + flags (validated at parse time).
    Regex {
        pat: String,
        flags: String,
    },
    /// Template: (cooked, expr) pairs plus the cooked tail.
    Tpl(Vec<(String, Expr)>, String),
    /// `class Name extends Sup { ... }` (name None for expressions).
    Class {
        name: Option<String>,
        parent: Option<Box<Expr>>,
        members: Vec<ClassMember>,
    },
    /// `super(args)` in a derived constructor.
    SuperCall(Vec<Expr>),
    /// `super.name` / `super[key]`: method lookup on the parent prototype.
    SuperProp(Box<Expr>),
    /// Optional chain: base + steps. Each step carries its own `?.` flag.
    /// `a?.b.c(d)` is Chain(a, [Member(b,true), Member(c,false), Call(d,false)]).
    OptChain(Box<Expr>, Vec<OptOp>),
    Func(Rc<FnDef>),
    New(Box<Expr>, Vec<Expr>),
}

/// One object-literal entry: `k: v`, `k` shorthand, `...x` spread,
/// `m() {}` method, `get x()` / `set x(v)` accessor side, or a computed
/// `[kexpr]: v` key.
#[derive(Debug, Clone)]
pub enum ObjEntry {
    Pair(String, Expr),
    Spread(Expr),
    Computed(Expr, Expr),
    Accessor {
        key: String,
        get: Option<std::rc::Rc<FnDef>>,
        set: Option<std::rc::Rc<FnDef>>,
    },
}

/// One `var` declarator: `name = init` or a pattern (`[a,b] = e`).
#[derive(Debug, Clone)]
pub enum VarDecl {
    Plain(String, Option<Expr>),
    Pat(Pat, Expr),
}

/// `var` (function-scoped, hoisted as undefined) vs `let`/`const`
/// (block-scoped; reads before declaration stay "not defined").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    Var,
    Let,
    Const,
}

/// Destructuring pattern: identifier leaves (plus nested patterns),
/// element/field defaults, holes (`[,,]`) and a trailing rest name.
#[derive(Debug, Clone)]
pub enum Pat {
    Ident(String),
    Arr(Vec<Option<(Pat, Option<Expr>)>>, Option<String>),
    Obj(Vec<ObjField>, Option<String>),
}

#[derive(Debug, Clone)]
pub struct ObjField {
    pub key: String,
    pub pat: Pat,
    pub default: Option<Expr>,
}

/// A class member after parsing: constructor, method, accessor side,
/// or field (instance or static).
#[derive(Debug, Clone)]
pub struct ClassMember {
    pub statik: bool,
    pub kind: MemberKind,
}

#[derive(Debug, Clone)]
pub enum MemberKind {
    Ctor {
        params: Vec<(Pat, Option<Expr>)>,
        rest: Option<String>,
        body: Vec<Stmt>,
    },
    Method(String, Rc<FnDef>),
    Get(String, Rc<FnDef>),
    Set(String, Rc<FnDef>),
    Field(String, Option<Expr>),
    /// Computed `[kexpr]` members; the key stringifies at eval (symbols
    /// included, same rule as computed object keys - the iteration
    /// protocols themselves stay unimplemented).
    ComputedMethod {
        key: Expr,
        def: Rc<FnDef>,
    },
    ComputedGet {
        key: Expr,
        def: Rc<FnDef>,
    },
    ComputedSet {
        key: Expr,
        def: Rc<FnDef>,
    },
    ComputedField {
        key: Expr,
        init: Option<Expr>,
    },
}

/// Constructor closure data: instance field initializers. `derived` is
/// implicit (presence of `__super` in the ctor's pairs at eval).
#[derive(Debug, Clone)]
pub struct ClassCtor {
    pub fields: Vec<(String, Option<Expr>)>,
}

/// One step of an optional chain. The bool marks a `?.` step.
#[derive(Debug, Clone)]
pub enum OptOp {
    Member(String, bool),
    Index(Expr, bool),
    Call(Vec<Expr>, bool),
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub name: Option<String>,
    pub params: Vec<(Pat, Option<Expr>)>,
    pub body: Vec<Stmt>,
    /// `async function`: call wraps the result in a Promise; enables `await`.
    pub is_async: bool,
    /// Arrow: lexical `this`, no `new`, no own `prototype` (prototype kept
    /// as harmless stub for now).
    pub is_arrow: bool,
    /// Trailing `...args`: collects surplus call args into an array.
    pub rest: Option<String>,
    /// Some for class constructors: instance field initializers, and the
    /// marker that direct calls must reject ("invoke with new").
    pub cls: Option<ClassCtor>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),
    /// Vec covers `var a=1, b=2`. `var` binds function scope (hoisted);
    /// `let`/`const` bind the current block env.
    VarDecl(VarKind, Vec<VarDecl>),
    FnDecl(Rc<FnDef>),
    Return(Option<Expr>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    /// do body while (test): runs at least once.
    DoWhile(Box<Stmt>, Expr),
    /// for(init; test; update) body
    For(Option<Box<Stmt>>, Option<Expr>, Option<Expr>, Box<Stmt>),
    /// Strict `for-of` over arrays and strings only:
    /// `for (var|let|const x of iter) body` (decl) or `for (x of iter) body`.
    /// Targets take patterns: `for (var {k} of xs)`. `var` targets bind
    /// in function scope (visible after the loop); `let`/`const` in the
    /// loop env; bare targets assign.
    ForOf {
        pat: Pat,
        decl: Option<VarKind>,
        iter: Expr,
        body: Box<Stmt>,
    },
    /// Strict `for-in` over own enumerable keys (objects, array/string
    /// indices). Anything else iterates zero times.
    ForIn {
        pat: Pat,
        decl: Option<VarKind>,
        obj: Expr,
        body: Box<Stmt>,
    },
    /// `switch (d) { case e: ...; default: ... }`: strict match, fallthrough.
    /// cases holds (test, body); test None is `default` (at most one).
    Switch {
        disc: Expr,
        cases: Vec<(Option<Expr>, Vec<Stmt>)>,
    },
    Block(Vec<Stmt>),
    Break(Option<String>),
    Continue(Option<String>),
    /// `throw <expr>`
    Throw(Expr),
    /// `name: stmt` - break/continue target (validated at runtime).
    Label(String, Box<Stmt>),
    /// `class Name extends Sup { ... }`: evaluates the class value, then
    /// binds the name (never hoisted - using it earlier is "not defined").
    ClassDecl(String, Expr),
    /// try { body } [catch [(param)] { block }] [finally { block }] -
    /// the parser requires at least one of catch/finally.
    Try {
        body: Vec<Stmt>,
        catch: Option<(Option<String>, Vec<Stmt>)>,
        finally: Option<Vec<Stmt>>,
    },
}
