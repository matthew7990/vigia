//! AST. Rc appears only on FnDef so Obj::Func can share an immutable body.

use std::rc::Rc;

#[derive(Debug)]
pub enum Expr {
    Num(f64),
    Str(String),
    Bool(bool),
    Null,
    Undef,
    Ident(String),
    Arr(Vec<Expr>),
    ObjLit(Vec<(String, Expr)>),
    /// op: "!" "~" "+" "-" "typeof" "++" "--" (prefix)
    Unary(&'static str, Box<Expr>),
    /// op: "++" "--" (postfix)
    Postfix(&'static str, Box<Expr>),
    Bin(&'static str, Box<Expr>, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// op: "=" or a compound op ("+=", ...). lhs: Ident | Member | Index.
    Assign(&'static str, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    /// Optional chain: base + steps. Each step carries its own `?.` flag.
    /// `a?.b.c(d)` is Chain(a, [Member(b,true), Member(c,false), Call(d,false)]).
    OptChain(Box<Expr>, Vec<OptOp>),
    Func(Rc<FnDef>),
    New(Box<Expr>, Vec<Expr>),
}

/// One step of an optional chain. The bool marks a `?.` step.
#[derive(Debug)]
pub enum OptOp {
    Member(String, bool),
    Index(Expr, bool),
    Call(Vec<Expr>, bool),
}

#[derive(Debug)]
pub struct FnDef {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
    /// `async function`: call wraps the result in a Promise; enables `await`.
    pub is_async: bool,
    /// Arrow: lexical `this`, no `new`, no own `prototype` (prototype kept
    /// as harmless stub for now).
    pub is_arrow: bool,
}

#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    /// var/let/const are the same for now; Vec covers `var a=1, b=2`.
    VarDecl(Vec<(String, Option<Expr>)>),
    FnDecl(Rc<FnDef>),
    Return(Option<Expr>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    /// for(init; test; update) body
    For(Option<Box<Stmt>>, Option<Expr>, Option<Expr>, Box<Stmt>),
    /// Strict `for-of` over arrays and strings only:
    /// `for (var|let|const x of iter) body` (decl) or `for (x of iter) body`.
    ForOf {
        name: String,
        is_decl: bool,
        iter: Expr,
        body: Box<Stmt>,
    },
    Block(Vec<Stmt>),
    Break,
    Continue,
    /// `throw <expr>`
    Throw(Expr),
    /// try { body } [catch [(param)] { block }] [finally { block }] -
    /// the parser requires at least one of catch/finally.
    Try {
        body: Vec<Stmt>,
        catch: Option<(Option<String>, Vec<Stmt>)>,
        finally: Option<Vec<Stmt>>,
    },
}
