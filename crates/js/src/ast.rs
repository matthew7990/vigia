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
    Func(Rc<FnDef>),
    New(Box<Expr>, Vec<Expr>),
}

#[derive(Debug)]
pub struct FnDef {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
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
    Block(Vec<Stmt>),
    Break,
    Continue,
}
