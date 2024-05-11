use crate::symbol::Symbol;

#[derive(Debug)]
pub enum Expr {
    Bool(bool),
    Integer(i64),
    Lambda(Symbol, Box<Expr>),

    Variable(Symbol),

    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Symbol, Box<Expr>, Box<Expr>),

    Apply(Box<Expr>, Box<Expr>),
}
