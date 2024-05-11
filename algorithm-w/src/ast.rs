use std::rc::Rc;

use crate::symbol::Symbol;

#[derive(Debug)]
pub enum Expr {
    Bool(bool),
    Int(i64),
    Lambda(Symbol, Rc<Expr>),
    Variable(Symbol),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    //Let(Symbol, Box<Expr>, Box<Expr>),
    Apply(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Eq,
}
