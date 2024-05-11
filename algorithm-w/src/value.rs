use std::{fmt::Display, rc::Rc};

use crate::{ast::Expr, symbol::Symbol};

#[derive(Debug, Clone)]
pub enum Value {
    Bool(bool),
    Integer(i64),
    Closure(Rc<Closure>),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Integer(n) => write!(f, "{n}"),
            Value::Closure(c) => write!(f, "<closure {:p}>", c),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Integer(n1), Value::Integer(n2)) => n1 == n2,
            (Value::Closure(c1), Value::Closure(c2)) => std::ptr::eq(c1, c2),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct Closure {
    pub frame: Rc<Frame>,
    pub param: Symbol,
    pub body: Rc<Expr>,
}

#[derive(Debug)]
pub struct Frame {
    pub parent: Option<Rc<Frame>>,
    pub v_name: Symbol,
    pub v_value: Value,
}

impl Frame {
    pub fn lookup(&self, name: &Symbol) -> Option<Value> {
        // TODO: リニアサーチしているので効率が悪い
        if self.v_name == name {
            return Some(self.v_value.clone());
        }
        if let Some(ref parent) = self.parent {
            return parent.lookup(name);
        }
        None
    }
}
