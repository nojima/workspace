use std::{
    cell::RefCell,
    fmt::Display,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{ast::Expr, symbol::Symbol};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Simple(Symbol),
    Function(Box<Type>, Box<Type>),
    Variable(Rc<RefCell<Variable>>),
}

impl Type {
    pub fn fresh() -> Type {
        Type::Variable(Rc::new(RefCell::new(Variable::fresh())))
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Simple(name) => name.fmt(f),
            Type::Function(a, b) => write!(f, "({a} -> {b})"),
            Type::Variable(v) => match *v.borrow() {
                Variable::Unbound(id) => write!(f, "τ{id}"),
                Variable::Bound(ref t) => t.fmt(f),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Variable {
    Unbound(usize),
    Bound(Type),
}

impl Variable {
    pub fn fresh() -> Variable {
        static NEXT_VARIABLE_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_VARIABLE_ID.fetch_add(1, Ordering::SeqCst);
        Variable::Unbound(id)
    }
}

pub type Environment = im::HashMap<Symbol, Type>;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TypeError {
    #[error("failed to unify: {0} and {1}")]
    FailedToUnify(Type, Type),

    #[error("undefined variable: {0}")]
    UndefinedVariable(Symbol),

    #[error("unimplemented")]
    Unimplemented,
}

pub fn unify(t1: &Type, t2: &Type) -> Result<(), TypeError> {
    match (t1, t2) {
        (t1, t2) if t1 == t2 => {
            return Ok(());
        }

        (Type::Function(t1, t2), Type::Function(t3, t4)) => {
            unify(t1, t3)?;
            unify(t2, t4)?;
            return Ok(());
        }

        // 少なくとも片方が型変数であるとき
        (Type::Variable(v), t) | (t, Type::Variable(v)) => {
            let mut v = v.borrow_mut();
            match *v {
                Variable::Unbound(_) => {
                    // TODO: occur check
                    *v = Variable::Bound(t.clone());
                }
                Variable::Bound(ref tt) => {
                    unify(t, tt)?;
                }
            };
            return Ok(());
        }

        _ => return Err(TypeError::FailedToUnify(t1.clone(), t2.clone())),
    }
}

pub fn type_of(env: &Environment, expr: &Expr) -> Result<Type, TypeError> {
    match expr {
        Expr::Variable(name) => {
            let Some(t) = env.get(name) else {
                return Err(TypeError::UndefinedVariable(*name));
            };
            Ok(t.clone())
        }
        Expr::Lambda(param_name, body_expr) => {
            let param_type = Type::fresh();
            let body_env = env.update(*param_name, param_type.clone());
            let body_type = type_of(&body_env, body_expr)?;
            let t = Type::Function(Box::new(param_type), Box::new(body_type));
            Ok(t)
        }
        Expr::Apply(expr1, expr2) => {
            let fun_type1 = type_of(env, expr1)?;
            let arg_type = type_of(env, expr2)?;
            let ret_type = Type::fresh();
            let fun_type2 = Type::Function(Box::new(arg_type), Box::new(ret_type.clone()));
            unify(&fun_type1, &fun_type2)?;
            Ok(ret_type)
        }
        _ => Err(TypeError::Unimplemented),
    }
}
