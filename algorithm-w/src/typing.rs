use std::{
    cell::RefCell,
    collections::{hash_map::Entry, HashMap},
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
    Quantified(usize),
}

pub fn int() -> Type {
    Type::Simple("Int".into())
}

pub fn bool() -> Type {
    Type::Simple("Bool".into())
}

impl Type {
    pub fn fresh() -> Type {
        Type::Variable(Rc::new(RefCell::new(Variable::fresh())))
    }

    // この型に含まれるすべての Variable を Quantified に変換した型を返す
    // (unsound!)
    pub fn generalize(&self) -> Type {
        match self {
            Type::Variable(var) => {
                let var = var.borrow();
                match *var {
                    Variable::Unbound(id) => Type::Quantified(id),
                    Variable::Bound(ref t) => t.generalize(),
                }
            }
            Type::Function(t1, t2) => {
                Type::Function(Box::new(t1.generalize()), Box::new(t2.generalize()))
            }
            _ => self.clone(),
        }
    }

    // この型に含まれる Quantified をすべて fresh な Variable に置き換えた型を返す
    pub fn instanciate(&self) -> Type {
        let mut memo = HashMap::new();
        self.instanciate_(&mut memo)
    }

    fn instanciate_(&self, memo: &mut HashMap<usize, Rc<RefCell<Variable>>>) -> Type {
        match self {
            Type::Quantified(id) => match memo.entry(*id) {
                Entry::Occupied(entry) => {
                    let var_ref = entry.get();
                    Type::Variable(Rc::clone(var_ref))
                }
                Entry::Vacant(entry) => {
                    let var = Variable::fresh();
                    let var_ref = Rc::new(RefCell::new(var));
                    entry.insert(Rc::clone(&var_ref));
                    Type::Variable(var_ref)
                }
            },
            Type::Function(t1, t2) => Type::Function(
                Box::new(t1.instanciate_(memo)),
                Box::new(t2.instanciate_(memo)),
            ),
            _ => self.clone(),
        }
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
            Type::Quantified(id) => write!(f, "α{id}"),
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

    #[error("occurs check failure")]
    OccursCheckFailure,

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
                    occurs_check(&v, t)?;
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

// t の中に var が出現していたらエラーを返す
pub fn occurs_check(var: &Variable, t: &Type) -> Result<(), TypeError> {
    match t {
        Type::Variable(var2) => {
            let var2 = var2.borrow();
            if std::ptr::eq(var, &*var2) {
                return Err(TypeError::OccursCheckFailure);
            }
            if let Variable::Bound(ref t2) = *var2 {
                occurs_check(var, t2)
            } else {
                Ok(())
            }
        }
        Type::Function(t1, t2) => {
            occurs_check(var, t1)?;
            occurs_check(var, t2)?;
            Ok(())
        }
        _ => Ok(()),
    }
}

pub fn type_of(env: &Environment, expr: &Expr) -> Result<Type, TypeError> {
    match expr {
        Expr::Variable(name) => {
            let Some(t) = env.get(name) else {
                return Err(TypeError::UndefinedVariable(*name));
            };
            Ok(t.instanciate())
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
        Expr::Let(name, expr1, expr2) => {
            let expr1_type = type_of(env, expr1)?;
            let expr2_env = env.update(*name, expr1_type.generalize());
            type_of(&expr2_env, expr2)
        }
        Expr::Int(_) => Ok(int()),
        Expr::Bool(_) => Ok(bool()),
        _ => Err(TypeError::Unimplemented),
    }
}
