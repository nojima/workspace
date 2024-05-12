use std::rc::Rc;

use crate::{
    ast::{BinOp, Expr},
    symbol::Symbol,
    value::{Closure, Frame, Value},
};

#[derive(Debug, Clone, thiserror::Error)]
pub enum EvalError {
    #[error("undefined variable: {0}")]
    UndefinedVariable(Symbol),

    #[error("non-closure value cannot be applied")]
    NonClosureObjectCannoBeApplied,

    #[error("non-boolean value cannot be used in condition")]
    NonBooleanValueCannotBeUsedInCondition,

    #[error("unexpected type of argument: expected={0}, actual={1}")]
    UnexpectedTypeOfArgument(String, String),
}

type Result<T> = std::result::Result<T, EvalError>;

pub fn eval(expr: &Expr, frame: Rc<Frame>) -> Result<Value> {
    match expr {
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Int(n) => Ok(Value::Integer(*n)),
        Expr::Lambda(param, body) => {
            let closure = Closure {
                frame: frame,
                param: param.clone(),
                body: Rc::clone(&body),
            };
            Ok(Value::Closure(Rc::new(closure)))
        }
        Expr::Variable(name) => match frame.lookup(name) {
            Some(value) => Ok(value),
            None => Err(EvalError::UndefinedVariable(name.clone())),
        },
        Expr::Apply(expr1, expr2) => {
            let f = eval(expr1, Rc::clone(&frame))?;
            let arg = eval(expr2, frame)?;
            let Value::Closure(closure) = f else {
                return Err(EvalError::NonClosureObjectCannoBeApplied);
            };
            let new_frame = Rc::new(Frame {
                parent: Some(Rc::clone(&closure.frame)),
                v_name: closure.param.clone(),
                v_value: arg,
            });
            eval(&closure.body, new_frame)
        }
        Expr::If(cond_expr, then_expr, else_expr) => {
            let cond_value = eval(&cond_expr, Rc::clone(&frame))?;
            let Value::Bool(cond_value) = cond_value else {
                return Err(EvalError::NonBooleanValueCannotBeUsedInCondition);
            };
            if cond_value {
                eval(&then_expr, frame)
            } else {
                eval(&else_expr, frame)
            }
        }
        Expr::Let(name, bound_expr, body_expr) => {
            let bound_value = eval(&bound_expr, Rc::clone(&frame))?;
            let new_frame = Rc::new(Frame {
                parent: Some(frame),
                v_name: name.clone(),
                v_value: bound_value,
            });
            eval(&body_expr, new_frame)
        }
        Expr::BinOp(op, lhs_expr, rhs_expr) => {
            let lhs_value = eval(lhs_expr, Rc::clone(&frame))?;
            let rhs_value = eval(rhs_expr, frame)?;
            match op {
                BinOp::Add => {
                    let Value::Integer(x) = lhs_value else {
                        return Err(EvalError::UnexpectedTypeOfArgument(
                            "Integer".into(),
                            lhs_value.to_string(),
                        ));
                    };
                    let Value::Integer(y) = rhs_value else {
                        return Err(EvalError::UnexpectedTypeOfArgument(
                            "Integer".into(),
                            rhs_value.to_string(),
                        ));
                    };
                    Ok(Value::Integer(x + y))
                }
                BinOp::Eq => Ok(Value::Bool(lhs_value == rhs_value)),
            }
        }
    }
}
