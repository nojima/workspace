use crate::{ast::Expr, types::{Env, Equal, Substitutable, Substitution, Type}};


#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum UnificationError {
    #[error("failed to unify: lhs={0}, rhs={1}")]
    FailedToUnify(String, String),
}

pub fn unify(mut equals: Vec<Equal>) -> Result<Substitution, UnificationError> {
    let mut subst = Substitution::new();
    while let Some(eq) = equals.pop() {
        use Type::*;
        match eq {
            // 冗長な等式の除去
            Equal(t1, t2) if t1 == t2 => {}
            // (t1 → t2) == (t3 → t4) ==> (t1 == t3) && (t2 == t4)
            Equal(Func(t1, t2), Func(t3, t4)) => {
                equals.push(Equal(*t1, *t3));
                equals.push(Equal(*t2, *t4));
            }
            // 代入
            Equal(Variable(id), t) | Equal(t, Variable(id)) if !t.occur(id) => {
                subst.add(id, t);
                equals = equals.substitute(&subst);
            }
            // どれにも当てはまらない場合は失敗
            Equal(t1, t2) => {
                return Err(UnificationError::FailedToUnify(
                    t1.to_string(),
                    t2.to_string(),
                ));
            }
        }
    }
    Ok(subst)
}

fn func(t1: Type, t2: Type) -> Type {
    Type::Func(Box::new(t1), Box::new(t2))
}

pub fn primary_type(expr: &Expr) -> Result<(Env, Type), UnificationError> {
    match expr {
        Expr::Bool(_) => Ok((Env::empty(), Type::Bool)),
        Expr::Int(_) => Ok((Env::empty(), Type::Int)),
        Expr::Lambda(param, body) => {
            let (body_env, body_type) = primary_type(&body)?;
            if body_env.contains(param) {
                let t = func(body_env[param].clone(), body_type);
                Ok((body_env.without(param), t))
            } else {
                Ok((body_env, func(Type::fresh(), body_type)))
            }
        }
        Expr::Variable(name) => {
            let t = Type::fresh();
            Ok((Env::unit(name.clone(), t.clone()), t))
        }
        Expr::Apply(expr1, expr2) => {
            let (env1, type1) = primary_type(expr1)?;
            let (env2, type2) = primary_type(expr2)?;
            let new_t = Type::fresh();
            let mut equals = vec![Equal(type1, func(type2, new_t.clone()))];
            for (name, t1) in env1.iter() {
                if env2.contains(name) {
                    let t2 = env2[name].clone();
                    equals.push(Equal(t1.clone(), t2));
                }
            }
            let subst = unify(equals)?;
            let env1 = env1.substitute(&subst);
            let env2 = env2.substitute(&subst);
            Ok((env1.union(&env2), new_t.substitute(&subst)))
        }
        _ => unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::types::{Equal, Type};

    use super::unify;

    fn func(t1: Type, t2: Type) -> Type {
        Type::Func(Box::new(t1), Box::new(t2))
    }

    #[test]
    fn test() -> anyhow::Result<()> {
        use Type::*;
        assert_eq!(
            unify(vec![Equal(Variable(0), Int)])?,
            [(0, Int)].into(),
        );
        assert_eq!(
            unify(vec![Equal(Bool, Variable(0))])?,
            [(0, Bool)].into(),
        );
        assert_eq!(
            unify(vec![Equal(func(Int, Bool), func(Variable(0), Variable(1)))])?,
            [(0, Int), (1, Bool)].into(),
        );
        assert_eq!(
            unify(vec![Equal(func(Variable(0), Int), func(Variable(1), Variable(0)))])?,
            [(0, Int), (1, Int)].into(),
        );
        assert_eq!(
            unify(vec![
                Equal(func(Variable(0), Variable(0)), func(Variable(1), Variable(2))),
                Equal(Variable(2), Bool),
            ])?,
            [(0, Bool), (1, Bool), (2, Bool)].into(),
        );
        Ok(())
    }
}
