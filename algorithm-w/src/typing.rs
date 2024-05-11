use crate::types::{Equal, Substitutable, Substitution, Type};

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
