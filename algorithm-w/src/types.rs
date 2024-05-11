use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Func(Box<Type>, Box<Type>),
    Variable(u64),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Func(t1, t2) => write!(f, "{t1} -> {t2}"),
            Type::Variable(id) => write!(f, "t{id}"),
        }
    }
}

impl Type {
    pub fn occur(&self, id: u64) -> bool {
        use Type::*;
        match self {
            Int | Bool => false,
            Func(t1, t2) => t1.occur(id) || t2.occur(id),
            Variable(id_) => *id_ == id,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Substitution(HashMap<u64, Type>);

impl Substitution {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn apply(&self, id: u64) -> Option<Type> {
        self.0.get(&id).cloned()
    }

    pub fn add(&mut self, id: u64, t: Type) {
        self.0.insert(id, t);
    }
}

impl<const N: usize> From<[(u64, Type); N]> for Substitution {
    fn from(value: [(u64, Type); N]) -> Self {
        Self(HashMap::from(value))
    }
}

pub trait Substitutable {
    fn substitute(&self, subst: &Substitution) -> Self;
}

impl Substitutable for Type {
    fn substitute(&self, subst: &Substitution) -> Self {
        use Type::*;
        match self {
            Int | Bool => self.clone(),
            Func(t1, t2) => Func(
                Box::new(t1.substitute(subst)),
                Box::new(t2.substitute(subst)),
            ),
            Variable(id) => {
                if let Some(t) = subst.apply(*id) {
                    t
                } else {
                    self.clone()
                }
            }
        }
    }
}

pub struct Equal(pub Type, pub Type);

impl Substitutable for Equal {
    fn substitute(&self, subst: &Substitution) -> Self {
        let Equal(t1, t2) = self;
        Equal(t1.substitute(subst), t2.substitute(subst))
    }
}

impl Substitutable for Vec<Equal> {
    fn substitute(&self, subst: &Substitution) -> Self {
        self.iter().map(|eq| eq.substitute(subst)).collect()
    }
}
