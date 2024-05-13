use std::{
    collections::HashMap,
    fmt::Display,
    ops::Index,
    sync::atomic::{AtomicU64, Ordering::SeqCst},
};

use crate::symbol::Symbol;

static NEXT_VARIABLE_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Func(Box<Type>, Box<Type>),
    Variable(u64),
}

impl Type {
    pub fn fresh() -> Type {
        Type::Variable(NEXT_VARIABLE_ID.fetch_add(1, SeqCst))
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Func(t1, t2) => write!(f, "({t1} -> {t2})"),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polytype {
    quantifiers: Vec<u64>,
    ty: Type,
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

#[derive(Debug)]
pub struct Env(im::HashMap<Symbol, Type>);

impl Env {
    pub fn empty() -> Self {
        Self(im::HashMap::new())
    }

    pub fn unit(name: Symbol, t: Type) -> Self {
        Self(im::HashMap::unit(name, t))
    }

    pub fn contains(&self, name: &Symbol) -> bool {
        self.0.contains_key(name)
    }

    pub fn without(&self, name: &Symbol) -> Self {
        let mut ret = self.0.clone();
        ret.remove(name);
        Self(ret)
    }

    pub fn union(&self, other: &Self) -> Self {
        Self(self.0.clone().union(other.0.clone()))
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &Type)> {
        self.0.iter()
    }
}

impl Index<&Symbol> for Env {
    type Output = Type;

    fn index(&self, index: &Symbol) -> &Self::Output {
        &self.0[index]
    }
}

impl Substitutable for Env {
    fn substitute(&self, subst: &Substitution) -> Self {
        Env(self
            .0
            .iter()
            .map(|(name, t)| (name.clone(), t.substitute(subst)))
            .collect())
    }
}
