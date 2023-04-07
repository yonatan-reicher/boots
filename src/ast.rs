use crate::located::Range;
use crate::name::Name;

pub type PAst = Box<Ast>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Var(Name, Range),
    Appl(PAst, PAst, Vec<Ast>),
    Arrow(ArrowKind, PAst, PAst),
    TypeAnnotation(PAst, PAst),
    Literal(Literal, Range),
    Let(PAst, PAst, PAst),
    Tuple(Vec<Ast>),
    TupleType(Vec<Ast>),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    String(Name),
    Int(i32),
    Prop,
    Type,
}

// Unify with term::ArrowKind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArrowKind {
    Value,
    Type,
}
