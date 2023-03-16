use crate::located::Range;
use crate::name::Name;

pub type PAst = Box<Ast>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Var(Name, Range),
    Appl(PAst, PAst, Vec<Ast>),
    Arrow(ArrowType, PAst, PAst),
    TypeAnnotation(PAst, PAst),
    Literal(Literal, Range),
    Let(PAst, PAst, PAst),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    String(String),
    Int(i32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArrowType {
    Value,
    Type,
}
