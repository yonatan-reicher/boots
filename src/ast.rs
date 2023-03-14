use crate::located::Range;

pub type PAst = Box<Ast>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Var(String, Range),
    Appl(PAst, PAst),
    Arrow(ArrowType, PAst, PAst),
    TypeAnnotation(PAst, PAst),
    Literal(Literal),
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
