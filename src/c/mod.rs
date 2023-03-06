/**
 * Contains an types and functions for emiting C code.
 */
mod indented_text;
pub mod combine_traits;

use std::rc::Rc;

use crate::name::Name;
use indented_text::IndentedText as I;

trait MultilineCode {
    fn to_code_i(&self) -> I;

    fn to_code(&self) -> String {
        self.to_code_i().to_string()
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub includes: Vec<Include>,
    pub declarations: Vec<TopLevelDeclaration>,
}

#[derive(Debug, Clone)]
pub enum Include {
    Arrow(String),
    Quote(String),
}

// TODO: Think about using PTypeExpr instead of just TypeExpr in the following datastructures.

#[derive(Debug, Clone)]
pub enum TopLevelDeclaration {
    Function(Function),
    Typedef(TypeExpr, Name),
    Struct(Name, Vec<(PTypeExpr, Name)>),
}

#[derive(Debug, Clone)]
pub struct Function {
    pub return_type: PTypeExpr,
    pub name: Name,
    pub parameters: Vec<(PTypeExpr, Name)>,
    pub body: Option<Block>,
}

#[derive(Debug, Clone)]
pub enum TypeExpr {
    Var(Name),
    StructVar(Name),
    Ptr(PTypeExpr),
    Struct(Vec<(PTypeExpr, Name)>),
    FunctionPtr(PTypeExpr, Vec<PTypeExpr>),
}

pub type PTypeExpr = Rc<TypeExpr>;

pub type Block = Vec<Statement>;

#[derive(Debug, Clone)]
pub enum Statement {
    Expr(Expr),
    Assign(Expr, Expr),
    Return(Expr),
    If(Expr, Block, Option<Block>),
    While(Expr, Block),
    For(Expr, Expr, Expr, Block),
    Declaration {
        type_expression: PTypeExpr,
        name: Name,
        initializer: Expr,
    },
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var(Name),
    Call(Box<Expr>, Vec<Expr>),
    Int(i32),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Cast(PTypeExpr, Box<Expr>),
    SizeOf(PTypeExpr),
    Arrow(Box<Expr>, Name),
    Dot(Box<Expr>, Name),
    Inc(Box<Expr>),
    Dec(Box<Expr>),
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Neg,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl MultilineCode for Program {
    fn to_code_i(&self) -> I {
        I::many([
            I::lines(self.includes.iter().map(|include| match include {
                Include::Arrow(path) => format!("#include <{}>", path),
                Include::Quote(path) => format!("#include \"{}\"", path),
            })),
            I::line_str(""),
            I::many_vec(
                self.declarations
                    .iter()
                    .map(|decl| decl.to_code_i().then(I::line_str("")))
                    .collect(),
            ),
        ])
    }
}

impl Program {
    pub fn to_code(&self) -> String {
        <Self as MultilineCode>::to_code(self)
    }
}

impl MultilineCode for TopLevelDeclaration {
    fn to_code_i(&self) -> I {
        use TopLevelDeclaration::*;
        match self {
            Function(function) => function.to_code_i(),
            Typedef(typ, name) => I::line(format!("typedef {};", typ.to_code_with_name_typedef(name))),
            Struct(name, fields) => I::line(struct_code(Some(name), fields)),
        }
    }
}

impl MultilineCode for Function {
    fn to_code_i(&self) -> I {
        I::line(format!(
            "{} {}({})",
            self.return_type.to_code(),
            self.name.as_ref(),
            &self
                .parameters
                .iter()
                .map(|(typ, name)| typ.to_code_with_name(name))
                .collect::<Vec<_>>()
                .join(", "),
        ))
        .then(if let Some(body) = &self.body {
            I::many([
                I::AddToLastLine(" {".into()),
                I::many_vec(body.iter().map(|stmt| stmt.to_code_i()).collect()).indent(),
                I::line("}".into()),
            ])
        } else {
            I::AddToLastLine(";".into())
        })
    }
}

fn block_code(x: &Block) -> I {
    I::many_vec(x.iter().map(|s| s.to_code_i()).collect())
}

impl MultilineCode for Statement {
    fn to_code_i(&self) -> I {
        match self {
            Statement::Expr(expr) => I::line(expr.to_code() + ";"),
            Statement::Return(expr) => I::line(format!("return {};", expr.to_code())),
            Statement::If(cond, then, else_) => I::many([
                I::line(format!("if ({}) {{", cond.to_code())),
                I::indent(block_code(then)),
                if let Some(else_) = else_ {
                    I::many([I::line_str("}} else {{"), I::indent(block_code(else_))])
                } else {
                    I::Empty
                },
                I::line_str("}}"),
            ]),
            Statement::While(cond, body) => I::many([
                I::line(format!("while ({}) {{", cond.to_code())),
                I::indent(block_code(body)),
                I::line_str("}}"),
            ]),
            Statement::For(start, cond, inc, body) => I::many([
                I::line(format!(
                    "for ({}; {}; {}) {{",
                    start.to_code(),
                    cond.to_code(),
                    inc.to_code(),
                )),
                I::indent(block_code(body)),
                I::line_str("}}"),
            ]),
            Statement::Declaration {
                type_expression,
                name,
                initializer,
            } => I::line(assignment_declaration_code(type_expression, name, initializer) + ";"),
            Statement::Assign(left, right) => {
                // TODO: Check that left can be assigned.
                I::line(format!("{} = {};", left.to_code(), right.to_code()))
            }
        }
    }
}

impl Expr {
    pub fn to_code(&self) -> String {
        match self {
            Expr::Var(name) => name.into(),
            Expr::Int(value) => value.to_string(),
            Expr::Call(function, arguments) => {
                let mut code = String::new();
                code.push_str(function.to_code().as_str());
                code.push_str("(");
                code.push_str(
                    arguments
                        .iter()
                        .map(|argument| argument.to_code())
                        .collect::<Vec<String>>()
                        .join(", ")
                        .as_str(),
                );
                code.push_str(")");
                code
            }
            Expr::Unary(op, expr) => {
                let mut code = String::new();
                code.push_str("(");
                code.push_str(match op {
                    UnaryOp::Neg => "-",
                });
                code.push_str(expr.to_code().as_str());
                code.push_str(")");
                code
            }
            Expr::Binary(op, lhs, rhs) => {
                let mut code = String::new();
                code.push_str("(");
                code.push_str(lhs.to_code().as_str());
                code.push_str(match op {
                    BinaryOp::Add => " + ",
                    BinaryOp::Sub => " - ",
                    BinaryOp::Mul => " * ",
                    BinaryOp::Div => " / ",
                    BinaryOp::Eq => " == ",
                    BinaryOp::Neq => " != ",
                    BinaryOp::Lt => " < ",
                    BinaryOp::Le => " <= ",
                    BinaryOp::Gt => " > ",
                    BinaryOp::Ge => " >= ",
                });
                code.push_str(rhs.to_code().as_str());
                code.push_str(")");
                code
            }
            Expr::Cast(type_expr, expr) => {
                let mut code = String::new();
                code.push_str("((");
                code.push_str(type_expr.to_code().as_str());
                code.push_str(")");
                code.push_str(expr.to_code().as_str());
                code.push_str(")");
                code
            }
            Expr::Arrow(e, name) => {
                e.to_code() + "->" + name
            }
            Expr::Dot(e, name) => {
                e.to_code() + "." + name
            }
            Expr::SizeOf(type_expr) => {
                format!("sizeof({})", type_expr.to_code())
            }
            Expr::Inc(e) => {
                e.to_code() + "++"
            }
            Expr::Dec(e) => {
                e.to_code() + "--"
            }
        }
    }
}

fn struct_code(struct_type_name: Option<&str>, fields: &Vec<(PTypeExpr, Name)>) -> String {
    // Write to a buffer piece by piece.
    let mut buf = String::new();

    buf += "struct ";
    if let Some(name) = struct_type_name {
        buf += &name;
        buf += " ";
    } 
    buf += "{ ";

    for (field_typ, field_name) in fields {
        buf += &field_typ.to_code_with_name(field_name);
        buf += "; ";
    }

    buf += "}";
    buf
}

impl TypeExpr {
    /// Convert a type expression to a string. Does not take names into account.
    pub fn to_code(&self) -> String {
        use TypeExpr::*;
        match self {
            Var(name) => name.into(),
            StructVar(name) => "struct ".to_string() + name.as_ref(),
            Struct(fields) => struct_code(None, fields),
            FunctionPtr(_, _) => self.to_code_with_name(""),
            Ptr(typ) => typ.to_code() + "*",
        }
    }

    /// Convert a type expression to a string, of a value with a name such as
    /// a variable or a parameter.
    pub fn to_code_with_name(&self, name: &str) -> String {
        use TypeExpr::*;
        match self {
            FunctionPtr(ret, params) => {
                let mut buf = String::new();
                buf += &ret.to_code();
                buf += " (*";
                buf += name;
                buf += ")(";
                for (i, param) in params.iter().enumerate() {
                    if i != 0 {
                        buf += ", ";
                    }
                    buf += &param.to_code();
                }
                buf += ")";
                buf
            }
            Ptr(typ) => format!("{} *{name}", &typ.to_code()),
            _ => format!("{} {}", self.to_code(), name),
        }
    }

    /// Convert a type expression to a string, of a value with a name for a
    /// typedef.
    /// The difference is that in a typedef, a struct needs to get the name
    /// while in a variable declaration, it should not.
    ///
    /// Example:
    /// ```c
    /// typedef struct foo { int bar; } foo;
    /// struct { int bar; } my_foo; // No name after struct keyword!
    /// ```
    pub fn to_code_with_name_typedef(&self, name: &str) -> String {
        use TypeExpr::*;
        match self {
            Struct(fields) => struct_code(Some(name), fields) + " " + name,
            _ => self.to_code_with_name(name),
        }
    }
}

fn assignment_declaration_code(type_expression: &TypeExpr, name: &str, rhs: &Expr) -> String {
    format!(
        "{} = {}",
        type_expression.to_code_with_name(name),
        rhs.to_code()
    )
}

/*
macro_rules! some_try {
    ($x: expr) => {{
        match $x {
            Ok(res) => res,
            Err(err) => return Some(Err(err)),
        }
    }};
}
*/

// Implement some conversions.
impl From<Name> for Expr {
    fn from(name: Name) -> Self {
        Expr::Var(name)
    }
}

impl From<Name> for TypeExpr {
    fn from(name: Name) -> Self {
        TypeExpr::Var(name)
    }
}
