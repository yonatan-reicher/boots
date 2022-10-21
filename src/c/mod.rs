/**
 * Contains an types and functions for emiting C code.
 */

pub struct Program {
    pub includes: Vec<Include>,
    pub declarations: Vec<TopLevelDeclaration>,
}

pub enum Include {
    Arrow(String),
    Quote(String),
}

pub enum TopLevelDeclaration {
    Function(Function),
}

pub struct Function {
    pub return_type: TypeExpr,
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub body: Option<Block>,
}

pub struct Parameter {
    pub name: String,
    pub type_expression: TypeExpr,
}

pub enum TypeExpr {
    Var(String),
}

pub type Block = Vec<Statement>;

pub enum Statement {
    Expr(Expr),
    Return(Expr),
    If(Expr, Block, Option<Block>),
    While(Expr, Block),
    For(Expr, Expr, Expr, Block),
    Declaration {
        type_expression: TypeExpr,
        name: String,
        initializer: Option<Expr>,
    },
}

pub enum Expr {
    Var(String),
    Call(Box<Expr>, Vec<Expr>),
    Int(i32),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Cast(TypeExpr, Box<Expr>),
}

pub enum UnaryOp {
    Neg,
}

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

impl Program {
    pub fn to_code(&self) -> String {
        let mut code = String::new();
        for include in &self.includes {
            match include {
                Include::Arrow(name) => code.push_str(&format!("#include <{}>\n", name)),
                Include::Quote(name) => code.push_str(&format!("#include \"{}\"\n", name)),
            }
        }
        for declaration in &self.declarations {
            use TopLevelDeclaration::*;
            match declaration {
                Function(function) => {
                    code.push_str(&format!("{}\n", function.to_code()));
                }
            }
        }
        code
    }
}

impl Function {
    pub fn to_code(&self) -> String {
        let mut code = String::new();

        code.push_str(&format!(
            "{} {}(",
            self.return_type.to_code(),
            &self.name,
        ));

        let mut first = true;
        for parameter in &self.parameters {
            if !first {
                code.push_str(", ");
            }
            first = false;
            code.push_str(parameter.to_code().as_str());
        }

        code
    }
}

impl Expr {
    pub fn to_code(&self) -> String {
        match self {
            Expr::Var(name) => {
                name.into()
            }
            Expr::Int(value) => {
                value.to_string()
            }
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
        }
    }
}

impl TypeExpr {
    pub fn to_code(&self) -> String {
        match self {
            TypeExpr::Var(name) => {
                name.into()
            }
        }
    }
}

pub fn declaration_code(type_expr: &TypeExpr, name: &str) -> String {
    match type_expr {
        TypeExpr::Var(type_name) => {
            format!("{} {}", type_name, name)
        }
    }
}

impl Parameter {
    pub fn to_code(&self) -> String {
        declaration_code(&self.type_expression, &self.name)
    }
}

fn assignment_declaration_code(type_expression: &TypeExpr, name: &str, rhs: &Expr) -> String {
    format!("{} = {}", declaration_code(type_expression, name), rhs.to_code())
}

macro_rules! some_try {
    ($x: expr) => {{
        match $x {
            Ok(res) => res,
            Err(err) => return Some(Err(err)),
        }
    }};
}

