//! This module contains traits that are implemented automatically which make
//! it easy to combine C expressions and statements to bigger expression and
//! statements.

use crate::c::{BinaryOp, Block, Expr, PTypeExpr, Statement, TypeExpr};
use crate::name::Name;

/// Implements functions for making expressions out of other things.
pub trait CombExpr1: Into<Box<Expr>> {
    /// Makes an access expression.
    fn arrow(self, field: impl Into<Name>) -> Expr {
        Expr::Arrow(self.into(), field.into())
    }

    fn inc(self) -> Expr {
        Expr::Inc(self.into())
    }

    fn dec(self) -> Expr {
        Expr::Dec(self.into())
    }

    fn eq(self, other: impl Into<Box<Expr>>) -> Expr {
        Expr::Binary(BinaryOp::Eq, self.into(), other.into())
    }

    /// Makes a call expression to this function.
    fn call(self, parameters: impl Into<Vec<Expr>>) -> Expr {
        Expr::Call(self.into(), parameters.into())
    }

    /// Makes an expression that casts this to another type.
    fn cast(self, type_expr: impl Into<PTypeExpr>) -> Expr {
        Expr::Cast(type_expr.into(), self.into())
    }
}

// Implement `CombExpr1` for everything you can!
impl<T> CombExpr1 for T where T: Into<Box<Expr>> {}

/// Implements functions for making expressions out of other things.
/// The difference between this and the other trait is the required bound.
pub trait CombExpr2: Into<Expr> {
    /// Makes a return statement of this expression.
    fn ret(self) -> Statement {
        Statement::Return(self.into())
    }

    /// Makes this expresssion an expression-statement.
    fn stmt(self) -> Statement {
        Statement::Expr(self.into())
    }

    /// Assigns another expression this this expression.
    fn assign(self, expr: impl Into<Expr>) -> Statement {
        Statement::Assign(self.into(), expr.into())
    }

    /// Assign this expression to a new variable!
    fn variable(self, name: impl Into<Name>, type_expr: impl Into<PTypeExpr>) -> Statement {
        Statement::Declaration {
            type_expression: type_expr.into(),
            name: name.into(),
            initializer: self.into(),
        }
    }

    fn if_then(self, true_block: impl Into<Block>) -> Statement {
        Statement::If(self.into(), true_block.into(), None)
    }
}

impl<T> CombExpr2 for T where T: Into<Expr> {}

pub trait CombTypeExpr: Into<PTypeExpr> {
    fn sizeof(self) -> Expr {
        Expr::SizeOf(self.into())
    }

    fn ptr(self) -> TypeExpr {
        TypeExpr::Ptr(self.into())
    }

    fn function_ptr(self, parameters: impl Into<Vec<PTypeExpr>>) -> TypeExpr {
        TypeExpr::FunctionPtr(self.into(), parameters.into())
    }
}

impl<T> CombTypeExpr for T where T: Into<PTypeExpr> {}

pub trait CombName: Into<Name> {
    fn var(self) -> Expr {
        Expr::Var(self.into())
    }

    fn type_var(self) -> TypeExpr {
        TypeExpr::Var(self.into())
    }

    fn struct_type_var(self) -> TypeExpr {
        TypeExpr::StructVar(self.into())
    }
}

impl<T> CombName for T where T: Into<Name> {}

pub trait CombInt: Into<i32> {
    fn literal(self) -> Expr {
        Expr::Int(self.into())
    }
}

impl CombInt for i32 {}
