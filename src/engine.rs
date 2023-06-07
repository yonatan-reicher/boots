//! This module contains the engine type that is used as a context in which to
//! run and compile code.

use std::cell::RefCell;

use crate::c::Program as CProgram;
use crate::compile::compile;
use crate::ast::Ast;
use crate::ast_to_term::{ast_to_term, Error as AstError};
use crate::term::{eval, infer, EvalContext, PTerm, TypeContext, TypeError, Term};
use crate::name::Name;

#[derive(Debug, Clone, Default)]
pub struct Engine {
    type_context: RefCell<TypeContext>,
    eval_context: RefCell<EvalContext>,
    variable_names: Vec<Name>,
}

impl Engine {
    pub fn new() -> Engine {
        Engine::default()
    }

    pub fn add_variable(&mut self, name: Name, ty: PTerm, value: PTerm) {
        self.variable_names.push(name);
        self.type_context.get_mut().push(ty);
        self.eval_context.get_mut().push(Some(value));
    }

    #[allow(dead_code)]
    pub fn remove_variable(&mut self, name: &Name) -> bool {
        let Some((index, _)) = self.variable_names.iter().enumerate().find(|(_, n)| n == &name) else {
            return false;
        };

        self.variable_names.remove(index);
        self.type_context.get_mut().remove(index);
        self.eval_context.get_mut().remove(index);
        return true;
    }

    pub fn ast_to_term(&self, input: &Ast) -> Result<PTerm, Vec<AstError>> {
        ast_to_term(input, &self.variable_names)
    }

    pub fn infer_type(&self, term: PTerm) -> Result<PTerm, Vec<TypeError>> {
        infer(&term, &mut self.type_context.borrow_mut(), &mut self.eval_context.borrow_mut())
    }

    pub fn eval(&self, term: PTerm) -> PTerm {
        eval(&term, &mut self.eval_context.borrow_mut())
    }

    pub fn compile(&self, term: PTerm) -> CProgram {
        /*
        // Put the values in the term.
        for value in self.eval_context.borrow().iter().rev() {
            term = Term::Let(None, value.clone().unwrap(), term).into();
        }
        */
        compile(&self.eval(term))
    }
}
