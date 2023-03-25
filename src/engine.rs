//! This module contains the engine type that is used as a context in which to
//! run and compile code.

use std::cell::RefCell;

use crate::c::Program as CProgram;
use crate::compile::compile;
use crate::term::{eval, infer, EvalContext, PTerm, Term, TypeContext, TypeError};
use crate::name::Name;

#[derive(Debug, Clone, Default)]
pub struct Engine {
    type_context: RefCell<TypeContext>,
    eval_context: RefCell<EvalContext>,
}

impl Engine {
    pub fn new() -> Engine {
        Engine::default()
    }

    pub fn add_variable(&mut self, name: Name, ty: PTerm, value: PTerm) {
        self.type_context.get_mut().insert(name.clone(), ty);
        self.eval_context.get_mut().insert(name, value);
    }

    #[allow(dead_code)]
    pub fn remove_variable(&mut self, name: &Name) {
        self.type_context.get_mut().remove(name);
        self.eval_context.get_mut().remove(name);
    }

    pub fn infer_type(&self, mut term: PTerm) -> Result<PTerm, Vec<TypeError>> {
        // Put the values in the term.
        for (name, value) in self.eval_context.borrow().iter() {
            term = Term::substitute_or(term, name, value.clone());
        }
        infer(&term, &mut self.type_context.borrow_mut())
    }

    pub fn eval(&self, mut term: PTerm) -> PTerm {
        // Put the values in the term.
        for (name, value) in self.eval_context.borrow().iter() {
            term = Term::substitute_or(term, name, value.clone());
        }
        eval(&term, &mut self.eval_context.borrow_mut())
    }

    pub fn compile(&self, mut term: PTerm) -> CProgram {
        // Put the values in the term.
        for (name, value) in self.eval_context.borrow().iter() {
            term = Term::substitute_or(term, name, value.clone());
        }
        compile(term)
    }
}
