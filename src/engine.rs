//! This module contains the engine type that is used as a context in which to
//! run and compile code.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::core::{Term, PTerm, TypeContext};
use crate::name::Name;
use crate::compile::compile;
use crate::c::Program as CProgram;

#[derive(Debug, Clone, Default)]
pub struct Engine { 
    context: RefCell<TypeContext>,
    values: HashMap<Name, PTerm>,
}

impl Engine {
    pub fn new() -> Engine {
        Engine::default()
    }

    pub fn add_variable(&mut self, name: Name, ty: PTerm, value: PTerm) {
        self.context.borrow_mut().insert(name.clone(), ty);
        self.values.insert(name, value);
    }

    #[allow(dead_code)]
    pub fn remove_variable(&mut self, name: &Name) {
        self.context.borrow_mut().remove(name);
        self.values.remove(name);
    }

    pub fn infer_type(&self, mut term: PTerm) -> Result<PTerm, Vec<String>> {
        // Put the values in the term.
        for (name, value) in &self.values {
            term = Term::substitute_or(term, name, value.clone());
        }
        term.infer_type_with_ctx(&mut self.context.borrow_mut())
    }

    pub fn eval(&self, mut term: PTerm) -> PTerm {
        // Put the values in the term.
        for (name, value) in &self.values {
            term = Term::substitute_or(term, name, value.clone());
        }
        Term::eval_or(term)
    }

    pub fn compile(&self, mut term: PTerm) -> CProgram {
        // Put the values in the term.
        for (name, value) in &self.values {
            term = Term::substitute_or(term, name, value.clone());
        }
        compile(term)
    }
}
