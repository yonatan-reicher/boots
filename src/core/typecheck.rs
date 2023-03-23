use std::collections::HashMap;

use crate::core::{Term, PTerm};
use crate::name::Name;

pub type Context = HashMap<Name, PTerm>;

pub struct TypedTerm {
    term: Term,
    ty: PTerm,
}
