use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use std::rc::Rc;

// Shared ownership strings made for least copies.
#[derive(Clone)]
pub enum Name {
    Rc(Rc<str>),
    Static(&'static str),
}

use Name::*;

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        match self {
            Static(x) => x,
            Rc(rc) => rc.as_ref(),
        }
    }
}

impl Deref for Name {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_ref()
    }
}

impl From<&Name> for String {
    fn from(name: &Name) -> Self {
        name.as_ref().into()
    }
}

impl From<&'static str> for Name {
    fn from(x: &'static str) -> Self {
        Static(x)
    }
}

impl From<Rc<str>> for Name {
    fn from(rc: Rc<str>) -> Self {
        Rc(rc)
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}
