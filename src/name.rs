use std::fmt::{self, Debug, Display, Formatter};
use std::ops::Deref;
use std::rc::Rc;

// Shared ownership strings made for least copies.
#[derive(Clone)]
pub enum Name {
    Rc(Rc<str>),
    Static(&'static str),
}

use Name::*;

impl Name {
    pub fn from_str(x: &str) -> Self {
        let rc: Rc<str> = x.into();
        rc.into()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        match self {
            Static(x) => x,
            Rc(rc) => rc.as_ref(),
        }
    }
}

impl std::borrow::Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.as_ref()
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
        Debug::fmt(self.as_ref(), f)
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.as_ref(), f)
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        other.as_ref() == self.as_ref()
    }
}

impl Eq for Name {}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

impl std::hash::Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}
