// TODO: Implement order for Pos and region

use std::ops::{Deref, DerefMut, Add};
use std::cmp::{min, max};

pub type Pos = usize;
 
#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq)] 
pub struct Range(pub Pos, pub Pos);

impl From<std::ops::Range<Pos>> for Range {
    fn from(range: std::ops::Range<Pos>) -> Self {
        Range(range.start, range.end)
    }
}

impl Add<Range> for Range {
    type Output = Range;

    fn add(self, rhs: Range) -> Self::Output {
        Range(min(self.0, rhs.0), max(self.1, rhs.1))
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq)] 
pub struct Located<T>(pub T, pub Range);

impl<T> Located<T> {
    #[allow(dead_code)]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Located<U> {
        Located(f(self.0), self.1)
    }
}

impl<T> Deref for Located<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Located<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub trait IntoLocated<T>: Into<T> {
    fn into_located(self, range: impl Into<Range>) -> Located<T> {
        Located(self.into(), range.into())
    }
}

impl<T> IntoLocated<T> for T {}
