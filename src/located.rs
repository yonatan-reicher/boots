// TODO: Implement order for Pos and region

pub type Pos = usize;
 
pub type Range = std::ops::Range<Pos>;

#[derive(Clone, Hash, Debug, PartialEq, Eq)] 
pub struct Located<T>(pub T, pub Range);

pub trait AsLocated<T>: Into<T> {
    fn as_located(self, range: Range) -> Located<T> {
        Located(self.into(), range)
    }
}

impl<T> AsLocated<T> for T {}
