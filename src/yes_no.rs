pub trait YesNo {
    type If<Then, Else>;
    type Not: YesNo;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Yes;
impl YesNo for Yes {
    type If<Then, Else> = Then;
    type Not = No;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum No {}
impl YesNo for No {
    type If<Then, Else> = Else;
    type Not = Yes;
}

pub mod prelude {
    pub use super::{No, Yes, YesNo};
}
