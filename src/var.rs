use std::fmt;

/// A free or bound variable.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(pub(crate) u32);

impl Var {
    /// The empty set, `'static`.
    pub const EMPTY: Self = Var(u32::MAX);
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if *self == Var::EMPTY {
            return write!(f, "'static");
        }

        if self.0 <= u32::from(b'z' - b'a') {
            write!(f, "'{}", char::from(b'a' + self.0 as u8))
        } else {
            write!(f, "_{}", self.0)
        }
    }
}
