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

        match self.0 {
            c @ 0..=26 => write!(f, "'{}", char::from(b'a' + c as u8)),
            n => write!(f, "_{}", n),
        }
    }
}
