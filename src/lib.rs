#![feature(drain_filter, box_patterns, let_else, control_flow_enum)]

#[macro_use]
mod util;

mod dnf;
mod form;
mod nnf;
mod qe;
pub mod short;
mod simp;
#[cfg(test)]
mod tests;
mod var;
pub mod visit;

pub use form::{Formula, QuantifierKind};
pub use var::Var;

type P<T> = Box<T>;
type List<T> = Vec<T>;
