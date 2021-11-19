use std::mem;
use std::ops::ControlFlow::{Break, Continue};

use crate::{short::*, Formula};

impl Formula {
    pub fn negation_normal_form(mut self) -> Self {
        self.make_negation_normal_form();
        self
    }

    pub fn make_negation_normal_form(&mut self) {
        self.make_nnf_(false);
    }

    fn make_nnf_(&mut self, invert: bool) {
        match self {
            Self::Trivial(sat) => {
                if invert {
                    *sat = !*sat;
                }
            }

            Self::Prop(..) | Self::SubsetEq { .. } => {
                if invert {
                    *self = not(self.clone());
                }
            }

            Self::Not(form) => {
                form.make_nnf_(!invert);
                *self = form.take()
            }

            Self::And(list) => {
                list.iter_mut().for_each(|form| form.make_nnf_(invert));
                if invert {
                    *self = Self::Or(mem::take(list));
                }
            }
            Self::Or(list) => {
                list.iter_mut().for_each(|form| form.make_nnf_(invert));
                if invert {
                    *self = Self::And(mem::take(list));
                }
            }

            Self::Bind(kind, _, form) => {
                if invert {
                    *kind = kind.dual();
                }

                form.make_nnf_(invert)
            }
        }
    }

    /// Returns `true` if this formula is in negation normal form, i.e. if it has only atomic
    /// formulas inside a `Not`.
    pub fn is_negation_normal_form(&self) -> bool {
        let inside_negation = false;
        self.visit_with_stateful(inside_negation, |form, &in_neg| {
            if in_neg && !form.is_atomic() {
                return Break(());
            }

            Continue(form.is_not())
        })
        .is_continue()
    }
}
