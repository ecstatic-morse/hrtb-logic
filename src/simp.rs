#[allow(unused_imports)]
use std::ops::ControlFlow::{self as Flow, Break, Continue};

use crate::{Formula, Var};

impl Formula {
    /// Rewrites a connective to remove boolean constants.
    ///
    /// Applies the following identities:
    ///
    /// - ¬⊥ → ⊤
    /// - ¬⊤ → ⊥
    /// - ⊥ ∨ P → P
    /// - ⊤ ∧ P → P
    /// - ⊤ ∨ P → ⊤
    /// - ⊥ ∧ P → ⊥
    pub fn simplify_trivial_connective(&mut self) {
        let (l, short_circ) = match self {
            Formula::Not(box Formula::Trivial(sat)) => {
                *self = (!*sat).into();
                return;
            }

            Formula::Or(l) => (l, true),
            Formula::And(l) => (l, false),

            _ => return,
        };

        // (⊥ ∨ P → P) ∧ (⊤ ∧ P → P)
        l.retain(|f| !matches!(f, Formula::Trivial(sat) if *sat != short_circ));

        // (⊤ ∨ P → ⊤) ∧ (⊥ ∧ P → ⊥)
        if l.iter()
            .any(|f| matches!(f, Formula::Trivial(sat) if *sat == short_circ))
        {
            *self = short_circ.into();
        }
    }

    /// Recursively rewrites a formula to remove any boolean constants inside a connective.
    pub fn simplify_all_trivial_connectives(&mut self) {
        let _: Flow<()> = self.visit_with_post_mut(|form| {
            form.simplify_trivial_connective();
            Continue(())
        });
    }

    /// Returns `true` if this formula contains a literal false or true as part of a connective.
    #[cfg(test)]
    pub(crate) fn has_trivial_connectives(&mut self) -> bool {
        self.visit_with_pre(|form| match form {
            Formula::Or(l) | Formula::And(l) if l.iter().any(Formula::is_trivial) => Break(()),
            Formula::Not(box Formula::Trivial(_)) => Break(()),

            _ => Continue(()),
        })
        .is_break()
    }

    /// Replaces trivial subset relations with their truth values.
    ///
    /// Applies the following identities:
    ///
    /// - ∅ ⊆ x → ⊤
    /// - x ⊆ x → ⊤
    pub fn simplify_subset_identity(&mut self) {
        #[rustfmt::skip]
        let new = match self {
            Formula::SubsetEq { sub: Var::EMPTY, sup: _ } => true.into(),
            Formula::SubsetEq { sub, sup } if sub == sup => true.into(),

            _ => return,
        };

        *self = new
    }

    pub fn simplify_all_subset_identities(&mut self) {
        let _: Flow<()> = self.visit_with_pre_mut(|form| {
            form.simplify_subset_identity();
            Continue(())
        });
    }

    pub fn simplify(&mut self) {
        let _: Flow<()> = self.visit_with_post_mut(|form| {
            // NOTE: Order matters.
            form.simplify_subset_identity();
            form.simplify_trivial_connective();

            Continue(())
        });
    }
}
