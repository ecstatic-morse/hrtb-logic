//! Quantifier elimination for an atomless Boolean algebra with order constraints.
//!
//! Thanks to Mario Carneiro for formalizing this approach and providing us with a simple QE
//! algorithm.

use crate::{short::*, Formula, Var};
use contracts::*;
use itertools::Itertools;
use std::ops::ControlFlow::{self as Flow, Continue};

impl Formula {
    pub fn eliminate_all_quantifiers(&mut self) {
        let _: Flow<()> = self.visit_with_post_mut(|form| {
            if form.is_bind() {
                form.eliminate_quantifier();
            }

            Continue(())
        });
    }

    #[requires(self.is_bind())]
    fn eliminate_quantifier(&mut self) {
        unwrap!(let Formula::Bind(kind, var, box mut form) = self.take());

        debug_assert!(!form.has_quantifiers());

        // ∀a.P ↔ ¬∃a.¬P
        //            ^
        if kind.is_forall() {
            form = !form;
        }

        form.simplify();
        form.make_disjunctive_normal_form();

        match &mut form {
            Formula::Or(l) => l.iter_mut().for_each(|f| f.eliminate_existential(var)),
            _ => form.eliminate_existential(var),
        };

        // ∀a.P ↔ ¬∃a.¬P
        //        ^
        if kind.is_forall() {
            form = !form
        }

        *self = form;
    }

    fn eliminate_existential(&mut self, exst: Var) {
        // Call the existentially quantified variable `z`.
        let z = exst;

        // Mario Carneiro's QE algorithm transforms an existentially quantified statement like this:
        //
        // ∃z, ⋀ᵢ aᵢ ⊆ z ∧ ⋀ᵢ z ⊆ bᵢ ∧ ⋀ᵢ ¬(cᵢ ⊆ z) ∧ ⋀ᵢ ¬(z ⊆ dᵢ)
        //
        // into the following:
        //
        // ⋀ᵢ,ⱼ aᵢ ⊆ bⱼ ∧ ⋀ᵢ,ⱼ ¬(cᵢ ⊆ aⱼ) ∧ ⋀ᵢ ¬(cᵢ ⊆ ∅) ∧ ⋀ᵢ,ⱼ ¬(bᵢ ⊆ dⱼ)
        //
        // I'll try to explain this part-by-part, although I won't prove that this is sufficient to
        // show that z exists. Only that it is necessary.
        //
        // The intuition for the first term (a ⊆ b) is straightforward. If it does not hold, there
        // is no "room" for z in between a and b, and the quantifier is unsatisfiable.
        //
        // We'll prove that the second is necessary by contradiction.
        // Assume c ⊆ a. We want ∃z a ⊆ z ∧ ¬(c ⊆ z) to hold. By the transitive property, we can
        // substitute a with c in the first inequality, which would give us P ∧ ¬P.
        //
        // The third term is required because ¬(c ⊆ z) is trivially unsatisfiable if c is the empty set.
        //
        // For the final term, use the same approach as for the second. Since there is no global
        // upper bound, there is no analogue to the third term, ¬(c ⊆ z), involving d.

        let mut literals = match self.take() {
            Formula::And(l) => l,
            form => vec![form],
        };

        let mut aa = vec![];
        let mut bb = vec![];
        let mut cc = vec![];
        let mut dd = vec![];

        literals.retain(|form| {
            // At this stage, any formula involving `z` is a subset relation (or its negation)
            // that fits one of the patterns below.
            match *form {
                // a ⊆ z
                Formula::SubsetEq { sub: a, sup } if sup == z => aa.push(a),
                // z ⊆ b
                Formula::SubsetEq { sub, sup: b } if sub == z => bb.push(b),
                // ¬(c ⊆ z)
                Formula::Not(box Formula::SubsetEq { sub: c, sup }) if sup == z => {
                    cc.push(c)
                }
                // ¬(z ⊆ d)
                Formula::Not(box Formula::SubsetEq { sub, sup: d }) if sub == z => {
                    dd.push(d)
                }

                // Formulas that don't involve `z` can be moved outside the quantifier unchanged.
                // Leave them as-is.
                _ => {
                    debug_assert!(!form.has_var(z));
                    return true;
                }
            }

            false
        });

        macro_rules! mk_product {
            ($lower:ident, $upper:ident, $func:expr) => {
                literals.extend($lower.iter().cartesian_product($upper.iter()).map($func))
            };
        }

        // a ⊆ b
        mk_product!(aa, bb, |(&a, &b)| subeq(a, b));

        // ¬(c ⊆ a)
        mk_product!(cc, aa, |(&c, &a)| !subeq(c, a));

        // ¬(b ⊆ d)
        mk_product!(bb, dd, |(&b, &d)| !subeq(b, d));

        // We only need to add the ¬(c ⊆ ∅) constraint if a is empty. Otherwise it follows
        // trivially from the second `mk_product`.
        if aa.is_empty() {
            literals.extend(cc.iter().map(|&c| !empty(c)));
        }

        let ret = match literals.len() {
            0 => true.into(),
            1 => literals.pop().unwrap(),
            _ => Formula::And(literals),
        };

        *self = ret;
    }
}
