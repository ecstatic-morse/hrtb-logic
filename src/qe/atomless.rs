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

        // ∀x.P ↔ ¬∃x.¬P
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

        // ∀x.P ↔ ¬∃x.¬P
        //        ^
        if kind.is_forall() {
            form = !form
        }

        *self = form;
    }

    fn eliminate_existential(&mut self, exst: Var) {
        let mut literals = match self.take() {
            Formula::And(l) => l,
            form => vec![form],
        };

        let mut lowers = vec![];
        let mut uppers = vec![];
        let mut strict_uppers = vec![];
        let mut strict_lowers = vec![];

        literals.retain(|form| {
            if !form.has_var(exst) {
                return true;
            }

            match *form {
                // a ⊆ w
                Formula::SubsetEq { sub, sup } if sub == exst => uppers.push(sup),
                // x ⊆ a
                Formula::SubsetEq { sub, sup } if sup == exst => lowers.push(sub),
                // y ⊂ a
                Formula::Not(box Formula::SubsetEq { sub, sup }) if sub == exst => {
                    strict_lowers.push(sup)
                }
                // a ⊂ z
                Formula::Not(box Formula::SubsetEq { sub, sup }) if sup == exst => {
                    strict_uppers.push(sub)
                }

                _ => unreachable!(),
            }

            false
        });

        macro_rules! mk_product {
            ($lower:ident, $upper:ident, $func:expr) => {
                literals.extend($lower.iter().cartesian_product($upper.iter()).map($func))
            };
        }

        // Relate each upper bound with each lower bound. If either bound is strict, the relation
        // is also strict.
        mk_product!(lowers, uppers, |(&sub, &sup)| subeq(sub, sup));
        mk_product!(lowers, strict_uppers, |(&sub, &sup)| subne(sub, sup));
        mk_product!(strict_lowers, uppers, |(&sub, &sup)| subne(sub, sup));
        mk_product!(strict_lowers, strict_uppers, |(&sub, &sup)| subne(sub, sup));

        // If we have no lower bounds, we need to explicitly encode the fact that ∃a.a ⊂ x is only
        // satisfiable if x is not the empty set. If we have lower bounds, this is implicit because
        // we will have a strict subset constraint on some free region.
        if lowers.is_empty() && strict_lowers.is_empty() {
            literals.extend(strict_uppers.iter().map(|&upper| not_empty(upper)));
        }

        let ret = match literals.len() {
            0 => true.into(),
            1 => literals.pop().unwrap(),
            _ => Formula::And(literals),
        };

        *self = ret;
    }
}
