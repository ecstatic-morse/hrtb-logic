use std::mem;
use std::ops::ControlFlow::{Break, Continue};

use contracts::*;
use itertools::Itertools;

use crate::{Formula, List};

impl Formula {
    pub fn disjunctive_normal_form(mut self) -> Self {
        self.make_disjunctive_normal_form();
        self
    }

    #[debug_requires(!self.has_quantifiers())]
    pub fn make_disjunctive_normal_form(&mut self) {
        self.make_negation_normal_form();
        self.make_dnf_();
    }

    pub fn make_dnf_(&mut self) {
        // Flattens one level of nested connectives, e.g. `And([And(...), ...])`
        macro_rules! flatten_connective {
            ($list:expr, $Kind:ident) => {{
                let len = $list.len();
                for i in 0..len {
                    let form = &mut $list[i];
                    if let Self::$Kind(inner) = form {
                        let mut inner = mem::take(inner).into_iter();

                        if let Some(head) = inner.next() {
                            *form = head;
                            $list.extend(inner);
                        }
                    }
                }
            }};
        }

        match self {
            Self::Trivial(_) | Self::Prop(..) | Self::SubsetEq { .. } => {}

            // No need to recurse into a negation. We're already in NNF.
            Self::Not(form) => debug_assert!(form.is_atomic()),

            Self::Or(list) => {
                list.iter_mut().for_each(Formula::make_dnf_);
                flatten_connective!(list, Or); // ((a ∨ b) ∨ c) → (a ∨ b ∨ c)
            }

            Self::And(conj) => {
                conj.iter_mut().for_each(Formula::make_dnf_);
                flatten_connective!(conj, And); // ((a ∧ b) ∧ c) → (a ∧ b ∧ c)

                // If we don't have any OR clauses, there's nothing to distribute. We're done.
                if !conj.iter().any(Formula::is_or) {
                    return;
                }

                // Separate atomic formulas (and their negations) from ORs. After this, each
                // formula in `and_clauses` is an OR. We'll handle these separately.
                let atomics: List<_> = conj.drain_filter(|f| f.is_atomic() || f.is_not()).collect();
                debug_assert!(conj.iter().all(Formula::is_or));

                let disj: List<_> = conj
                    .iter()
                    .map(|or| {
                        unwrap!(let Self::Or(list) = or);
                        list.iter().cloned()
                    })
                    .multi_cartesian_product()
                    .map(|mut list| {
                        flatten_connective!(list, And);

                        // Don't forget the atomics from the original conjunction.
                        list.extend(atomics.iter().cloned());
                        Formula::And(list)
                    })
                    .collect();

                *self = Self::Or(disj);
            }

            Self::Bind(..) => panic!("formula is not quantifier-free"),
        }
    }

    pub fn is_disjunctive_normal_form(&self) -> bool {
        struct NotDnf;

        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum Depth {
            Top,
            Or,
            And,
            Not,
        }

        self.visit_with_stateful(Depth::Top, |form, &depth| {
            #[rustfmt::skip]
            let new_depth = match form {
                | Formula::Prop(_)
                | Formula::Trivial(_)
                | Formula::SubsetEq { .. }
                => return Continue(depth),

                Formula::Bind(..) => return Break(NotDnf),

                Formula::Not(_) => Depth::Not,
                Formula::And(_) => Depth::And,
                Formula::Or(_) => Depth::Or,
            };

            // If we want to allow nested connectives, this could be `<`.
            if new_depth <= depth {
                return Break(NotDnf);
            }

            Continue(new_depth)
        })
        .is_continue()
    }
}
