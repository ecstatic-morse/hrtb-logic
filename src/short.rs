//! Terse constructors for various `Formula`s.

use crate::{Formula, QuantifierKind, Var, P};

pub const fn var(c: char) -> Var {
    let c = c.to_ascii_lowercase();
    assert!(c.is_ascii_lowercase());

    let x = c as u32 - 'a' as u32;
    Var(x)
}

pub fn not(form: Formula) -> Formula {
    if let Formula::Trivial(sat) = form {
        return (!sat).into();
    }

    Formula::Not(P::new(form))
}

pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(vec![a, b])
}

pub fn or_(forms: impl IntoIterator<Item = Formula>) -> Formula {
    Formula::Or(forms.into_iter().collect())
}

pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(vec![a, b])
}

pub fn and_(forms: impl IntoIterator<Item = Formula>) -> Formula {
    Formula::And(forms.into_iter().collect())
}

pub fn implies(antecedent: Formula, consequent: Formula) -> Formula {
    or(not(antecedent), consequent)
}

pub fn iff(a: Formula, b: Formula) -> Formula {
    and(implies(a.clone(), b.clone()), implies(b, a))
}

pub fn forall(var: Var, form: Formula) -> Formula {
    Formula::Bind(QuantifierKind::ForAll, var, P::new(form))
}

pub fn exists(var: Var, form: Formula) -> Formula {
    Formula::Bind(QuantifierKind::Exists, var, P::new(form))
}

pub const fn subeq(sub: Var, sup: Var) -> Formula {
    Formula::SubsetEq { sub, sup }
}

/// a ⊂ b, expressed as a ⊆ b ∧ ¬(a ⊆ b ∧ b ⊆ a).
pub fn subne(sub: Var, sup: Var) -> Formula {
    and(subeq(sub, sup), !and(subeq(sub, sup), subeq(sup, sub)))
}

pub fn empty(var: Var) -> Formula {
    subeq(var, Var::EMPTY)
}

pub const fn prop(s: &'static str) -> Formula {
    Formula::Prop(s)
}
