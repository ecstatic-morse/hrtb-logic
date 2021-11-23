use std::ops::ControlFlow::{self as Flow, Break, Continue};
use std::{fmt, mem, ops};

use crate::visit::{AnonFormVisitor, AnonFormVisitorMut, Visit, VisitMut};
use crate::{short::*, List, Var, P};

/// A quantifier, either "for all", or "there exists".
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum QuantifierKind {
    ForAll,
    Exists,
}

impl fmt::Display for QuantifierKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Self::ForAll => "∀",
            Self::Exists => "∃",
        };

        write!(f, "{}", s)
    }
}

impl QuantifierKind {
    pub fn dual(self) -> Self {
        match self {
            Self::ForAll => Self::Exists,
            Self::Exists => Self::ForAll,
        }
    }

    pub fn is_exists(&self) -> bool {
        matches!(self, Self::Exists)
    }

    pub fn is_forall(&self) -> bool {
        matches!(self, Self::ForAll)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Formula {
    /// An opaque proposition, used for testing.
    Prop(&'static str),

    Trivial(bool),
    Not(P<Formula>),
    And(List<Formula>),
    Or(List<Formula>),

    /// An existential or universal quantifier over some variable.
    Bind(QuantifierKind, Var, P<Formula>),

    SubsetEq {
        sub: Var,
        sup: Var,
    },
}

impl From<bool> for Formula {
    fn from(x: bool) -> Self {
        Formula::Trivial(x)
    }
}

impl ops::Not for Formula {
    type Output = Self;

    fn not(self) -> Self::Output {
        not(self)
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn needs_parens(form: &Formula) -> bool {
            match form {
                Formula::Trivial(_) | Formula::Prop(..) => false,
                Formula::Not(inner) => needs_parens(inner),
                _ => true,
            }
        }

        match self {
            Formula::Trivial(true) => write!(f, "True"),
            Formula::Trivial(false) => write!(f, "False"),
            Formula::Prop(s) => write!(f, "{}", s),

            Formula::SubsetEq { sub, sup } => write!(f, "{:?} ⊆ {:?}", sub, sup),

            Formula::Bind(kind, var, form @ box Formula::Bind(..)) => {
                write!(f, "{}{:?}{}", kind, var, form)
            }
            Formula::Bind(kind, var, form) => write!(f, "{}{:?}.({})", kind, var, form),

            Formula::Not(inner) if !needs_parens(&**inner) => write!(f, "¬{}", inner),
            Formula::Not(form) => write!(f, "¬({})", form),

            Formula::And(list) | Formula::Or(list) => {
                let sep = match self {
                    Formula::And(_) => '∧',
                    Formula::Or(_) => '∨',
                    _ => unreachable!(),
                };

                let mut first = true;
                for form in list {
                    if !first {
                        write!(f, " {} ", sep)?;
                    } else {
                        first = false;
                    }

                    if needs_parens(form) {
                        write!(f, "({})", form)?;
                    } else {
                        write!(f, "{}", form)?;
                    }
                }

                Ok(())
            }
        }
    }
}

impl Formula {
    pub fn take(&mut self) -> Self {
        mem::replace(self, false.into())
    }

    #[rustfmt::skip]
    pub fn is_atomic(&self) -> bool {
        match self {
            | Formula::Trivial(_)
            | Formula::Prop(_)
            | Formula::SubsetEq { .. }
            => true,

            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Bind(..)
            => false,
        }
    }

    pub fn is_trivial(&self) -> bool {
        matches!(self, Self::Trivial(..))
    }

    pub fn is_not(&self) -> bool {
        matches!(self, Formula::Not(_))
    }

    pub fn is_or(&self) -> bool {
        matches!(self, Formula::Or(_))
    }

    pub fn is_and(&self) -> bool {
        matches!(self, Formula::And(_))
    }

    pub fn is_bind(&self) -> bool {
        matches!(self, Formula::Bind(..))
    }

    pub fn is_subseteq(&self) -> bool {
        matches!(self, Formula::SubsetEq { .. })
    }

    pub fn is_forall(&self) -> bool {
        matches!(self, Formula::Bind(QuantifierKind::ForAll, ..))
    }

    pub fn is_exists(&self) -> bool {
        matches!(self, Formula::Bind(QuantifierKind::Exists, ..))
    }

    pub fn visit_with_pre<R>(&self, mut f: impl FnMut(&Self) -> Flow<R>) -> Flow<R> {
        AnonFormVisitor::pre(|x: &Self, _: &mut ()| f(x)).visit_formula(self)
    }

    pub fn visit_with_pre_mut<R>(&mut self, mut f: impl FnMut(&mut Self) -> Flow<R>) -> Flow<R> {
        AnonFormVisitorMut::pre(|x: &mut Self, _| f(x)).visit_formula(self)
    }

    pub fn visit_with_post<R>(&self, mut f: impl FnMut(&Self) -> Flow<R>) -> Flow<R> {
        AnonFormVisitor::post(|x: &Self, _| f(x)).visit_formula(self)
    }

    pub fn visit_with_post_mut<R>(&mut self, mut f: impl FnMut(&mut Self) -> Flow<R>) -> Flow<R> {
        AnonFormVisitorMut::post(|x: &mut Self, _| f(x)).visit_formula(self)
    }

    pub fn visit_with_stateful<S, R>(
        &self,
        initial_state: S,
        mut f: impl FnMut(&Self, &S) -> Flow<R, S>,
    ) -> Flow<R, ()> {
        let pre = |form: &Formula, stack: &mut Vec<S>| {
            let new_state: S = f(form, stack.last().unwrap())?;
            stack.push(new_state);
            Continue(())
        };

        let post = |_form: &Formula, stack: &mut Vec<S>| {
            stack.pop();
            Continue(())
        };

        AnonFormVisitor {
            pre,
            post,
            state: vec![initial_state],
        }
        .visit_formula(self)
    }

    pub fn visit_with_stateful_mut<S, R>(
        &mut self,
        initial_state: S,
        mut f: impl FnMut(&mut Self, &S) -> Flow<R, S>,
    ) -> Flow<R, ()> {
        let pre = |form: &mut Formula, stack: &mut Vec<S>| {
            let new_state: S = f(form, stack.last().unwrap())?;
            stack.push(new_state);
            Continue(())
        };

        let post = |_form: &mut Formula, stack: &mut Vec<S>| {
            stack.pop();
            Continue(())
        };

        AnonFormVisitorMut {
            pre,
            post,
            state: vec![initial_state],
        }
        .visit_formula(self)
    }

    /// True if any part of this formula mentions the given variable.
    ///
    /// This includes `Bind`.
    pub fn has_var(&self, var: Var) -> bool {
        matches!(HasVar(var).visit_formula(self), Break(FoundVar))
    }

    pub fn has_quantifiers(&self) -> bool {
        self.visit_with_pre(|form| {
            if form.is_bind() {
                Break(())
            } else {
                Continue(())
            }
        })
        .is_break()
    }

    /// Returns `true` if this contains an `And` immediately within another `And` or an `Or` within
    /// another `Or`.
    pub fn has_nested_connective(&self) -> bool {
        self.visit_with_pre(|form| match form {
            Formula::Or(l) if l.iter().any(Formula::is_or) => Break(()),
            Formula::And(l) if l.iter().any(Formula::is_and) => Break(()),
            _ => Continue(()),
        })
        .is_break()
    }
}

struct FoundVar;
struct HasVar(Var);

impl Visit for HasVar {
    type Break = FoundVar;

    fn visit_var(&mut self, var: &Var) -> Flow<Self::Break> {
        if *var == self.0 {
            Break(FoundVar)
        } else {
            Continue(())
        }
    }
}
