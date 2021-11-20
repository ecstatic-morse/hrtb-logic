use insta::assert_display_snapshot;

use crate::{short::*, Formula, Var};

const A: Var = Var(0);
const B: Var = Var(1);
const C: Var = Var(2);
const D: Var = Var(3);
const E: Var = Var(4);

const X: Var = Var(23);
const Y: Var = Var(24);
const Z: Var = Var(25);

const P: Formula = prop("P");
const Q: Formula = prop("Q");
const R: Formula = prop("R");
const S: Formula = prop("S");
const T: Formula = prop("T");
const U: Formula = prop("U");
const V: Formula = prop("V");

#[test]
fn nnf() {
    let nnf = Formula::negation_normal_form;

    assert_eq!(nnf(!!Q), Q);
    assert_eq!(nnf(!and(P, Q)), or(!P, !Q));
    assert_eq!(nnf(!or(P, Q)), and(!P, !Q));
    assert_eq!(nnf(!forall(A, P)), exists(A, !P));

    assert_display_snapshot!(nnf(!forall(A, or(P, and(Q, R)))), @"∃'a.(¬P ∧ (¬Q ∨ ¬R))");
}

#[test]
fn dnf() {
    let dnf = Formula::disjunctive_normal_form;

    assert_display_snapshot!(dnf(and(or(P, Q), or(R, S))), @"(P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)");
    assert_display_snapshot!(dnf(and(or(and(P, Q), R), S)), @"(P ∧ Q ∧ S) ∨ (R ∧ S)");
    assert_display_snapshot!(dnf(and_([or(P, Q), or(R, S), or_([T, U, V])])));
}

#[test]
fn qe_atomless() {
    let _ = Y;

    let dnf = Formula::disjunctive_normal_form;
    let qe = |mut f: Formula| {
        f.eliminate_all_quantifiers();
        f.simplify();
        f.make_negation_normal_form();
        f
    };

    // http://smallcultfollowing.com/babysteps/blog/2019/01/21/hereditary-harrop-region-constraints/
    assert_display_snapshot!(qe(forall(B, subeq(B, A))), @"False");
    assert_display_snapshot!(qe(forall(A, forall(B, subeq(B, A)))), @"False");
    assert_display_snapshot!(qe(exists(B, and(subeq(A, B), subeq(B, C)))), @"'a ⊆ 'c");
    assert_display_snapshot!(qe(forall(B, subeq(A, B))), @"'a ⊆ 'static");

    assert_display_snapshot!(
        qe(exists(A, and_([subeq(B, A), subeq(C, A), subeq(A, D), subeq(A, E)]))),
        @"('b ⊆ 'd) ∧ ('b ⊆ 'e) ∧ ('c ⊆ 'd) ∧ ('c ⊆ 'e)"
    );

    // https://gist.github.com/nikomatsakis/8bfda6c1119727e13ec6e98f33d2b696#future-directions-let-the-trait-solver-solve-higher-ranked-things
    assert_display_snapshot!(
        qe(forall(A, implies(subeq(A, B), subeq(A, C)))),
        @"'b ⊆ 'c"
    );
    assert_display_snapshot!(
        qe(forall(A, implies(and(subeq(A, B), subeq(A, C)), subeq(A, D)))),
        @"('b ⊆ 'd) ∨ ('c ⊆ 'd)"
    );
    assert_display_snapshot!(
        qe(forall(A, implies(or(subeq(A, B), subeq(A, C)), subeq(A, D)))),
        @"('b ⊆ 'd) ∧ ('c ⊆ 'd)"
    );
    assert_display_snapshot!(
        dnf(qe(forall(A, iff(or(subeq(A, B), subeq(A, C)), subeq(A, D))))),
        @"(('d ⊆ 'b) ∧ ('b ⊆ 'd) ∧ ('c ⊆ 'd)) ∨ (('d ⊆ 'c) ∧ ('b ⊆ 'd) ∧ ('c ⊆ 'd))"
    );

    // https://rust-lang.zulipchat.com/#narrow/stream/186049-t-compiler.2Fwg-polonius/topic/Quantifier.20elimination.20for.20HRTBs/near/262167372
    assert_display_snapshot!(
        qe(exists(Z, forall(X, iff(subeq(X, Z), and(subeq(X, A), subeq(X, B)))))),
        @"(('a ⊆ 'b)) ∨ (('b ⊆ 'a))"
    );

    // The transitive property: ('a ⊆ 'b) ∧ ('b ⊆ 'c) → 'a ⊆ 'c
    assert_display_snapshot!(
        qe(forall(A, forall(C, forall(B, implies(and(subeq(A, B), subeq(B, C)), subeq(A, C)))))),
        @"True"
    );

    // A property of atomless boolean algebras that is not true for finite sets: We can always find
    // an element that is ordered between any other two (distinct) elements.
    //
    // ∀a,c.('a ⊂ 'c) → ∃b.(('a ⊂ 'b) ∧ ('b ⊂ 'c))
    assert_display_snapshot!(
        qe(forall(A, forall(C, implies(subne(A, C), exists(B, and(subne(A, B), subne(B, C))))))),
        @"True"
    );
}

#[test]
fn is_dnf() {
    let is_dnf = |f: Formula| f.is_disjunctive_normal_form();
    assert!(!is_dnf(and(or(P, Q), or(R, S))));
    assert!(is_dnf(or(and(P, Q), and(R, S))));
}

#[test]
fn has_nested_connective() {
    let has_nested = |f: Formula| f.has_nested_connective();

    assert!(!has_nested(and(or(P, Q), or(R, S))));
    assert!(has_nested(or(and(P, Q), or(R, S))));
}

mod prop {
    use super::*;
    use proptest::prelude::*;

    const PROPS: &'static str = "PQRSTUVWYZ";

    impl Arbitrary for Formula {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): Self::Parameters) -> Self::Strategy {
            let mut props: Vec<_> = (0..PROPS.len())
                .map(|i| PROPS.get(i..=i).unwrap())
                .map(prop)
                .collect();

            props.push(true.into());
            props.push(false.into());

            // FIXME: Ideally, the predicates in our test cases would be unique, but `LazyJust`
            // must be pure. `no_shrink` seems to work okay as long as the sample space is large.
            let leaf = proptest::sample::select(props).no_shrink();

            leaf.prop_recursive(6, 64, 10, |inner| {
                prop_oneof![
                    inner.clone().prop_map(|form| not(form)),
                    proptest::collection::vec(inner.clone(), 2..6).prop_map(Formula::Or),
                    proptest::collection::vec(inner.clone(), 2..6).prop_map(Formula::And),
                ]
            })
            .boxed()
        }
    }

    proptest! {
        #[test]
        fn nnf(form in any::<Formula>()) {
            let nnf = form.negation_normal_form();
            prop_assert!(nnf.is_negation_normal_form());
        }

        #[test]
        fn dnf(form in any::<Formula>()) {
            let dnf = form.disjunctive_normal_form();
            prop_assert!(dnf.is_disjunctive_normal_form());
        }

        #[test]
        fn trivial(mut form in any::<Formula>()) {
            form.simplify_all_trivial_connectives();
            prop_assert!(!form.has_trivial_connectives());
        }
    }
}
