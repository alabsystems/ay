// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL negatives for the congruence-explanation lowering.
//!
//! Each names a CONCRETE falsifying assignment and checks it in-test with the
//! independent evaluator in `congruence_derivation_sweep_tests`, or — where
//! the clause is VALID but out of the lowering's scope — says exactly which
//! rule is missing and why declining is the fail-closed answer.
//!
//! Split out of `congruence_derivation_tests` so each file stays inside the
//! repository's per-file line ceiling.

use super::super::plan_euf_congruence_derivation;
use super::{eq, fun, neq, uninterpreted, var};
use ay_core::{Sort, TermStore};

#[test]
fn declines_a_chain_with_a_broken_link() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let d = var(&mut terms, "d");
    // `a = b`, `c = d` |/= `a = d`.
    let clause = vec![
        neq(&mut terms, a, b),
        neq(&mut terms, c, d),
        eq(&mut terms, a, d),
    ];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
    let witness = crate::congruence_derivation::sweep_tests::falsifies(&terms, &clause)
        .expect("the clause is invalid, so a countermodel must exist");
    assert_eq!(
        witness.len(),
        4,
        "a := 0, b := 0, c := 1, d := 1 falsifies every literal: {witness:?}"
    );
}

#[test]
fn declines_a_congruence_over_different_function_symbols() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let gb = fun(&mut terms, "g", vec![b], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, fa, gb)];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
    assert!(
        crate::congruence_derivation::sweep_tests::falsifies(&terms, &clause).is_some(),
        "f(a) = g(b) does not follow from a = b: f := identity, g := constant"
    );
}

#[test]
fn declines_a_congruence_over_different_arities() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fab = fun(&mut terms, "f", vec![a, b], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, fa, fab)];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
    assert!(crate::congruence_derivation::sweep_tests::falsifies(&terms, &clause).is_some());
}

#[test]
fn declines_a_smuggled_non_equality_literal() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), not_p, eq(&mut terms, fa, fb)];
    assert!(
        plan_euf_congruence_derivation(&mut terms, &clause).is_none(),
        "a non-equality literal is out of scope even though the clause is VALID"
    );
}

#[test]
fn declines_a_positive_equality_read_as_a_hypothesis() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    // `(cl (= a b) (= (f a) (f b)))` is FALSE under a := 0, b := 1,
    // f(0) := 2, f(1) := 3 — reading the positive equality as a hypothesis
    // would derive it.
    let clause = vec![eq(&mut terms, a, b), eq(&mut terms, fa, fb)];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
    assert!(crate::congruence_derivation::sweep_tests::falsifies(&terms, &clause).is_some());
}

#[test]
fn declines_a_clause_with_two_positive_equalities() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let clause = vec![
        neq(&mut terms, a, b),
        eq(&mut terms, b, c),
        eq(&mut terms, a, c),
    ];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
}

#[test]
fn declines_a_clause_with_no_hypothesis() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let clause = vec![eq(&mut terms, a, b)];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
}

#[test]
fn declines_a_repeated_literal() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    let hypothesis = neq(&mut terms, a, b);
    let clause = vec![hypothesis, hypothesis, eq(&mut terms, fa, fb)];
    assert!(
        plan_euf_congruence_derivation(&mut terms, &clause).is_none(),
        "a multiset the reordering step could not restore is declined"
    );
}

#[test]
fn declines_a_congruence_under_a_negation_former() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    // VALID (`not` is a function), but `eq_congruent` requires two
    // APPLICATIONS, so this lowering has no rule for it and declines.
    let clause = vec![neq(&mut terms, p, q), eq(&mut terms, not_p, not_q)];
    assert!(plan_euf_congruence_derivation(&mut terms, &clause).is_none());
}
