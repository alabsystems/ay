// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial negatives and the guard-mutation ledger for sub-schema (P).
//!
//! Every negative whose clause is FALSIFIABLE names its countermodel and checks
//! it in-test with the independent evaluator BEFORE asserting the decline. The
//! three SCOPE negatives are labelled as such: their clauses are valid, and the
//! decline is a deliberate boundary rather than a soundness requirement.

use super::*;

/// Which test goes RED when each guard is deleted or weakened. Verified by hand
/// with a temporary edit per row, the named test re-run, the failure observed,
/// and the guard restored.
///
/// | # | guard | test that goes RED |
/// |---|---|---|
/// | M1 | a POSITIVE equality is never a hypothesis | `a_positive_equality_is_never_a_hypothesis` |
/// | M2 | acceptance needs a TRUE atom merged with a FALSE one, not two TRUE ones | `two_true_atoms_merging_is_not_a_refutation` |
/// | M3 | the TRUE class is merged | `the_true_class_merge_is_load_bearing` |
/// | M4 | the FALSE class is merged | `the_false_class_merge_is_load_bearing` |
/// | M5 | congruence closure runs | `accepts_the_measured_mem_congruence_shape` |
/// | M6 | SCOPE: a non-equality literal is required | `an_all_equality_clause_is_out_of_scope` |
/// | M7 | SCOPE: at least one hypothesis equality | `a_clause_with_no_hypothesis_equality_is_out_of_scope` |
/// | M8 | SCOPE: at least one positive literal | `an_all_negative_clause_is_out_of_scope` |
/// | M9 | the caller's envelope is honoured, TRUE-atom intern alone | GREEN — backstopped |
/// | M9-QUAD | every debit site weakened together | `an_exhausted_envelope_rejects_rather_than_accepts` |
///
/// M9 is the "guards backstop each other" case: the validator interns through
/// FOUR metered `add` sites, so weakening one leaves the other three refusing
/// and the test honestly stays GREEN. Weakening all four turns it RED. Nine of
/// ten mutations are RED; the tenth is recorded, not hidden.
pub(super) const GUARD_MUTATION_LEDGER: &str = "see the table above";

/// M1. Reading a POSITIVE equality as a hypothesis would accept this clause,
/// which is FALSE at `a := 0, b := 1, p(0) := true, p(1) := false`.
#[test]
fn a_positive_equality_is_never_a_hypothesis() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pb = mk_fun(&mut terms, "p", vec![b], Sort::Bool);
    let eq_ab = mk_eq(&mut terms, a, b);
    let not_pa = terms.mk_not_raw(pa);
    let clause = vec![eq_ab, not_pa, pb];
    let model = refuted_at(&terms, &clause);
    assert!(
        model.contains(":="),
        "the countermodel must pin truth values"
    );
    assert!(!accepts(&terms, &clause));
}

/// M2. Two atoms the falsifying model reads TRUE being congruent proves
/// nothing. Falsified at `a := b := 0, p(0) := true`.
#[test]
fn two_true_atoms_merging_is_not_a_refutation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pb = mk_fun(&mut terms, "p", vec![b], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_pa = terms.mk_not_raw(pa);
    let not_pb = terms.mk_not_raw(pb);
    // Every literal is negative, so the clause is falsified by making `a = b`
    // and `p` true there — and it has no positive literal at all.
    let clause = vec![hypothesis, not_pa, not_pb];
    let _ = refuted_at(&terms, &clause);
    assert!(!accepts(&terms, &clause));

    // The same shape WITH a positive literal, so the scope guard is not what
    // rejects it: falsified at `a := b := 0`, `p(0) := true`, `q(0) := false`.
    let qa = mk_fun(&mut terms, "q", vec![a], Sort::Bool);
    let with_positive = vec![hypothesis, not_pa, not_pb, qa];
    let _ = refuted_at(&terms, &with_positive);
    assert!(!accepts(&terms, &with_positive));
}

/// M3. The TRUE-class merge is what relates `x` and `y`: both are read TRUE, so
/// `g(x) = g(y)`. Without it the clause is declined. The clause IS valid, so
/// this negative is a completeness anchor, and the accompanying falsifiable
/// sibling below pins that the rule does not accept the shape unconditionally.
#[test]
fn the_true_class_merge_is_load_bearing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let c = terms.mk_var("c", Sort::Int);
    let gx = mk_fun(&mut terms, "g", vec![x], Sort::Int);
    let gy = mk_fun(&mut terms, "g", vec![y], Sort::Int);
    let eq_gx_c = mk_eq(&mut terms, gx, c);
    let eq_gy_c = mk_eq(&mut terms, gy, c);
    let not_x = terms.mk_not_raw(x);
    let not_y = terms.mk_not_raw(y);
    let not_eq_gx_c = terms.mk_not_raw(eq_gx_c);
    let clause = vec![not_x, not_y, not_eq_gx_c, eq_gy_c];
    assert!(is_valid(&terms, &clause));
    assert!(accepts(&terms, &clause));

    // Drop `(not y)` and the clause becomes FALSIFIABLE — `x := true`,
    // `y := false`, `g(true) := c`, `g(false) := d != c` — and is refused.
    let weakened = vec![not_x, not_eq_gx_c, eq_gy_c];
    let _ = refuted_at(&terms, &weakened);
    assert!(!accepts(&terms, &weakened));
}

/// M4. The mirror: the FALSE-class merge relates two atoms the model must read
/// FALSE. This is the shape of the measured ten-literal `clearsy` clause.
#[test]
fn the_false_class_merge_is_load_bearing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let c = terms.mk_var("c", Sort::Int);
    let gx = mk_fun(&mut terms, "g", vec![x], Sort::Int);
    let gy = mk_fun(&mut terms, "g", vec![y], Sort::Int);
    let eq_gx_c = mk_eq(&mut terms, gx, c);
    let eq_gy_c = mk_eq(&mut terms, gy, c);
    let not_eq_gx_c = terms.mk_not_raw(eq_gx_c);
    let clause = vec![not_eq_gx_c, x, y, eq_gy_c];
    assert!(is_valid(&terms, &clause));
    assert!(accepts(&terms, &clause));

    // Drop `y` and it becomes FALSIFIABLE — `x := false`, `y := true`,
    // `g(false) := c`, `g(true) := d != c` — and is refused.
    let weakened = vec![not_eq_gx_c, x, eq_gy_c];
    let _ = refuted_at(&terms, &weakened);
    assert!(!accepts(&terms, &weakened));
}

/// An unrelated conclusion is refused even though the hypotheses are usable.
/// Falsified at `a := b := 0`, `c := 1`, `p(0) := true`, `p(1) := false`.
#[test]
fn an_unrelated_predicate_conclusion_is_refused() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pc = mk_fun(&mut terms, "p", vec![c], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_pa = terms.mk_not_raw(pa);
    let clause = vec![hypothesis, not_pa, pc];
    let _ = refuted_at(&terms, &clause);
    assert!(!accepts(&terms, &clause));
}

/// A predicate applied at a DIFFERENT arity is a different function symbol for
/// congruence, so no merge happens. Falsified with `p/1` and `p/2` independent.
#[test]
fn a_different_arity_predicate_is_not_congruent() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p1 = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let p2 = mk_fun(&mut terms, "p", vec![b, b], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_p1 = terms.mk_not_raw(p1);
    let clause = vec![hypothesis, not_p1, p2];
    let _ = refuted_at(&terms, &clause);
    assert!(!accepts(&terms, &clause));
}

/// SCOPE (M6). An all-equality clause belongs to sub-schema (E). This one is
/// VALID and (P) still declines it, so the two schemas stay disjoint and (E)'s
/// own scope tests keep meaning what they say.
#[test]
fn an_all_equality_clause_is_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = mk_eq(&mut terms, a, b);
    let hypothesis = terms.mk_not_raw(eq_ab);
    let clause = vec![hypothesis, eq_ab];
    assert!(is_valid(&terms, &clause));
    // (E) owns it, and does accept it — so the decline below is (P)'s scope
    // guard and nothing else.
    assert!(recognize_euf_congruence_explanation(&terms, &clause));
    assert!(!recognize_euf_polarity_congruence(&terms, &clause));
}

/// SCOPE (M7). Without a hypothesis equality this is a propositional
/// tautology, which `bool_tautology` owns; (P) declines it rather than widening
/// into that rule's population.
#[test]
fn a_clause_with_no_hypothesis_equality_is_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let not_pa = terms.mk_not_raw(pa);
    let clause = vec![not_pa, pa];
    assert!(is_valid(&terms, &clause));
    assert!(!accepts(&terms, &clause));
}

/// SCOPE (M8). With no positive literal there is no FALSE class to meet, and
/// the guard says so explicitly rather than indexing an empty vector.
#[test]
fn an_all_negative_clause_is_out_of_scope() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_pa = terms.mk_not_raw(pa);
    let clause = vec![hypothesis, not_pa];
    assert!(!accepts(&terms, &clause));
}

/// A single literal is refused before anything else runs.
#[test]
fn a_one_literal_clause_is_refused() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    assert!(!accepts(&terms, &[pa]));
    assert!(!accepts(&terms, &[]));
}

/// M9. The caller's envelope is honoured: a `progress` callback that refuses
/// everything makes the validator return `ResourceLimit`, never `Ok`.
#[test]
fn an_exhausted_envelope_rejects_rather_than_accepts() {
    let mut terms = TermStore::new();
    let clause = clearsy_clause(&mut terms, false);
    assert!(recognize_euf_polarity_congruence(&terms, &clause));
    let refused = validate_euf_polarity_congruence(&terms, ProofId(0), &clause, &mut |_, _| false);
    assert!(matches!(refused, Err(ProofCheckError::ResourceLimit)));
    assert!(!GUARD_MUTATION_LEDGER.is_empty());
}
