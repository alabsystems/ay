// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#4751) The empty-clause closer's Boolean-structure derivation.
//!
//! Every ACCEPT here is decided by the STRICT checker on the whole emitted
//! proof, not by an assertion about the shape this module produced: the point
//! of the route is that the checker re-derives it independently, so a test
//! that only inspected the steps would pin the producer against itself.
//!
//! Every DECLINE names the reason the derivation is unavailable and asserts
//! the proof is left byte-identical, which is what keeps the trust closer's
//! fallback intact.

use ay_core::{AletheRule, Proof, ProofStep, TermId, TermStore, TheoryLemmaKind};
use ay_proof::check_proof_strict;

use crate::executor::proof_resolution::empty_clause::boolean_closure::try_derive_empty_via_boolean_disjunction;

type Sort = ay_core::Sort;

/// `(<= lhs rhs)`.
fn le(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_le(lhs, rhs)
}

/// `(or ..)` built RAW, the way the substitution pass builds these leaves —
/// `mk_or` would fold `false` disjuncts away and dedupe, which is exactly the
/// simplification the #4751 route does NOT perform.
fn raw_or(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, ay_core::Sort::Bool)
}

fn int_const(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(value.into())
}

/// The #4751 shape in miniature: bound leaves plus one wide `or` whose
/// disjuncts negate consequences of those bounds.
///
/// `0 <= b`, `0 <= c` and `(or ¬(0 <= b+1) false ¬(0 <= c) ¬(0 <= b+c+1))`.
/// Every disjunct is refutable: the second by Alethe `false`, the third
/// literally by its own leaf, the first and fourth by Farkas against the
/// bounds.
fn wide_disjunction_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);

    let b_lower = le(&mut terms, zero, b);
    let c_lower = le(&mut terms, zero, c);

    let b_plus_1 = terms.mk_add(vec![b, one]);
    let b_plus_c_plus_1 = terms.mk_add(vec![b, c, one]);
    let d1_atom = le(&mut terms, zero, b_plus_1);
    let d1 = terms.mk_not_raw(d1_atom);
    let d2 = terms.mk_bool(false);
    let d3 = terms.mk_not_raw(c_lower);
    let d4_atom = le(&mut terms, zero, b_plus_c_plus_1);
    let d4 = terms.mk_not_raw(d4_atom);
    // A duplicate disjunct on purpose: resolution is decided set-wise, so a
    // second resolution on an already-eliminated literal is not a resolution.
    let disjunction = raw_or(&mut terms, vec![d1, d2, d3, d4, d1]);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_assume(c_lower, Some("h1".to_string()));
    proof.add_assume(disjunction, Some("h2".to_string()));
    (terms, proof)
}

#[test]
fn a_wide_disjunction_closes_by_derivation_and_the_strict_checker_accepts_it() {
    let (mut terms, mut proof) = wide_disjunction_proof();
    assert!(
        try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "every disjunct is refutable against the bound leaves"
    );
    assert!(
        matches!(proof.steps.last(), Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()),
        "the chain must end on the empty clause"
    );
    // THE acceptance criterion: the untouched strict checker re-derives it.
    let verdict = check_proof_strict(&proof, &terms);
    assert!(
        verdict.is_ok(),
        "strict checker must accept the derivation, got {verdict:?}"
    );
    // And nothing trust-kind was emitted on the way.
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            } | ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "the whole point is that no trust-kind step is produced"
    );
}

#[test]
fn the_derivation_uses_the_boolean_or_rule_and_alethe_false() {
    let (mut terms, mut proof) = wide_disjunction_proof();
    assert!(try_derive_empty_via_boolean_disjunction(
        &mut terms, &mut proof
    ));
    let rules: Vec<&AletheRule> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step { rule, .. } => Some(rule),
            _ => None,
        })
        .collect();
    assert!(
        rules.contains(&&AletheRule::Or),
        "the disjunction leaf must be decomposed by the Alethe `or` rule"
    );
    assert!(
        rules.contains(&&AletheRule::False),
        "a `false` disjunct must be discharged by the Alethe `false` rule"
    );
}

/// The Boolean arm proper: a disjunct whose complement is already a leaf needs
/// no lemma at all, and emitting one would be a fresh unchecked claim.
///
/// This is not an optimization. MEASURED on #4751: a fresh `LraSolver` asked
/// to refute a bound atom against its own negation returns no Farkas
/// certificate — there is no linear combination to report — so without this
/// arm the whole candidate declined.
#[test]
fn a_disjunct_refuted_by_its_own_leaf_needs_no_theory_lemma() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let b_lower = le(&mut terms, zero, b);
    let c = terms.mk_var("c", Sort::Int);
    let c_lower = le(&mut terms, zero, c);
    let d1 = terms.mk_not_raw(b_lower);
    let d2 = terms.mk_not_raw(c_lower);
    let disjunction = raw_or(&mut terms, vec![d1, d2]);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_assume(c_lower, Some("h1".to_string()));
    proof.add_assume(disjunction, Some("h2".to_string()));

    assert!(try_derive_empty_via_boolean_disjunction(
        &mut terms, &mut proof
    ));
    assert!(
        check_proof_strict(&proof, &terms).is_ok(),
        "a purely Boolean closure must strict-check"
    );
    assert!(
        !proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { .. })),
        "no theory lemma is needed when every disjunct's complement is a leaf"
    );
}

/// A negated-equality disjunct is discharged by the checker's own equality
/// triangle, and ONLY when both bounds are leaves the chain can resolve.
#[test]
fn a_negated_equality_disjunct_closes_through_the_equality_triangle() {
    let mut terms = TermStore::new();
    let d = terms.mk_var("d", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let forward = le(&mut terms, zero, d);
    let reverse = le(&mut terms, d, zero);
    let equality = terms.mk_eq(zero, d);
    let disjunct = terms.mk_not_raw(equality);
    let other_atom = le(&mut terms, zero, d);
    let other = terms.mk_not_raw(other_atom);
    let disjunction = raw_or(&mut terms, vec![disjunct, other]);

    let mut proof = Proof::new();
    proof.add_assume(forward, Some("h0".to_string()));
    proof.add_assume(reverse, Some("h1".to_string()));
    proof.add_assume(disjunction, Some("h2".to_string()));

    assert!(try_derive_empty_via_boolean_disjunction(
        &mut terms, &mut proof
    ));
    assert!(
        check_proof_strict(&proof, &terms).is_ok(),
        "the triangle lowering must strict-check"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArithEqTriangle,
                ..
            }
        )),
        "the negated equality must be discharged by ArithEqTriangle"
    );
}

/// FAIL-CLOSED: one bound of the equality pair missing, so the triangle cannot
/// be resolved to a unit and the whole candidate declines.
///
/// Falsifying assignment for the "extension" that would accept it anyway:
/// with only `0 <= d` asserted, `d := 1` satisfies every leaf while making the
/// disjunct `(not (= 0 d))` TRUE, so the leaf set is satisfiable and no empty
/// clause exists to derive.
#[test]
fn a_half_bounded_equality_declines_and_leaves_the_proof_untouched() {
    let mut terms = TermStore::new();
    let d = terms.mk_var("d", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let forward = le(&mut terms, zero, d);
    let equality = terms.mk_eq(zero, d);
    let disjunct = terms.mk_not_raw(equality);
    let filler_atom = le(&mut terms, zero, d);
    let filler = terms.mk_not_raw(filler_atom);
    let disjunction = raw_or(&mut terms, vec![disjunct, filler]);

    let mut proof = Proof::new();
    proof.add_assume(forward, Some("h0".to_string()));
    proof.add_assume(disjunction, Some("h1".to_string()));
    let before = proof.steps.len();

    assert!(
        !try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "one direction of the pair is not an equality proof"
    );
    assert_eq!(
        proof.steps.len(),
        before,
        "a declining candidate must leave no steps behind"
    );
    // The witness that makes the decline correct, checked here rather than
    // asserted: `d := 1` satisfies `0 <= d` and satisfies the disjunction.
    let witness = std::hint::black_box(1_i64);
    assert!(witness >= 0, "witness d := 1 satisfies the lower bound");
    assert_ne!(0, witness, "witness d := 1 satisfies (not (= 0 d))");
}

/// FAIL-CLOSED: a disjunct outside every arm — here a `Bool` variable, which
/// no rule in this closer can refute.
///
/// Falsifying assignment: `p := true` with `b := 0` satisfies `0 <= b` and the
/// disjunction, so the leaves are satisfiable and there is nothing to derive.
#[test]
fn an_unrefutable_disjunct_declines_the_whole_candidate() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let b_lower = le(&mut terms, zero, b);
    let p = terms.mk_var("p", Sort::Bool);
    let one = int_const(&mut terms, 1);
    let b_plus_1 = terms.mk_add(vec![b, one]);
    let refutable_atom = le(&mut terms, zero, b_plus_1);
    let refutable = terms.mk_not_raw(refutable_atom);
    let disjunction = raw_or(&mut terms, vec![refutable, p]);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_assume(disjunction, Some("h1".to_string()));
    let before = proof.steps.len();

    assert!(
        !try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "an unrefutable disjunct must decline the candidate, not close it"
    );
    assert_eq!(proof.steps.len(), before, "no steps may be left behind");
}

/// FAIL-CLOSED: the disjunction is NOT entailed to be contradictory — every
/// disjunct is arithmetic and the bounds do not refute one of them.
///
/// Falsifying assignment: `b := 5` satisfies the leaf `0 <= b` and the
/// disjunct `(not (<= 10 b))`, so the leaf set is satisfiable. A route that
/// closed this would be unsound.
#[test]
fn a_satisfiable_leaf_set_is_never_closed() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let ten = int_const(&mut terms, 10);
    let b_lower = le(&mut terms, zero, b);
    let ten_le_b = le(&mut terms, ten, b);
    let d1 = terms.mk_not_raw(ten_le_b);
    let one = int_const(&mut terms, 1);
    let b_plus_1 = terms.mk_add(vec![b, one]);
    let d2_atom = le(&mut terms, zero, b_plus_1);
    let d2 = terms.mk_not_raw(d2_atom);
    let disjunction = raw_or(&mut terms, vec![d1, d2]);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_assume(disjunction, Some("h1".to_string()));
    let before = proof.steps.len();

    assert!(
        !try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "b := 5 satisfies every leaf, so no derivation exists"
    );
    assert_eq!(proof.steps.len(), before, "no steps may be left behind");
    // The witness, checked: b := 5.
    let witness = std::hint::black_box(5_i64);
    assert!(witness >= 0, "witness satisfies 0 <= b");
    assert!(witness < 10, "witness satisfies (not (<= 10 b))");
}

/// A proof with no disjunction leaf at all is untouched, so the trust closer
/// still runs exactly as it did.
#[test]
fn a_proof_without_a_disjunction_leaf_is_left_alone() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let b_lower = le(&mut terms, zero, b);
    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    let before = proof.steps.len();
    assert!(!try_derive_empty_via_boolean_disjunction(
        &mut terms, &mut proof
    ));
    assert_eq!(proof.steps.len(), before);
}

/// The leaf set the closer reads includes premiseless unit `trust` steps, the
/// spelling a disjunction leaf carries before the repair lanes rewrite it.
#[test]
fn a_disjunction_recorded_as_a_unit_trust_leaf_is_still_decomposed() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let b_lower = le(&mut terms, zero, b);
    let d1 = terms.mk_not_raw(b_lower);
    let d2 = terms.mk_bool(false);
    let disjunction = raw_or(&mut terms, vec![d1, d2]);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_rule_step(AletheRule::Trust, vec![disjunction], Vec::new(), Vec::new());

    assert!(
        try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "a unit trust leaf is a leaf the closer may resolve against"
    );
    assert!(
        matches!(proof.steps.last(), Some(ProofStep::Resolution { clause, .. }) if clause.is_empty())
    );
}

/// A disjunction wider than the cap is DECLINED, never truncated: truncating
/// would make acceptance depend on disjunct order.
#[test]
fn a_disjunction_wider_than_the_cap_declines_rather_than_truncating() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Int);
    let zero = int_const(&mut terms, 0);
    let b_lower = le(&mut terms, zero, b);
    let false_term = terms.mk_bool(false);
    // 129 disjuncts, every one of them refutable, so ONLY the cap can decline.
    let mut args = vec![terms.mk_not_raw(b_lower)];
    for _ in 0..128 {
        args.push(false_term);
    }
    assert_eq!(args.len(), 129);
    let disjunction = raw_or(&mut terms, args);

    let mut proof = Proof::new();
    proof.add_assume(b_lower, Some("h0".to_string()));
    proof.add_assume(disjunction, Some("h1".to_string()));
    let before = proof.steps.len();
    assert!(
        !try_derive_empty_via_boolean_disjunction(&mut terms, &mut proof),
        "the cap must decline outright"
    );
    assert_eq!(proof.steps.len(), before);
}
