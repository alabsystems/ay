// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for proof term rewriting (`proof_rewrite.rs`).

use super::*;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{AletheRule, Proof, ProofStep, Sort, TermStore};
use num_bigint::BigInt;

/// Verify that `rewrite_proof_terms` substitutes canonical `(<= b a)` with
/// surface `(>= a b)` in all Assume and Step clause positions.
#[test]
fn test_rewrite_proof_terms_canonicalized_leq_to_geq() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    // Canonical form: (<= b a) — AY rewrites >= to <= with swapped args
    let leq_b_a = terms.mk_app(Symbol::named("<="), vec![b, a], Sort::Bool);
    // Surface form: (>= a b) — what the user wrote
    let geq_a_b = terms.mk_app(Symbol::named(">="), vec![a, b], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(leq_b_a, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![leq_b_a], // clause containing canonical term
        vec![],
        vec![],
    );

    let mut rewrites = HashMap::default();
    rewrites.insert(leq_b_a, geq_a_b);

    Executor::rewrite_proof_terms(&mut terms, &mut proof, &rewrites);

    // Assume step should now reference the surface form
    assert!(
        matches!(&proof.steps[0], ProofStep::Assume(t) if *t == geq_a_b),
        "Assume not rewritten to surface form"
    );
    // Step clause should also be rewritten
    let ProofStep::Step { clause, .. } = &proof.steps[1] else {
        unreachable!("step 1 should be a Step variant")
    };
    assert_eq!(clause[0], geq_a_b, "Step clause not rewritten");
}

/// Verify that auxiliary assumptions (containing `_mod_`/`_div_` variables)
/// that don't match problem assertions are demoted to Trust steps.
#[test]
fn test_demote_auxiliary_non_problem_assumptions_to_trust() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let aux = terms.mk_var("_mod_q_0", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    // Auxiliary assertion: (= _mod_q_0 0)
    let aux_eq = terms.mk_app(Symbol::named("="), vec![aux, zero], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(p, None); // step 0: problem assertion
    proof.add_assume(aux_eq, None); // step 1: auxiliary (not in problem)

    let problem_assertions = vec![p]; // only p is a real assertion
    let mut aux_assume_steps = HashSet::default();
    aux_assume_steps.insert(1u32); // step 1 is auxiliary

    Executor::demote_auxiliary_non_problem_assumptions(
        &mut proof,
        &problem_assertions,
        &aux_assume_steps,
    );

    // Step 0 should remain an Assume (it's a problem assertion)
    assert!(
        matches!(&proof.steps[0], ProofStep::Assume(t) if *t == p),
        "problem assumption should be preserved"
    );
    // Step 1 should be demoted to Trust
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        ..
    } = &proof.steps[1]
    else {
        unreachable!("step 1 should be a Trust step after demotion")
    };
    assert_eq!(
        clause,
        &[aux_eq],
        "Trust clause should contain the aux term"
    );
}

/// Verify that non-problem assumptions are demoted to Trust even when they use
/// only user-declared symbols. This covers normalized ring-arithmetic
/// equalities where the proof term no longer matches the original assertion
/// surface syntax (for example `(* c1 16)` vs `(* 16 c1)`).
#[test]
fn test_demote_non_problem_assumptions_to_trust() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let c1 = terms.mk_var("c1", Sort::Int);
    let s1 = terms.mk_var("s1", Sort::Int);
    let sixteen = terms.mk_int(BigInt::from(16));

    let original_mul = terms.mk_app(Symbol::named("*"), vec![sixteen, c1], Sort::Int);
    let normalized_mul = terms.mk_app(Symbol::named("*"), vec![c1, sixteen], Sort::Int);
    let sum_xy = terms.mk_app(Symbol::named("+"), vec![x, y], Sort::Int);
    let original_rhs = terms.mk_app(Symbol::named("+"), vec![original_mul, s1], Sort::Int);
    let normalized_rhs = terms.mk_app(Symbol::named("+"), vec![normalized_mul, s1], Sort::Int);
    let original_assertion =
        terms.mk_app(Symbol::named("="), vec![sum_xy, original_rhs], Sort::Bool);
    let normalized_assume =
        terms.mk_app(Symbol::named("="), vec![sum_xy, normalized_rhs], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(original_assertion, None);
    proof.add_assume(normalized_assume, None);

    Executor::demote_non_problem_assumptions(&mut proof, &[original_assertion]);

    assert!(
        matches!(&proof.steps[0], ProofStep::Assume(t) if *t == original_assertion),
        "problem assumption should remain an assume step"
    );
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        ..
    } = &proof.steps[1]
    else {
        unreachable!("non-problem assumption should be demoted to trust")
    };
    assert_eq!(
        clause,
        &[normalized_assume],
        "Trust clause should preserve the rewritten assumption term"
    );
}

/// Verify that `term_contains_aux_mod_div_var` detects `_mod_`/`_div_`
/// variables nested inside application terms, and returns false for
/// terms without such variables.
#[test]
fn test_term_contains_aux_mod_div_var_detection() {
    let mut terms = TermStore::new();

    // Term with no aux variables: (+ x 1)
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let plus_x_1 = terms.mk_app(Symbol::named("+"), vec![x, one], Sort::Int);
    assert!(
        !Executor::term_contains_aux_mod_div_var(&terms, plus_x_1),
        "plain term should not contain aux vars"
    );

    // Term with aux variable nested: (+ x _div_q_0)
    let div_q = terms.mk_var("_div_q_0", Sort::Int);
    let plus_x_divq = terms.mk_app(Symbol::named("+"), vec![x, div_q], Sort::Int);
    assert!(
        Executor::term_contains_aux_mod_div_var(&terms, plus_x_divq),
        "term containing _div_q_0 should be detected"
    );

    // Deeper nesting: (* 5 (+ _mod_r_1 y))
    let mod_r = terms.mk_var("_mod_r_1", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let inner = terms.mk_app(Symbol::named("+"), vec![mod_r, y], Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let outer = terms.mk_app(Symbol::named("*"), vec![five, inner], Sort::Int);
    assert!(
        Executor::term_contains_aux_mod_div_var(&terms, outer),
        "deeply nested _mod_r_1 should be detected"
    );
}

/// Verify that `infer_auxiliary_division_rewrites` correctly parses
/// `(= x (+ (* 3 _mod_q_0) _mod_r_0))` and produces rewrites
/// mapping `_mod_q_0 → (div x 3)` and `_mod_r_0 → (mod x 3)`.
#[test]
fn test_infer_division_rewrites_scaled_quotient() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let q = terms.mk_var("_mod_q_0", Sort::Int);
    let r = terms.mk_var("_mod_r_0", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));

    // Build: (= x (+ (* 3 _mod_q_0) _mod_r_0))
    let scaled_q = terms.mk_app(Symbol::named("*"), vec![three, q], Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), vec![scaled_q, r], Sort::Int);
    let constraint = terms.mk_app(Symbol::named("="), vec![x, sum], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(constraint, None);

    let mut rewrites = HashMap::default();
    Executor::infer_auxiliary_division_rewrites(&mut terms, &proof, &mut rewrites);

    assert_eq!(
        rewrites.len(),
        2,
        "expected 2 rewrites (quotient + remainder)"
    );
    // _mod_q_0 → (div x 3)
    let div_term = terms.mk_intdiv(x, three);
    assert_eq!(
        rewrites.get(&q),
        Some(&div_term),
        "quotient var should map to (div x 3)"
    );
    // _mod_r_0 → (mod x 3)
    let mod_term = terms.mk_mod(x, three);
    assert_eq!(
        rewrites.get(&r),
        Some(&mod_term),
        "remainder var should map to (mod x 3)"
    );
}

/// Verify that a bare quotient variable (divisor=1) is correctly parsed:
/// `(= x (+ _div_q_0 _div_r_0))` → `_div_q_0 → (div x 1)`, `_div_r_0 → (mod x 1)`.
#[test]
fn test_infer_division_rewrites_bare_quotient() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let q = terms.mk_var("_div_q_0", Sort::Int);
    let r = terms.mk_var("_div_r_0", Sort::Int);

    // Build: (= x (+ _div_q_0 _div_r_0))
    let sum = terms.mk_app(Symbol::named("+"), vec![q, r], Sort::Int);
    let constraint = terms.mk_app(Symbol::named("="), vec![x, sum], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(constraint, None);

    let mut rewrites = HashMap::default();
    Executor::infer_auxiliary_division_rewrites(&mut terms, &proof, &mut rewrites);

    assert_eq!(rewrites.len(), 2, "expected 2 rewrites for bare quotient");
    let one = terms.mk_int(BigInt::from(1));
    let div_term = terms.mk_intdiv(x, one);
    assert_eq!(
        rewrites.get(&q),
        Some(&div_term),
        "bare quotient should map to (div x 1)"
    );
}

/// Verify that reversed operand order is handled:
/// `(= (+ _mod_r_0 (* 5 _mod_q_0)) x)` — equality and addend order swapped.
#[test]
fn test_infer_division_rewrites_reversed_operands() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let q = terms.mk_var("_mod_q_0", Sort::Int);
    let r = terms.mk_var("_mod_r_0", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    // Build: (= (+ _mod_r_0 (* 5 _mod_q_0)) x)  — both equality and addend reversed
    let scaled_q = terms.mk_app(Symbol::named("*"), vec![five, q], Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), vec![r, scaled_q], Sort::Int);
    let constraint = terms.mk_app(Symbol::named("="), vec![sum, x], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(constraint, None);

    let mut rewrites = HashMap::default();
    Executor::infer_auxiliary_division_rewrites(&mut terms, &proof, &mut rewrites);

    assert_eq!(
        rewrites.len(),
        2,
        "reversed operands should still produce 2 rewrites"
    );
    let div_term = terms.mk_intdiv(x, five);
    assert_eq!(
        rewrites.get(&q),
        Some(&div_term),
        "quotient should map to (div x 5) with reversed operands"
    );
}

/// Verify that non-division assumptions produce no rewrites.
#[test]
fn test_infer_division_rewrites_no_match() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    // Build: (= x y) — no aux vars, should produce no rewrites
    let eq = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(eq, None);

    let mut rewrites = HashMap::default();
    Executor::infer_auxiliary_division_rewrites(&mut terms, &proof, &mut rewrites);

    assert!(
        rewrites.is_empty(),
        "non-division constraint should produce no rewrites"
    );
}

/// Verify that `rewrite_term` descends through `Not` wrappers.
#[test]
fn test_rewrite_term_through_not() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    let leq_b_a = terms.mk_app(Symbol::named("<="), vec![b, a], Sort::Bool);
    let geq_a_b = terms.mk_app(Symbol::named(">="), vec![a, b], Sort::Bool);
    let not_leq = terms.mk_not(leq_b_a);

    let mut rewrites = HashMap::default();
    rewrites.insert(leq_b_a, geq_a_b);
    let mut cache = HashMap::default();

    let result = Executor::rewrite_term(&mut terms, not_leq, &rewrites, &mut cache);
    // Result should be (not (>= a b))
    let expected = terms.mk_not(geq_a_b);
    assert_eq!(
        result, expected,
        "rewrite_term should descend through Not wrappers"
    );
}
