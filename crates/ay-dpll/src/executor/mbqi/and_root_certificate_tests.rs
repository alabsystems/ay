// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantified SAT certificates over an asserted `(and …)` root.
//!
//! LOIS (SMT-LIB LRA) asserts its queries as one root
//! `(and (forall ((g Real)) φ) ground₁ ground₂ …)`. The constant-
//! interpretation and finite-table certificates partition the CONJUNCT VIEW
//! of such a root (`flatten_quantified_and_roots`), discharge every leaf
//! under one shared interpretation, and still bind their witness to the
//! AUTHORED root vector the publication gate re-authenticates.

use super::*;
use ay_frontend::parse;

fn executor_for(input: &str) -> Executor {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    exec
}

/// ACCEPTING DIRECTION (LOIS incremental0 check-sat 29, verbatim shape): the
/// all-zero interpretation satisfies the universal and all three ground
/// leaves. The witness must be pending for the authored one-root vector —
/// not for the flattened leaves, which no gate ever sees as roots.
#[test]
fn certifies_a_quantified_and_root_and_binds_the_authored_root() {
    let mut exec = executor_for(
        "(set-logic LRA)
         (declare-const b Real)
         (declare-const a Real)
         (declare-const c Real)
         (declare-const h Real)
         (assert (and (forall ((g Real)) (or (or (or (> b g) (> a g)) (> c g)) (>= g h)))
                      (and (and (>= h b) (>= h a)) (>= h c))))",
    );
    let assertions = exec.ctx.assertions.clone();
    assert_eq!(
        assertions.len(),
        1,
        "the fixture must reach the certificate as ONE and-root"
    );
    assert!(
        exec.try_const_interp_sat_certificate(&assertions, LogicCategory::QfLra)
            .is_some(),
        "every leaf of the and-root holds under the all-zero interpretation"
    );
    let leaves = flatten_quantified_and_roots(&exec.ctx.terms, &assertions);
    assert_eq!(leaves.len(), 4);
    let state = exec
        .const_interp_cert_witness_state
        .as_ref()
        .expect("a grant parks its witness");
    assert!(
        state.is_pending_current_for(&exec, &assertions),
        "the witness is bound to the authored root vector"
    );
    assert!(
        !state.is_pending_current_for(&exec, &leaves),
        "the conjunct view must never become the bound identity"
    );
}

/// NEGATIVE CONTROL — flattening must not turn into dropping. The universal
/// `∀g. a > g ∨ g ≥ h` holds exactly when `h ≤ a`, so every interpretation
/// that satisfies it (e.g. all-zero) falsifies the sibling leaf `h > a`. A
/// certificate that certified the `forall` leaf and skipped its ground
/// sibling would publish a false model of an UNSAT query.
#[test]
fn declines_when_a_ground_leaf_of_the_and_root_is_false_under_every_candidate() {
    let mut exec = executor_for(
        "(set-logic LRA)
         (declare-const a Real)
         (declare-const h Real)
         (assert (and (forall ((g Real)) (or (> a g) (>= g h))) (> h a)))",
    );
    let assertions = exec.ctx.assertions.clone();
    assert_eq!(assertions.len(), 1);
    assert!(
        exec.try_const_interp_sat_certificate(&assertions, LogicCategory::QfLra)
            .is_none(),
        "the ground leaf `h > a` must sink every combination the universal admits"
    );
    assert!(exec.const_interp_cert_witness_state.is_none());
}

/// REJECTING DIRECTION — only `and` is a conjunctive position. A quantifier
/// below an `or` leaf stays out of class even though the all-zero
/// interpretation happens to satisfy the whole root.
#[test]
fn declines_a_quantifier_below_a_disjunctive_leaf_of_the_and_root() {
    let mut exec = executor_for(
        "(set-logic LRA)
         (declare-const a Real)
         (declare-const h Real)
         (assert (and (forall ((g Real)) (or (> a g) (>= g h)))
                      (or (forall ((g Real)) (>= g a)) (>= h a))))",
    );
    let assertions = exec.ctx.assertions.clone();
    assert!(
        exec.try_const_interp_sat_certificate(&assertions, LogicCategory::QfLra)
            .is_none(),
        "a disjunctive quantified leaf is not a top-level forall and must decline"
    );
}

/// NEGATIVE CONTROL for the per-obligation verdict memo. `forall x. x > b` is
/// false under every interpretation, and its instance under `b := 0` recurs
/// verbatim in the second combination (`a := 1, b := 0`), where the other
/// universal folds to `true`. A memo that replayed a refuted obligation as
/// discharged would grant that combination: a `sat` for an UNSAT query.
#[test]
fn a_refuted_obligation_stays_refuted_when_a_later_combination_rebuilds_it() {
    let mut exec = executor_for(
        "(set-logic LRA)
         (declare-const a Real)
         (declare-const b Real)
         (assert (forall ((x Real)) (> x b)))
         (assert (forall ((y Real)) (or (>= a 1.0) (= y a))))",
    );
    let assertions = exec.ctx.assertions.clone();
    assert_eq!(
        assertions.len(),
        2,
        "the fixture must reach the certificate intact"
    );
    assert!(
        exec.try_const_interp_sat_certificate(&assertions, LogicCategory::QfLra)
            .is_none(),
        "no interpretation satisfies `forall x. x > b`"
    );
}

/// FINITE-TABLE, accepting direction: each universal shares an `and` root
/// with the ground point that pins its table. One table-plus-default model
/// certifies both roots, and the parked witness names the authored roots.
#[test]
fn finite_table_certifies_and_roots_and_binds_the_authored_roots() {
    let mut exec = executor_for(
        "(set-logic UFLIA)
         (declare-fun f (Int) Int)
         (declare-fun g (Int) Int)
         (assert (and (forall ((x Int)) (>= (f x) 0)) (= (f 2) 3)))
         (assert (and (forall ((y Int)) (>= (+ (f y) (g y)) 0)) (= (g 2) 0)))",
    );
    let roots = exec.ctx.assertions.clone();
    assert_eq!(
        roots.len(),
        2,
        "the fixture must reach the certificate as two and-roots"
    );
    assert!(
        exec.try_finite_table_sat_certificate(&roots, LogicCategory::Uflia)
            .is_some(),
        "one shared table model satisfies every leaf of both roots"
    );
    let leaves = flatten_quantified_and_roots(&exec.ctx.terms, &roots);
    let state = exec
        .finite_table_cert_witness_state
        .as_ref()
        .expect("a grant parks its witness");
    assert!(state.is_pending_current_for(&exec, &roots));
    assert!(!state.is_pending_current_for(&exec, &leaves));
}

/// FINITE-TABLE, negative control: the pinned point `f(2) = -1` sits in the
/// same root as `forall x. f(x) >= 0`. UNSAT; the ground leaf must be
/// re-verified, never dropped with the flattening.
#[test]
fn finite_table_declines_an_and_root_whose_ground_leaf_breaks_the_universal() {
    let mut exec = executor_for(
        "(set-logic UFLIA)
         (declare-fun f (Int) Int)
         (assert (and (forall ((x Int)) (>= (f x) 0)) (= (f 2) (- 1))))",
    );
    let roots = exec.ctx.assertions.clone();
    assert_eq!(roots.len(), 1);
    assert!(
        exec.try_finite_table_sat_certificate(&roots, LogicCategory::Uflia)
            .is_none(),
        "the ground leaf contradicts the universal at x = 2"
    );
}
