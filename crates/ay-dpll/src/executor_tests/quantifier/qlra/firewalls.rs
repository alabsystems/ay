// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Firewall barriers for the lane (plan §6).
//!
//! * `#quant-alternation`: a universal under a disjunction is not a fact; the
//!   M1 lane must decline it and must never manufacture a verdict from it.
//! * CE-hypothesis ambiguity (row 2): the main query never carries a
//!   counterexample formula, so a VALID universal is published `sat`. A
//!   mutation that conjoins `¬ψ[e⃗]` into S1 turns the valid universal's S1
//!   UNSAT; the lane then proposes a refutation the strict replay cannot
//!   certify and the lane-published `sat` below disappears.
//! * Dangling binder / shadowing (row 5): a binder that shadows a declared
//!   constant of the same name is substituted capture-free, in both
//!   directions.

use super::{assert_lane_sat, assert_lane_unsat, run};

#[test]
fn universal_under_disjunction_is_declined_not_treated_as_a_fact() {
    const SMT: &str = "(set-logic LRA)(declare-const p Bool)\
         (assert (or p (forall ((x Real)) (> x 0))))(assert (not p))(check-sat)";
    // Default posture: the nested search takes the shape; never `sat`.
    assert_ne!(run(SMT).verdict, "sat", "the problem is unsat");
    // The depth-1 (M1) lane alone, under `--no-qlra-nested`, declines it.
    let _nested_off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let run = run(SMT);
    assert!(run.recognized, "the recognizer admits the theory fragment");
    assert_eq!(
        run.decline.as_deref(),
        Some("shape-QuantifierUnderConnective"),
        "M1 must decline a universal outside conjunctive position"
    );
    assert_ne!(run.verdict, "sat", "the problem is unsat");
}

#[test]
fn satisfiable_disjunctive_universal_is_never_refuted() {
    let run = run("(set-logic LRA)(declare-const p Bool)\
         (assert (or p (forall ((x Real)) (> x 0))))(check-sat)");
    assert_ne!(run.verdict, "unsat", "p = true satisfies the problem");
}

/// Row 2: valid universals must come back `sat` from the lane itself.
#[test]
fn valid_universal_is_published_sat_not_misread_as_refuted() {
    assert_lane_sat(
        "valid-iff",
        "(set-logic LRA)(declare-const c Real)\
         (assert (forall ((x Real)) (xor (> x c) (<= x c))))(check-sat)",
    );
    assert_lane_sat(
        "valid-two-binder",
        "(set-logic LRA)\
         (assert (forall ((x Real) (y Real)) (=> (< x y) (< (+ x 1) (+ y 1)))))(check-sat)",
    );
}

/// Row 5: the binder `x` shadows the declared constant `x`.
#[test]
fn shadowing_binder_is_substituted_capture_free() {
    assert_lane_unsat(
        "shadow-unsat",
        "(set-logic LRA)(declare-const x Real)(assert (= x 1))\
         (assert (forall ((x Real)) (< x 1)))(check-sat)",
    );
    assert_lane_sat(
        "shadow-sat",
        "(set-logic LRA)(declare-const x Real)(assert (= x 1))\
         (assert (forall ((x Real)) (or (< x 1) (>= x 1))))(check-sat)",
    );
}

/// `#cegqi-ce-var-selection`: the refuting tuple of `∀a b. a = b` must be
/// closed; a selection leaking a counterexample constant could only produce
/// an instance the strict `forall_inst` check refuses.
#[test]
fn two_binder_equality_is_refuted_with_a_closed_tuple() {
    assert_lane_unsat(
        "forall-a-b-eq",
        "(set-logic LRA)(assert (forall ((a Real) (b Real)) (= a b)))(check-sat)",
    );
}
