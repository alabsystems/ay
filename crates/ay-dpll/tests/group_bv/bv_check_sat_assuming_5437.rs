// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for `check-sat-assuming` in BV-family logics (#5437).
//!
//! Path B (solve_with_assumptions_for_theory) was missing:
//! - EUF congruence axioms for UfBv/AufBv
//! - Non-BV-return UF congruence for UfBv/AufBv
//! - Bool ITE condition filtering (linked ALL Bool terms, not just bv_ite_conditions)
//! - materialize_array_bv_terms for AufBv/ArrayBv

use ntest::timeout;

/// Core regression test for #5437: UFBV congruence via check-sat-assuming.
/// x=y must imply f(x)=f(y) by congruence, making (distinct (f x) (f y)) false.
/// The assumption (p) where p = (distinct (f x) (f y)) should be UNSAT.
#[test]
#[timeout(60_000)]
fn test_ufbv_check_sat_assuming_euf_congruence_regression_5437() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= x y))
        (assert (= p (distinct (f x) (f y))))
        (check-sat-assuming (p))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same congruence test but through AUFBV logic.
#[test]
#[timeout(60_000)]
fn test_aufbv_check_sat_assuming_euf_congruence_regression_5437() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= x y))
        (assert (= p (distinct (f x) (f y))))
        (check-sat-assuming (p))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Non-BV-return UF congruence via check-sat-assuming (#5433/#5437).
/// f returns Bool, not BitVec. The EUF axiom generator skips non-BV-return UFs,
/// so the non-BV-return congruence encoding must handle this case.
#[test]
#[timeout(60_000)]
fn test_ufbv_check_sat_assuming_non_bv_return_congruence_5437() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun p ((_ BitVec 8)) Bool)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (p x))
        (assert (not (p y)))
        (check-sat-assuming ())
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Path A regression: Bool-return UF congruence via regular check-sat (#5437).
/// This exercises generate_non_bv_euf_congruence (Path A) rather than
/// solve_with_assumptions_for_theory (Path B). The direct Tseitin variable
/// congruence encoding must make p(x) ↔ p(y) when x=y.
#[test]
#[timeout(60_000)]
fn test_ufbv_check_sat_bool_return_uf_congruence_path_a_5437() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun p ((_ BitVec 8)) Bool)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (p x))
        (assert (not (p y)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Simple QF_BV check-sat-assuming should still work (no UF involved).
#[test]
#[timeout(60_000)]
fn test_qf_bv_check_sat_assuming_basic_5437() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (= x #x00)))
        (assert (= x #xFF))
        (check-sat-assuming (p))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Proof-production robustness (b22): contradictory ground assumptions
/// (`x=bv1 ∧ x=bv2`) fold to UNSAT during preprocessing without routing
/// through the proof-producing SAT solver, so the proof tracker has no steps
/// and there are no `(assert ...)` problem assertions to seed `Assume` steps.
/// `build_unsat_proof` previously produced an EMPTY proof and tripped the
/// non-empty postcondition `debug_assert`. The verdict is correctly UNSAT;
/// this asserts no panic and that a valid (non-empty) proof is produced.
#[test]
#[timeout(60_000)]
fn test_qf_bv_check_sat_assuming_contradictory_ground_assumptions_no_panic_b22() {
    let smt = r#"
        (set-logic QF_BV)
        (set-option :produce-proofs true)
        (declare-const x (_ BitVec 2))
        (check-sat-assuming ((= x (_ bv1 2)) (= x (_ bv2 2))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same shape as b22 but with a base assertion plus a single contradicting
/// assumption — the conflict still folds at preprocessing. Verifies the proof
/// path stays robust when the problem assertion list is non-empty.
#[test]
#[timeout(60_000)]
fn test_qf_bv_check_sat_assuming_base_plus_contradicting_assumption_no_panic_b22() {
    let smt = r#"
        (set-logic QF_BV)
        (set-option :produce-proofs true)
        (declare-const x (_ BitVec 2))
        (assert (= x (_ bv1 2)))
        (check-sat-assuming ((= x (_ bv2 2))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// UFBV: SAT case with empty assumptions (trivially satisfiable).
/// Note: BV Path B model extraction has a pre-existing limitation where SAT
/// results may return "unknown" due to model validation failures. The core
/// soundness fix in #5437 is about wrong-SAT (should be UNSAT) results.
/// This test verifies we don't regress to "unsat" (which would be unsound).
#[test]
#[timeout(60_000)]
fn test_ufbv_check_sat_assuming_sat_empty_assumptions_5437() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (assert (= (f x) #xFF))
        (check-sat-assuming ())
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Must not be "unsat" (unsound). "sat" is correct; "unknown" is acceptable
    // due to pre-existing BV Path B model extraction limitation.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got: {outputs:?}"
    );
}
