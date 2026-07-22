// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Assumption-side SAT canaries for combined theory routes (#6731 Packet 4).
//!
//! These tests verify that `check-sat-assuming` returns `sat` (not `unknown`)
//! for trivially SAT formulas through the combined AUFLIA/LIRA/AUFLIRA paths.
//!
//! The root cause of #6731 was inner `finalize_sat_model_validation()` running
//! against temporary preprocessed assertions instead of the original formula.
//! `with_deferred_postprocessing` fixes this by deferring validation to the
//! outer `check_sat_assuming()` boundary.

use ntest::timeout;

/// QF_AUFLIA check-sat-assuming SAT canary: array with integer index.
///
/// Uses a direct boolean assumption (not a named boolean) to test the
/// AUFLIA assumption path through `with_deferred_postprocessing`.
/// Without the deferred-postprocessing fix, inner validation against
/// preprocessed assertions can degrade SAT to unknown.
///
/// The formula is trivially SAT: `(select (store a i 42) i) = 42` holds
/// by the array read-over-write axiom. Accepting `unsat` would mask a
/// soundness bug.
#[test]
#[timeout(60_000)]
fn test_auflia_assume_store_select_sat_canary_6731() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= (store a i 42) b))
        (check-sat-assuming ((= (select b i) 42)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "#6731 canary: QF_AUFLIA check-sat-assuming store/select must return sat, got {outputs:?}"
    );
}

/// QF_LIRA check-sat-assuming SAT canary: mixed Int/Real assumption.
///
/// Exercises the LIRA-ASSUME path through `with_deferred_postprocessing`.
/// A trivially SAT mixed-sort formula under assumptions must not degrade
/// to unknown due to validation running against preprocessed assertions.
///
/// The formula is trivially SAT: `x = 0, y = 1.0` satisfies all three
/// constraints. Accepting `unsat` would mask a soundness bug.
#[test]
#[timeout(60_000)]
fn test_lira_assume_mixed_sat_canary_6731() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (>= (to_real x) 0.0))
        (assert (<= y 10.0))
        (check-sat-assuming ((< (to_real x) y)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "#6731 canary: QF_LIRA check-sat-assuming must return sat, got {outputs:?}"
    );
}
