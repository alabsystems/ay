// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #6020: LRA NeedDisequalitySplit crash in combined
//! theory N-O check loop.
//!
//! The LRA solver legitimately produces NeedDisequalitySplit for disequality
//! constraints (x != c). Before the fix, `triage_lra_result` hit
//! `debug_assert!(false)` causing SIGABRT in debug mode. These tests exercise
//! disequality constraints in combined theory logics that route through the
//! N-O check loop: QF_UFLRA, QF_AUFLRA.

use ntest::timeout;

/// QF_UFLRA: uninterpreted function with real disequality.
/// Triggers triage_lra_result via uf_lra.rs N-O check loop.
/// Before fix: debug_assert crash. After fix: sat or unknown.
#[test]
#[timeout(30_000)]
fn test_uflra_disequality_no_crash_6020() {
    let result = crate::common::solve(
        "(set-logic QF_UFLRA)
         (declare-fun f (Real) Real)
         (declare-const x Real)
         (declare-const y Real)
         (assert (not (= x y)))
         (assert (= (f x) 1.0))
         (assert (= (f y) 2.0))
         (check-sat)",
    );
    // Formula is SAT (x=0, y=1, f(0)=1, f(1)=2). Must not crash or return unsat.
    assert_ne!(
        result, "unsat",
        "#6020: QF_UFLRA disequality must not return unsat"
    );
}

/// QF_AUFLRA: array + UF + real disequality.
/// Triggers triage_lra_result via auf_lra.rs N-O check loop.
/// This is the original crash path from #6020.
#[test]
#[timeout(30_000)]
fn test_auflra_disequality_no_crash_6020() {
    let result = crate::common::solve(
        "(set-logic QF_AUFLRA)
         (declare-const a (Array Real Real))
         (declare-const i Real)
         (declare-const j Real)
         (assert (not (= i j)))
         (assert (= (select (store a i 1.0) j) (select a j)))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "#6020: QF_AUFLRA disequality must not return unsat"
    );
}

/// Pure QF_LRA: multi-variable disequality with bounded reals.
/// The standalone LRA split-loop pipeline must converge in 2 iterations:
///   1. Simplex finds x = y = 0, disequality violated → NeedExpressionSplit
///   2. Split clause forces x < y or x > y → disequality satisfied → Sat
/// Before the fix: infinite loop because the disequality eval used
/// info.value.rational() which discards the epsilon component, so
/// x = 0+ε, y = 0 evaluated as x - y = 0 (violated) instead of ε (satisfied).
#[test]
#[timeout(10_000)]
fn test_lra_pure_disequality_sat_6020() {
    let result = crate::common::solve(
        "(set-logic QF_LRA)
         (declare-const x Real)
         (declare-const y Real)
         (assert (not (= x y)))
         (assert (>= x 0.0))
         (assert (<= x 1.0))
         (assert (>= y 0.0))
         (assert (<= y 1.0))
         (check-sat)",
    );
    assert_eq!(result, "sat", "#6020: Pure LRA disequality must return sat");
}

/// QF_LRA: single-variable disequality (x != 0) with bounded real.
/// This exercises the NeedDisequalitySplit path (single coefficient).
#[test]
#[timeout(10_000)]
fn test_lra_single_var_disequality_sat_6020() {
    let result = crate::common::solve(
        "(set-logic QF_LRA)
         (declare-const x Real)
         (assert (not (= x 0.0)))
         (assert (>= x (- 1.0)))
         (assert (<= x 1.0))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "#6020: Single-var LRA disequality must return sat"
    );
}
