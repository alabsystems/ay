// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness tests for LIRA cross-sort propagation (#5956 soundness fix).
//!
//! The original #5947 fix propagated non-tight integer assignments (e.g.,
//! `phase=0` from bounds `0 <= phase <= 1`) as tight bounds in LRA with
//! non-tight bound reasons. This created unsound conflict clauses: the
//! reasons only justified `0 <= x <= 1` but the assertion was `x = 0`.
//! When LRA conflicted, the learned clause blocked the range [0,1] instead
//! of just x=0, potentially causing false UNSAT on satisfiable formulas.
//!
//! The fix propagates individual bounds (sound) and requests a branch-and-bound
//! split to establish tight bounds on shared variables.

use ntest::timeout;

/// SAT: phase in {0,1} Int, to_real(phase) > 0.5 forces phase=1.
/// Regression: returned UNSAT due to unsound cross-sort conflict clause
/// blocking the range [0,1] instead of just the specific value phase=0.
#[test]
#[timeout(60_000)]
fn test_cross_sort_sat_phase_gt_half() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const phase Int)
        (declare-const y Real)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (> (to_real phase) 0.5))
        (assert (= y (to_real phase)))
        (assert (> y 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "phase=1, y=1.0 is a valid model");
}

/// SAT: phase in {0,1} Int, to_real(phase) >= 1.0 forces phase=1.
/// Simpler variant: just the bound constraint.
#[test]
#[timeout(60_000)]
fn test_cross_sort_sat_phase_ge_one() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const phase Int)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (>= (to_real phase) 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "phase=1 satisfies all constraints");
}

/// SAT: x in {0,1,2} Int, Real constraint needs to_real(x) >= 1.5.
/// Only x=2 satisfies. Tests non-binary integer range.
#[test]
#[timeout(60_000)]
fn test_cross_sort_sat_wider_range() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 2))
        (assert (>= (to_real x) 1.5))
        (assert (= r (+ (to_real x) 0.5)))
        (assert (> r 2.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x=2, r=2.5 is a valid model");
}

/// UNSAT: x in {0,1} Int, but Real constraints are inconsistent for both values.
/// Verifies the fix doesn't break UNSAT detection.
#[test]
#[timeout(60_000)]
fn test_cross_sort_unsat_both_branches() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= r (to_real x)))
        (assert (> r 1.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "no integer in [0,1] satisfies r > 1.5"
    );
}

/// SAT with Big-M pattern: same structure as #5947 but SAT.
/// phase=1 allows relu to be active, satisfying the lower bound.
#[test]
#[timeout(60_000)]
fn test_big_m_sat_phase_one() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const X_0 Real)
        (declare-const relu_1 Real)
        (declare-const phase_2 Int)
        (assert (>= X_0 0.0))
        (assert (<= X_0 2.0))
        (assert (>= phase_2 0))
        (assert (<= phase_2 1))
        (assert (>= relu_1 0.0))
        (assert (<= relu_1 (* 1000000.0 (to_real phase_2))))
        (assert (>= relu_1 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "phase_2=1 allows relu_1=1.0");
}
