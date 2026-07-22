// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #5947: LIRA solver returns SAT for UNSAT Big-M ReLU
//! encoding. The formula uses mixed Int/Real constraints with a `to_real`
//! coercion. The N-O combination must correctly propagate the integer
//! assignment for the shared variable across the Int/Real theory boundary.

use ntest::timeout;

/// Big-M ReLU encoding: phase_2 in {0,1} controls relu_1 activation.
///
/// With phase_2=1: relu_1 = lin_0 = X_0 <= 0.5, so Y_0 <= 0.5 < 1.0
/// With phase_2=0: relu_1 <= M*0 = 0 and relu_1 >= 0, so relu_1 = 0, Y_0 = 0 < 1.0
/// Both cases: Y_0 < 1.0, contradicting (>= Y_0 1.0). UNSAT.
///
/// Regression: ay returned SAT with phase_2=0, relu_1=1.0 (violating relu_1 <= M*phase_2=0).
/// Root cause: N-O cross-sort propagation only forwarded tight LIA bounds; non-tight but
/// integer-valued simplex assignments (0 <= phase_2 <= 1 with assignment 0) were not
/// propagated to LRA, so LRA could assign a different value to the shared variable.
#[test]
#[timeout(60_000)]
fn test_big_m_relu_unsat_5947() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const X_0 Real)
        (declare-const Y_0 Real)
        (declare-const lin_0 Real)
        (declare-const relu_1 Real)
        (declare-const phase_2 Int)
        (declare-const lin_3 Real)
        (assert (>= X_0 0.0))
        (assert (<= X_0 0.5))
        (assert (= lin_0 (* 1.0 X_0)))
        (assert (>= phase_2 0))
        (assert (<= phase_2 1))
        (assert (>= relu_1 0.0))
        (assert (>= relu_1 lin_0))
        (assert (<= relu_1 (+ lin_0 (* 1000000.0 (- 1 phase_2)))))
        (assert (<= relu_1 (* 1000000.0 phase_2)))
        (assert (= lin_3 (* 1.0 relu_1)))
        (assert (= Y_0 lin_3))
        (assert (>= Y_0 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Minimal version: just the conflicting constraints without chain variables.
/// phase_2 in {0,1} Int, relu Real, relu <= M * phase_2, relu >= 1.
#[test]
#[timeout(60_000)]
fn test_big_m_minimal_unsat_5947() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const relu Real)
        (declare-const phase Int)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (>= relu 0.0))
        (assert (<= relu (* 1000000.0 phase)))
        (assert (>= relu 1.0))
        (assert (= phase 0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// The phase=0 case without explicit equality — LIA must choose 0 from bounds.
/// Without to_real propagation, LRA doesn't learn the phase=0 assignment.
#[test]
#[timeout(60_000)]
fn test_big_m_phase_zero_implied_5947() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const relu Real)
        (declare-const phase Int)
        (assert (>= phase 0))
        (assert (<= phase 0))
        (assert (>= relu 0.0))
        (assert (<= relu (* 100.0 phase)))
        (assert (>= relu 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}
