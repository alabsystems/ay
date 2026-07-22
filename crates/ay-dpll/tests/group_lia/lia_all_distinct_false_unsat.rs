// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for false UNSAT on QF_LIA all-distinct + arithmetic (#5671).
//!
//! AY incorrectly returns UNSAT on satisfiable QF_LIA problems when 4+ bounded
//! integer variables have all pairwise disequality constraints plus additional
//! arithmetic constraints (e.g., diagonal constraints for N-queens).
//!
//! Root cause: multi-variable disequality splits used NeedDisequalitySplit which
//! creates clause (x <= v-1 | x >= v+1 | eq(x,y)). When eq(x,y) is false, this
//! permanently excludes x from value v. After multiple LP iterations with x=y at
//! different values, x is excluded from its entire domain -- but x != y does NOT
//! imply x != v. Fix: use NeedExpressionSplit for multi-variable disequalities,
//! which encodes (E <= F-1 | E >= F+1) and correctly splits on the difference.

use ntest::timeout;

/// 4-queens minimal repro: 4 bounded integer variables with all pairwise
/// disequalities + one diagonal constraint pair.
///
/// Expected: sat (e.g., q1=1, q2=3, q3=4, q4=2)
/// Before fix: unsat (false UNSAT from accumulated disequality split exclusions)
#[test]
#[timeout(10_000)]
fn test_4queens_minimal_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int)
        (declare-const q2 Int)
        (declare-const q3 Int)
        (declare-const q4 Int)
        (assert (>= q1 1)) (assert (<= q1 4))
        (assert (>= q2 1)) (assert (<= q2 4))
        (assert (>= q3 1)) (assert (<= q3 4))
        (assert (>= q4 1)) (assert (<= q4 4))
        ; All 6 pairwise disequalities
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q1 q4)))
        (assert (not (= q2 q3)))
        (assert (not (= q2 q4)))
        (assert (not (= q3 q4)))
        ; One pair of diagonal constraints
        (assert (not (= (+ q1 (- q2)) 1)))
        (assert (not (= (+ q1 (- q2)) (- 1))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "4-queens minimal repro must be SAT (#5671)"
    );
}

/// Verify 4 variables all-distinct only (no diagonal) is SAT.
/// Ensures the expression split path doesn't break the simple all-distinct case.
#[test]
#[timeout(10_000)]
fn test_4vars_all_distinct_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int) (declare-const q2 Int)
        (declare-const q3 Int) (declare-const q4 Int)
        (assert (>= q1 1)) (assert (<= q1 4))
        (assert (>= q2 1)) (assert (<= q2 4))
        (assert (>= q3 1)) (assert (<= q3 4))
        (assert (>= q4 1)) (assert (<= q4 4))
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q1 q4)))
        (assert (not (= q2 q3)))
        (assert (not (= q2 q4)))
        (assert (not (= q3 q4)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat", "4 all-distinct in [1,4] is SAT");
}

/// Edge case: 3 variables all-distinct + diagonal.
/// Tests that the expression split doesn't regress on smaller instances.
#[test]
#[timeout(10_000)]
fn test_3vars_all_distinct_plus_diagonal_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int)
        (declare-const q2 Int)
        (declare-const q3 Int)
        (assert (>= q1 1)) (assert (<= q1 3))
        (assert (>= q2 1)) (assert (<= q2 3))
        (assert (>= q3 1)) (assert (<= q3 3))
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q2 q3)))
        (assert (not (= (- q1 q2) 1)))
        (assert (not (= (- q1 q2) (- 1))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "3 all-distinct in [1,3] with diagonal is SAT"
    );
}
