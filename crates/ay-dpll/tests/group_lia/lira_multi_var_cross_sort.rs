// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for LIRA cross-sort propagation with multiple shared variables.
//!
//! All existing LIRA cross-sort tests use a single shared variable (one
//! `to_real(x)` coercion). This file tests multi-variable cross-sort
//! propagation where LIA must forward several integer assignments to LRA
//! in the same Nelson-Oppen iteration.
//!
//! Coverage gap identified in proof_coverage audit: `propagate_cross_sort_values`
//! iterates over all shared variables, but no test previously verified that
//! multiple variables are propagated correctly together.

use ntest::timeout;

/// Two shared Int/Real variables: x + y in Int, to_real(x) + to_real(y) in Real.
/// max(x,y) = (1,1) → to_real(x) + to_real(y) = 2.0 < 2.5. UNSAT.
#[test]
#[timeout(60_000)]
fn test_lira_two_shared_vars_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (= r (+ (to_real x) (to_real y))))
        (assert (> r 2.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "max(to_real(x) + to_real(y)) = 2.0 < 2.5"
    );
}

/// Two shared vars, SAT: x in {0,1,2}, y in {0,1,2}.
/// to_real(x) + to_real(y) >= 3.0 requires x+y >= 3, e.g. x=2,y=1.
#[test]
#[timeout(60_000)]
fn test_lira_two_shared_vars_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 2))
        (assert (>= y 0))
        (assert (<= y 2))
        (assert (= r (+ (to_real x) (to_real y))))
        (assert (>= r 3.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "x=2,y=1 (or x=1,y=2) satisfies r >= 3.0"
    );
}

/// Three shared variables: x, y, z all in {0,1}.
/// Real constraint: to_real(x) + to_real(y) + to_real(z) > 3.5.
/// Max is 3.0. UNSAT.
#[test]
#[timeout(60_000)]
fn test_lira_three_shared_vars_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (>= z 0))
        (assert (<= z 1))
        (assert (= r (+ (to_real x) (+ (to_real y) (to_real z)))))
        (assert (> r 3.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "max sum of 3 binary ints is 3.0 < 3.5"
    );
}

/// Three shared variables SAT: x, y, z in {0,1}.
/// Constraint: to_real(x) + to_real(y) + to_real(z) = 2.0.
/// Satisfiable by any pair-of-ones, e.g. x=1,y=1,z=0.
#[test]
#[timeout(60_000)]
fn test_lira_three_shared_vars_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (>= z 0))
        (assert (<= z 1))
        (assert (= r (+ (to_real x) (+ (to_real y) (to_real z)))))
        (assert (= r 2.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "e.g. x=1,y=1,z=0 gives r=2.0");
}

/// Mixed Int/Real constraints: both x and y forced to specific values (x=2, y=1),
/// but Real side requires sum > 3.5. to_real(2) + to_real(1) = 3.0, not > 3.5. UNSAT.
#[test]
#[timeout(60_000)]
fn test_lira_two_forced_vars_cross_sort_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const r Real)
        (assert (= x 2))
        (assert (= y 1))
        (assert (= r (+ (to_real x) (to_real y))))
        (assert (> r 3.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // x=2, y=1 → r = 3.0, not > 3.5. UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Two shared vars with different ranges: x in {0..10}, y in {0..5}.
/// to_real(x) - to_real(y) > 6.0 requires x - y > 6. Max: x=10,y=0 → 10 > 6. SAT.
#[test]
#[timeout(60_000)]
fn test_lira_different_ranges_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const diff Real)
        (assert (>= x 0))
        (assert (<= x 10))
        (assert (>= y 0))
        (assert (<= y 5))
        (assert (= diff (- (to_real x) (to_real y))))
        (assert (> diff 6.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x=10,y=0 → diff=10.0 > 6.0");
}
