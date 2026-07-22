// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for to_int floor axiom injection in LRA (#5944).
//!
//! Before this fix, any formula with symbolic `to_int(x)` returned Unknown
//! because LRA set `saw_unsupported = true`. The fix injects floor axioms:
//!   to_int(x) <= x < to_int(x) + 1
//! so that the simplex solver can reason about the floor function.

use ntest::timeout;

/// SAT: Simple to_int with symbolic variable should not return Unknown.
/// Before #5944, this returned Unknown because saw_unsupported was set.
#[test]
#[timeout(30_000)]
fn test_to_int_symbolic_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= y (to_int x)))
        (assert (>= x 2.5))
        (assert (<= x 2.9))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Before #5944 this returned unknown (saw_unsupported). Floor axioms
    // now let the solver determine y=2 satisfies the constraints.
    assert_eq!(
        outputs[0], "sat",
        "to_int(x) with x in [2.5, 2.9] should be sat with y=2"
    );
}

/// UNSAT: to_int(x) > x violates the floor axiom to_int(x) <= x.
#[test]
#[timeout(30_000)]
fn test_to_int_greater_than_arg_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (> (to_real (to_int x)) x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(x) <= x is a theory axiom, so to_real(to_int(x)) > x is UNSAT.
    assert_eq!(outputs[0], "unsat", "to_int(x) > x violates floor axiom");
}

/// SAT: to_int(x) = 3 with x in [3.0, 4.0) is satisfiable.
#[test]
#[timeout(30_000)]
fn test_to_int_bounded_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_int x) 3))
        (assert (>= x 3.0))
        (assert (< x 4.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "to_int(x)=3 with x in [3.0, 4.0) should be sat"
    );
}

/// UNSAT: to_int(x) = 3 with x < 3.0 is unsatisfiable.
/// Floor axiom: to_int(x) <= x, so to_int(x) = 3 implies x >= 3.
#[test]
#[timeout(30_000)]
fn test_to_int_below_floor_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_int x) 3))
        (assert (< x 3.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(x) = 3 => to_int(x) <= x => 3 <= x, contradicts x < 3.0
    assert_eq!(
        outputs[0], "unsat",
        "to_int(x)=3 with x < 3.0 is UNSAT via floor axiom"
    );
}

/// UNSAT: to_int(x) = 3 with x >= 4.0 is unsatisfiable.
/// Floor axiom: x < to_int(x) + 1, so to_int(x) = 3 implies x < 4.
#[test]
#[timeout(30_000)]
fn test_to_int_above_ceil_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_int x) 3))
        (assert (>= x 4.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(x) = 3 => x < to_int(x) + 1 => x < 4, contradicts x >= 4.0
    assert_eq!(
        outputs[0], "unsat",
        "to_int(x)=3 with x >= 4.0 is UNSAT via ceil axiom"
    );
}

/// SAT: to_int(x) = x when x is integer-valued.
/// The fractional part x - to_int(x) = 0 when x is an integer.
#[test]
#[timeout(30_000)]
fn test_to_int_integer_valued_real_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_real (to_int x)) x))
        (assert (>= x 0.0))
        (assert (<= x 10.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_real(to_int(x)) = x iff x is integer-valued. Combined with
    // 0 <= x <= 10, any integer in [0..10] satisfies this.
    assert_eq!(
        outputs[0], "sat",
        "to_int(x) = x for integer-valued reals should be sat"
    );
}

/// UNSAT: to_int(x) = 3 AND to_int(x) = 4 is a contradiction.
/// Both equalities create conflicting bounds on the same variable.
#[test]
#[timeout(30_000)]
fn test_to_int_conflicting_values_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_int x) 3))
        (assert (= (to_int x) 4))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "unsat",
        "to_int(x)=3 AND to_int(x)=4 is a contradiction"
    );
}

/// UNSAT: negative to_int with positive constraint.
/// to_int(x) = -1 implies -1 <= x < 0, which contradicts x > 0.
#[test]
#[timeout(30_000)]
fn test_to_int_negative_floor_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= (to_int x) (- 1)))
        (assert (> x 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(x) = -1 => -1 <= x < 0, contradicts x > 0
    assert_eq!(outputs[0], "unsat", "to_int(x)=-1 with x > 0 is UNSAT");
}
