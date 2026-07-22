// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundary-condition tests for atom_slack constant compensation (#6209).
//!
//! These tests exercise edge cases in the constant-offset adjustment
//! when reusing slack variables across push/pop scopes:
//! - Strict inequality + constant compensation
//! - Zero constant → non-zero constant transitions
//! - SAT-then-UNSAT across push/pop with same linear combination
//! - QF_LRA fractional constant offsets with strict bounds

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Strict inequality + push/pop: first scope uses x + y < 10, second uses x + y < 5.
/// Both SAT. Tests that strict bound compensation doesn't drop strictness.
#[test]
#[timeout(10_000)]
fn test_strict_inequality_push_pop_compensation() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (>= y 0))
        (push 1)
        (assert (< (+ x y) 10))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (< (+ x y) 5))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs[0].trim(), "sat", "x + y < 10 with x,y >= 0: SAT");
    assert_eq!(
        outputs[1].trim(),
        "sat",
        "x + y < 5 with x,y >= 0: SAT after pop"
    );
}

/// Zero-constant → non-zero constant transition: first scope asserts x + y > 0,
/// second asserts x + y > 10. The slack for x + y is created with constant 0
/// in the first scope. On reuse, constant compensation must adjust by 10.
#[test]
#[timeout(10_000)]
fn test_zero_to_nonzero_constant_compensation() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= x 100))
        (assert (<= y 100))
        (push 1)
        (assert (> (+ x y) 0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> (+ x y) 10))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs[0].trim(), "sat", "x + y > 0: SAT");
    assert_eq!(outputs[1].trim(), "sat", "x + y > 10: SAT after pop");
}

/// SAT-then-UNSAT across push/pop: first scope is SAT, second is genuinely UNSAT.
/// x, y in [0, 3]. First: x + y <= 6 (SAT). Second: x + y <= -1 (UNSAT).
/// Verifies constant compensation correctly detects the UNSAT conflict.
#[test]
#[timeout(10_000)]
fn test_sat_then_unsat_push_pop_compensation() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (push 1)
        (assert (<= (+ x y) 6))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (<= (+ x y) (- 1)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs[0].trim(), "sat", "x + y <= 6 with x,y >= 0: SAT");
    assert_eq!(
        outputs[1].trim(),
        "unsat",
        "x + y <= -1 with x,y >= 0: UNSAT"
    );
}

/// QF_LRA fractional strict bounds: x + y < 1/2, then x + y < 3/2.
/// Tests BigRational constant compensation with strict inequality.
#[test]
#[timeout(10_000)]
fn test_fractional_strict_bound_compensation() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (>= y 0))
        (push 1)
        (assert (< (+ x y) (/ 1 2)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (< (+ x y) (/ 3 2)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs[0].trim(), "sat", "x + y < 1/2 with x,y >= 0: SAT");
    assert_eq!(
        outputs[1].trim(),
        "sat",
        "x + y < 3/2 with x,y >= 0: SAT after pop"
    );
}

/// Three scopes: same linear combination, three different constants.
/// Exercises atom_slack cache reuse across multiple pop cycles.
/// x, y >= 0.  scope1: x+y=5 (SAT).  scope2: x+y=0 (SAT, x=y=0).  scope3: x+y=-1 (UNSAT).
#[test]
#[timeout(10_000)]
fn test_three_scope_constant_progression() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (push 1)
        (assert (= (+ x y) 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (+ x y) 0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (+ x y) (- 1)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs[0].trim(), "sat", "x + y = 5: SAT");
    assert_eq!(outputs[1].trim(), "sat", "x + y = 0: SAT (x=y=0)");
    assert_eq!(
        outputs[2].trim(),
        "unsat",
        "x + y = -1 with x,y >= 0: UNSAT"
    );
}
