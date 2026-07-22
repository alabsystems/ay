// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6193: QF_AUFLIA false UNSAT on trivially SAT formulas.
//!
//! Root cause: `get_or_create_slack` keyed on coefficients only, ignoring the
//! constant offset. When Nelson-Oppen equality exchange caused LIA to assert
//! `(+ x y) = 30` via `assert_shared_equality`, the LRA simplex reused the
//! slack variable created for `x + y - 30` (from the original atom `(= (+ x y) 30)`)
//! but applied the bound 30 directly to that slack. Since the slack represents
//! `x + y - 30`, this asserted `x + y - 30 >= 30` (i.e., `x + y >= 60`) instead
//! of the correct `x + y - 30 >= 0` (i.e., `x + y >= 30`). Combined with the
//! upper bound `x + y <= 30`, simplex detected a spurious conflict.
//!
//! Fix: `get_or_create_slack` now returns the original constant alongside the
//! slack variable, and `assert_bound_with_reasons` adjusts the bound by the
//! constant difference when reusing a slack.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Minimal reproducer: x=10, y=20, x+y=30 in QF_AUFLIA.
/// Must return SAT. Previously returned UNSAT (#6193).
#[test]
#[timeout(10_000)]
fn test_auflia_sum_equality_sat_6193() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 10))
        (assert (= y 20))
        (assert (= (+ x y) 30))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 regression: trivially SAT QF_AUFLIA formula must not return unsat"
    );
}

/// Full reproducer with array select: x=10, y=20, x+y=30, a[x]=y.
/// Must return SAT. Previously returned UNSAT (#6193).
#[test]
#[timeout(10_000)]
fn test_auflia_sum_with_array_select_sat_6193() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 10))
        (assert (= y 20))
        (assert (= (+ x y) 30))
        (assert (= (select a x) y))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 regression: SAT QF_AUFLIA with array select must not return unsat"
    );
}

/// Negative constants: x=-3, y=-7, x+y=-10 in QF_AUFLIA.
/// Tests that the constant-offset adjustment works with negative values.
#[test]
#[timeout(10_000)]
fn test_auflia_negative_constants_sat_6193() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x (- 3)))
        (assert (= y (- 7)))
        (assert (= (+ x y) (- 10)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 regression: negative constant SAT case must not return unsat"
    );
}

/// Three variables with inequality: x+y+z <= 100 AND x=10 AND y=20 AND z=30.
/// The atom `(+ x y z) <= 100` creates a slack for `x+y+z-100`, while the
/// shared equality from N-O would use a different constant offset.
#[test]
#[timeout(10_000)]
fn test_auflia_three_var_inequality_sat_6193() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (= x 10))
        (assert (= y 20))
        (assert (= z 30))
        (assert (<= (+ x (+ y z)) 100))
        (assert (>= (+ x (+ y z)) 50))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 regression: three-variable inequality must return sat"
    );
}

/// Genuine UNSAT case: x=10, y=20, x+y=31 is unsatisfiable.
/// Ensures the fix does not cause false SAT.
#[test]
#[timeout(10_000)]
fn test_auflia_sum_genuine_unsat_6193() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 10))
        (assert (= y 20))
        (assert (= (+ x y) 31))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "unsat",
        "#6193: genuinely UNSAT case must still return unsat"
    );
}

/// QF_LRA (rational) constant-offset test: x + y = 3/2 with fractional constants.
/// Verifies the slack constant-offset fix works correctly with BigRational arithmetic,
/// not just BigInteger.
#[test]
#[timeout(10_000)]
fn test_lra_fractional_constant_offset_sat_6193() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x (/ 1 2)))
        (assert (= y 1))
        (assert (= (+ x y) (/ 3 2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 coverage: fractional constant-offset with QF_LRA must be SAT"
    );
}

/// Multiple different constants sharing the same linear combination `x + y`:
/// (x + y = 5) AND (x + y <= 10) — both reuse the same slack variable
/// but with different constant offsets. Must be SAT.
#[test]
#[timeout(10_000)]
fn test_multi_constant_slack_reuse_sat_6193() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x y) 5))
        (assert (<= (+ x y) 10))
        (assert (>= (+ x y) 0))
        (assert (>= x 0))
        (assert (>= y 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6193 coverage: multiple constants on same linear combination must be SAT"
    );
}

/// Contradictory constants on the same linear combination:
/// (x + y = 5) AND (x + y = 10) — UNSAT. Both create bounds on the same slack.
/// Verifies the constant-offset adjustment correctly detects the conflict.
#[test]
#[timeout(10_000)]
fn test_contradictory_constants_same_slack_unsat_6193() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x y) 5))
        (assert (= (+ x y) 10))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "unsat",
        "#6193 coverage: contradictory constants on same slack must be UNSAT"
    );
}

/// Push/pop scope test: slack variable created in scope 1 is reused in scope 2
/// with a different constant. Verifies that bounds from popped scopes don't
/// contaminate the reused slack.
#[test]
#[timeout(10_000)]
fn test_push_pop_slack_reuse_6193() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (assert (>= y 0))
        (assert (<= y 10))
        (push 1)
        (assert (= (+ x y) 15))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (+ x y) 5))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    // First check-sat: x+y=15 with x,y in [0,10] — SAT at x=5, y=10
    assert_eq!(
        outputs[0].trim(),
        "sat",
        "#6193 coverage: x+y=15 with x,y in [0,10] must be SAT"
    );
    // Second check-sat: x+y=5 with x,y in [0,10] — SAT at x=0, y=5
    assert_eq!(
        outputs[1].trim(),
        "sat",
        "#6193 coverage: after pop, x+y=5 with x,y in [0,10] must be SAT"
    );
}
