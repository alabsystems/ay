// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6209: QF_LIA false UNSAT on disjunctive formulas.
//!
//! Root cause: atom_slack cache keyed on coefficients only, ignoring constant
//! offsets. When reusing a slack variable for a different bound with the same
//! coefficients but a different constant, the old constant was applied instead
//! of the new one. Fixed in b09b1a1cf by storing the original constant in the
//! cache and applying constant compensation on reuse.
//!
//! These formulas encode loop invariant preservation counterexamples from
//! verification-consumer (loop verification conditions). Each asserts preconditions AND
//! NOT(postcondition) and expects SAT (counterexample exists).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Disjunctive loop condition: (i < n) || (k > 0).
/// Counterexample: i=0, n=0, k=1, i_prime=1.
#[test]
#[timeout(10_000)]
fn test_lia_disjunctive_cond_sat_6209() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const n Int)
        (declare-const k Int)
        (declare-const i_prime Int)
        (assert (>= i 0))
        (assert (<= i n))
        (assert (or (< i n) (> k 0)))
        (assert (= i_prime (+ i 1)))
        (assert (not (and (>= i_prime 0) (<= i_prime n))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6209 regression: disjunctive loop cond counterexample must be SAT"
    );
}

/// Implication loop condition via vacuous truth: NOT(n > 0) OR (i < n).
/// Counterexample: i=0, n=0, i_prime=1.
#[test]
#[timeout(10_000)]
fn test_lia_implication_cond_sat_6209() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const n Int)
        (declare-const i_prime Int)
        (assert (>= i 0))
        (assert (<= i n))
        (assert (or (not (> n 0)) (< i n)))
        (assert (= i_prime (+ i 1)))
        (assert (not (and (>= i_prime 0) (<= i_prime n))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6209 regression: implication cond counterexample must be SAT"
    );
}

/// Step-2 increment: i_prime = i + 2 can overrun i <= n.
/// Counterexample: i=1, n=2, i_prime=3.
#[test]
#[timeout(10_000)]
fn test_lia_step2_cond_sat_6209() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const n Int)
        (declare-const i_prime Int)
        (assert (>= n 2))
        (assert (>= i 0))
        (assert (<= i n))
        (assert (< i n))
        (assert (= i_prime (+ i 2)))
        (assert (not (and (>= i_prime 0) (<= i_prime n))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6209 regression: step-2 overrun counterexample must be SAT"
    );
}

/// Body-break step-2 without n >= 2 precondition.
/// Counterexample: i=0, n=1, i_prime=2.
#[test]
#[timeout(10_000)]
fn test_lia_body_break_step2_sat_6209() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const n Int)
        (declare-const i_prime Int)
        (assert (>= i 0))
        (assert (<= i n))
        (assert (< i n))
        (assert (= i_prime (+ i 2)))
        (assert (not (and (>= i_prime 0) (<= i_prime n))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "#6209 regression: body-break step-2 counterexample must be SAT"
    );
}
