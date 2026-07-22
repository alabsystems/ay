// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_uflra_simple_sat() {
    // Combine UF and LRA: f(x) = y, x >= 0
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-fun f (Real) Real)
        (assert (= (f x) y))
        (assert (>= x 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_uflra_function_equality_unsat() {
    // f(x) = 5.0, f(x) = 6.0 is contradictory
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (assert (= (f x) 5.0))
        (assert (= (f x) 6.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflra_congruence_with_arithmetic() {
    // Test EUF congruence with arithmetic on the same function application
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (assert (>= (f x) 10.0))
        (assert (< (f x) 5.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // f(x) >= 10 and f(x) < 5 is a contradiction
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflra_arithmetic_sat() {
    // Pure arithmetic constraints in UFLRA logic
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 6.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_uflra_combined_sat() {
    // Combination of UF equality and separate arithmetic constraints
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const a Real)
        (declare-const b Real)
        (declare-fun f (Real) Real)
        (assert (>= a 0.0))
        (assert (<= b 10.0))
        (assert (= (f a) (f b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// QF_AUFLIA (Arrays + Uninterpreted Functions + Linear Integer Arithmetic) Tests
