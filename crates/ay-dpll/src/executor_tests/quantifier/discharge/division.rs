// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant- and symbolic-divisor CEGQI coverage.

use super::*;

/// Previously bailed (`Unknown(QuantifierCegqiIncomplete)`: div over a CE
/// variable): `forall x. div(x,2) <= 100` is FALSE (x = 1000 gives 500), so
/// asserting it is UNSAT. With the nonzero-constant-divisor lift, CEGQI
/// refinement instantiates at the counterexample model value and the constant
/// fold decides.
#[test]
fn test_cegqi_constant_divisor_forall_unsat() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (<= (div x 2) 100)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["sat"], "false div-forall accepted");
    assert_eq!(outputs, vec!["unsat"]);
}

/// Valid constant-divisor universal stays decided sat (Euclidean division:
/// `2*(x div 2) <= x` always holds): the CE lemma is refuted outright.
#[test]
fn test_cegqi_constant_divisor_valid_forall_sat() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (<= (* 2 (div x 2)) x)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "valid div-forall refuted");
}

/// SYMBOLIC divisors keep the bail (fail closed): `forall x. div(x,d) <= 100`
/// with `d > 0` is genuinely UNSAT, but the honest bounded verdict is unknown.
#[test]
#[ntest::timeout(20_000)]
fn test_cegqi_symbolic_divisor_stays_fail_closed() {
    let input = r#"
        (set-logic LIA)
        (declare-fun d () Int)
        (assert (> d 0))
        (assert (forall ((x Int)) (<= (div x d) 100)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown"]);
}

/// `rem` shares the symbolic-divisor incompleteness boundary with `div` and
/// `mod` and must not enter the widened NIA route.
#[test]
#[ntest::timeout(20_000)]
fn test_cegqi_symbolic_remainder_stays_fail_closed() {
    let input = r#"
        (set-logic LIA)
        (declare-fun d () Int)
        (assert (> d 1))
        (assert (forall ((x Int)) (= (rem x d) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown"]);
}

/// `mod` is the third integer quotient/remainder spelling and must share the
/// same semantic liveness gate.
#[test]
#[ntest::timeout(20_000)]
fn test_cegqi_symbolic_modulus_stays_fail_closed() {
    let input = r#"
        (set-logic LIA)
        (declare-fun d () Int)
        (assert (> d 1))
        (assert (forall ((x Int)) (= (mod x d) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown"]);
}

/// A live UF widens the post-quantifier route to QF_UFNIA. The guard is tied
/// to the unsupported operation, not one particular widened category.
#[test]
#[ntest::timeout(20_000)]
fn test_cegqi_uflia_symbolic_divisor_stays_fail_closed() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun d () Int)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (> d 0))
        (assert (forall ((x Int)) (<= (div x d) (f 0))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown"]);
}

/// Division by literal zero keeps the #57 underspecified semantics.
#[test]
fn test_cegqi_zero_divisor_keeps_57_semantics() {
    let input = r#"
        (set-logic UFNIA)
        (declare-const v Int)
        (assert (= v (div v 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "underspecified div-by-zero refuted");
}
