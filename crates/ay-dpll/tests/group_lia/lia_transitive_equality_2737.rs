// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for ay#2737: QF_LIA transitive equality timeout.
//!
//! `a=b ∧ c=a ∧ ¬(c=b)` timed out (>30s, returned Unknown)
//! because ay encoded equality as LRA relaxation (`a-b ≤ 0 ∧ a-b ≥ 0`) and the
//! disequality splitting loop exhausted iterations before propagating transitivity.
//!
//! Fixed by: per-atom unsupported tracking (#6167) + disequality split improvements
//! (#4906, #6165).

use ntest::timeout;

/// The exact pattern: a=b, c=a, NOT(c=b).
/// Must be UNSAT by transitive equality: c=a=b, so c=b.
#[test]
#[timeout(10_000)]
fn test_transitive_equality_3var_unsat_2737() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= c a))
        (assert (not (= c b)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// 4-variable transitive chain: a=b, b=c, c=d, NOT(a=d).
#[test]
#[timeout(10_000)]
fn test_transitive_equality_4var_chain_unsat_2737() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (assert (= a b))
        (assert (= b c))
        (assert (= c d))
        (assert (not (= a d)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Transitive equality with bound propagation: a=b, c=a, c>5, b<3.
/// UNSAT because a=b=c, so c>5 contradicts b<3.
#[test]
#[timeout(10_000)]
fn test_transitive_equality_bounds_conflict_2737() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= c a))
        (assert (> c 5))
        (assert (< b 3))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// verification-consumer verification pattern: result binding + postcondition check.
/// `result = (div x y)` ∧ `NOT(result = (div x y))` is trivially UNSAT.
/// This exercises the div-as-opaque-variable path (#6165).
#[test]
#[timeout(10_000)]
fn test_div_result_binding_contradiction_2737() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (= result (div x y)))
        (assert (not (= result (div x y))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT case: transitive equality with compatible bounds.
/// a=b, c=a, c>5, b<10 is satisfiable (e.g., a=b=c=7).
#[test]
#[timeout(10_000)]
fn test_transitive_equality_compatible_bounds_sat_2737() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= c a))
        (assert (> c 5))
        (assert (< b 10))
        (check-sat)
        (get-value (a b c))
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(output[0].trim(), "sat");

    let value_line = &output[1];
    let numbers: Vec<i64> = value_line
        .replace(['(', ')'], " ")
        .split_whitespace()
        .filter_map(|token| token.parse::<i64>().ok())
        .collect();
    assert_eq!(
        numbers.len(),
        3,
        "expected 3 integer bindings, got {value_line}"
    );

    let (a, b, c) = (numbers[0], numbers[1], numbers[2]);
    assert_eq!(a, b, "model must satisfy (= a b): a={a}, b={b}");
    assert_eq!(b, c, "model must satisfy (= c a): b={b}, c={c}");
    assert!(c > 5, "model must satisfy (> c 5): c={c}");
    assert!(b < 10, "model must satisfy (< b 10): b={b}");
}

/// Regression for #6698: transitive equality model must satisfy all assertions.
///
/// The standalone incremental path preprocesses `(= a b), (= c a)` into
/// variable substitution `b -> a, c -> a`, solving only `a > 5 ∧ a < 10`.
/// After SAT, the model must reconstruct b and c from a via the substitution
/// map — NOT from a post-minimization value that violates the equalities.
///
/// This test exercises the full model validation path via `(get-value ...)`.
#[test]
#[timeout(10_000)]
fn test_transitive_equality_model_validation_6698() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a b))
        (assert (= c a))
        (assert (> c 5))
        (assert (< b 10))
        (check-sat)
        (get-value (a b c))
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(output[0].trim(), "sat", "expected sat");

    // Parse the (get-value ...) output and verify a = b = c, c > 5, b < 10.
    let val_line = &output[1];
    // Format: ((a N) (b N) (c N))
    let nums: Vec<i64> = val_line
        .replace(['(', ')'], " ")
        .split_whitespace()
        .filter_map(|tok| tok.parse::<i64>().ok())
        .collect();
    assert_eq!(
        nums.len(),
        3,
        "expected 3 integer values from get-value, got: {val_line}"
    );
    let (a, b, c) = (nums[0], nums[1], nums[2]);
    assert_eq!(a, b, "model must satisfy (= a b): a={a}, b={b}");
    assert_eq!(c, a, "model must satisfy (= c a): c={c}, a={a}");
    assert!(c > 5, "model must satisfy (> c 5): c={c}");
    assert!(b < 10, "model must satisfy (< b 10): b={b}");
}

/// QF_LRA variant: same transitive pattern with real-sorted variables.
#[test]
#[timeout(10_000)]
fn test_transitive_equality_lra_unsat_2737() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (assert (= a b))
        (assert (= c a))
        (assert (not (= c b)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}
