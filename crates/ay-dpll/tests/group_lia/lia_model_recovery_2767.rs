// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for LIA model recovery after variable substitution (#2767).
//!
//! When `VariableSubstitution` eliminates variables (e.g., `result_a -> self_a + 1`),
//! `recover_substituted_lia_values` must compute correct model values for the eliminated
//! variables. These tests verify the model is consistent with all original assertions.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect()
}

fn get_int_binding(line: &str, name: &str) -> Option<i64> {
    let needle = format!("({name} ");
    let start = line.find(&needle)? + needle.len();
    let rest = &line[start..];

    if let Some(neg_body) = rest.strip_prefix("(- ") {
        let end = neg_body.find(')')?;
        let abs: i64 = neg_body[..end].trim().parse().ok()?;
        Some(-abs)
    } else {
        let end = rest.find(')')?;
        rest[..end].trim().parse().ok()
    }
}

/// Model recovery for simple equality substitution.
/// After SAT with `result_a = self_a + 1`, get-value on result_a must return self_a + 1.
#[test]
#[timeout(10_000)]
fn test_model_recovery_simple_equality() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const self_a Int)
        (declare-const result_a Int)

        (assert (= self_a 5))
        (assert (= result_a (+ self_a 1)))

        (check-sat)
        (get-value (self_a result_a))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(get_int_binding(lines[1], "self_a"), Some(5));
    assert_eq!(get_int_binding(lines[1], "result_a"), Some(6));
}

/// Model recovery for transitive equality chain.
/// a = 1, b = a + 1, c = b + 1 => c should be 3.
#[test]
#[timeout(10_000)]
fn test_model_recovery_transitive_chain() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)

        (assert (= a 1))
        (assert (= b (+ a 1)))
        (assert (= c (+ b 1)))

        (check-sat)
        (get-value (a b c))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(get_int_binding(lines[1], "a"), Some(1));
    assert_eq!(get_int_binding(lines[1], "b"), Some(2));
    assert_eq!(get_int_binding(lines[1], "c"), Some(3));
}

/// Model recovery with multiplication in substitution expression.
/// x = 3, y = x * 2 => y should be 6.
#[test]
#[timeout(10_000)]
fn test_model_recovery_with_multiplication() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (= x 3))
        (assert (= y (* x 2)))

        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(get_int_binding(lines[1], "x"), Some(3));
    assert_eq!(get_int_binding(lines[1], "y"), Some(6));
}

/// Model recovery with negation in substitution expression.
/// x = 5, y = -x => y should be -5.
#[test]
#[timeout(10_000)]
fn test_model_recovery_with_negation() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (= x 5))
        (assert (= y (- x)))

        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    assert_eq!(get_int_binding(lines[1], "x"), Some(5));
    assert_eq!(get_int_binding(lines[1], "y"), Some(-5));
}

/// Correctness check: model from equality chain satisfies original constraints.
/// Tests the complete pipeline: substitution, solve, recovery, model verification.
#[test]
#[timeout(10_000)]
fn test_model_recovery_correctness_check() {
    // This test checks that the model values returned after substitution recovery
    // actually satisfy all original assertions. We use get-value to extract the model
    // and verify consistency.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)

        (assert (>= a 0))
        (assert (<= a 10))
        (assert (= b (+ a 3)))
        (assert (= c (- b 1)))

        (check-sat)
        (get-value (a b c))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let a = get_int_binding(lines[1], "a").expect("missing a binding");
    let b = get_int_binding(lines[1], "b").expect("missing b binding");
    let c = get_int_binding(lines[1], "c").expect("missing c binding");

    assert!((0..=10).contains(&a));
    assert_eq!(b, a + 3);
    assert_eq!(c, b - 1);
}

/// Regression for #6698: standalone incremental LIA must reconstruct the
/// transitive-equality chain before minimization and final validation.
#[test]
#[timeout(10_000)]
fn test_model_recovery_transitive_equality_compatible_bounds_6698() {
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
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");

    let a = get_int_binding(lines[1], "a").expect("missing a binding");
    let b = get_int_binding(lines[1], "b").expect("missing b binding");
    let c = get_int_binding(lines[1], "c").expect("missing c binding");

    assert_eq!(a, b, "model must satisfy (= a b): a={a}, b={b}");
    assert_eq!(b, c, "model must satisfy (= c a): b={b}, c={c}");
    assert!(c > 5, "model must satisfy (> c 5): c={c}");
    assert!(b < 10, "model must satisfy (< b 10): b={b}");
}

/// Model recovery with `div` in substitution expression.
/// `x = 10, y = (div x 3)` => y should be 3 (Euclidean division).
/// Regression test for #2779.
#[test]
#[timeout(10_000)]
fn test_model_recovery_with_div() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (= x 10))
        (assert (= y (div x 3)))

        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let x = get_int_binding(lines[1], "x").expect("missing x binding");
    let y = get_int_binding(lines[1], "y").expect("missing y binding");
    assert_eq!(x, 10);
    assert_eq!(y, 3);
}

/// Model recovery with `mod` in substitution expression.
/// `x = 10, y = (mod x 3)` => y should be 1.
/// Regression test for #2779.
#[test]
#[timeout(10_000)]
fn test_model_recovery_with_mod() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (= x 10))
        (assert (= y (mod x 3)))

        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let x = get_int_binding(lines[1], "x").expect("missing x binding");
    let y = get_int_binding(lines[1], "y").expect("missing y binding");
    assert_eq!(x, 10);
    assert_eq!(y, 1);
}

/// Model recovery with `abs` in substitution expression.
/// `x = -7, y = (abs x)` => y should be 7.
#[test]
#[timeout(10_000)]
fn test_model_recovery_with_abs() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (= x (- 7)))
        (assert (= y (abs x)))

        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let x = get_int_binding(lines[1], "x").expect("missing x binding");
    let y = get_int_binding(lines[1], "y").expect("missing y binding");
    assert_eq!(x, -7);
    assert_eq!(y, 7);
}

/// Model recovery for a deep chain of 8 equalities.
/// Tests near the 10-pass boundary of recover_substituted_lia_values.
/// v0 = 1, v1 = v0+1, v2 = v1+1, ..., v7 = v6+1 => v7 = 8
#[test]
#[timeout(10_000)]
fn test_model_recovery_deep_chain_8() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const v0 Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (declare-const v3 Int)
        (declare-const v4 Int)
        (declare-const v5 Int)
        (declare-const v6 Int)
        (declare-const v7 Int)

        (assert (= v0 1))
        (assert (= v1 (+ v0 1)))
        (assert (= v2 (+ v1 1)))
        (assert (= v3 (+ v2 1)))
        (assert (= v4 (+ v3 1)))
        (assert (= v5 (+ v4 1)))
        (assert (= v6 (+ v5 1)))
        (assert (= v7 (+ v6 1)))

        (check-sat)
        (get-value (v0 v1 v2 v3 v4 v5 v6 v7))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    for (i, name) in ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]
        .iter()
        .enumerate()
    {
        let val =
            get_int_binding(lines[1], name).unwrap_or_else(|| panic!("missing {name} binding"));
        assert_eq!(val, (i as i64) + 1, "wrong value for {name}");
    }
}

/// Model recovery for a deep chain of 50 substitution links.
/// a0 = 1, a1 = a0+1, ..., a50 = a49+1 => a50 = 51
/// Regression test for #2779 (chain depth limit was 10).
#[test]
#[timeout(30_000)]
fn test_model_recovery_deep_chain_50() {
    let mut smt = String::from("(set-logic QF_LIA)\n");
    for i in 0..=50 {
        smt.push_str(&format!("(declare-const a{i} Int)\n"));
    }
    smt.push_str("(assert (= a0 1))\n");
    for i in 1..=50 {
        smt.push_str(&format!("(assert (= a{i} (+ a{} 1)))\n", i - 1));
    }
    smt.push_str("(check-sat)\n(get-value (a50))\n");

    let output = crate::common::solve(&smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let a50 = get_int_binding(lines[1], "a50").expect("missing a50 binding");
    assert_eq!(a50, 51);
}

/// Model recovery with negative div/mod operands.
/// SMT-LIB: (div -7 2) = -4, (mod -7 2) = 1
/// Regression test for #2779.
#[test]
#[timeout(10_000)]
fn test_model_recovery_div_mod_negative() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const d Int)
        (declare-const m Int)

        (assert (= x (- 7)))
        (assert (= d (div x 2)))
        (assert (= m (mod x 2)))

        (check-sat)
        (get-value (x d m))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let x = get_int_binding(lines[1], "x").expect("missing x binding");
    let d = get_int_binding(lines[1], "d").expect("missing d binding");
    let m = get_int_binding(lines[1], "m").expect("missing m binding");
    assert_eq!(x, -7);
    // SMT-LIB: (div -7 2) = -4 (floor division)
    assert_eq!(d, -4);
    // SMT-LIB: (mod -7 2) = 1 (always non-negative)
    assert_eq!(m, 1);
}

/// Model recovery with negative divisor in div/mod.
/// SMT-LIB: (div 7 (- 3)) = -2, (mod 7 (- 3)) = 1
/// Tests the smtlib_div branch for d < 0 which was previously untested.
#[test]
#[timeout(10_000)]
fn test_model_recovery_div_mod_negative_divisor() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const d Int)
        (declare-const m Int)

        (assert (= x 7))
        (assert (= d (div x (- 3))))
        (assert (= m (mod x (- 3))))

        (check-sat)
        (get-value (x d m))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat");
    let x = get_int_binding(lines[1], "x").expect("missing x binding");
    let d = get_int_binding(lines[1], "d").expect("missing d binding");
    let m = get_int_binding(lines[1], "m").expect("missing m binding");
    assert_eq!(x, 7);
    // SMT-LIB: (div 7 (- 3)) = -(div 7 3) = -(floor(7/3)) = -2
    assert_eq!(d, -2);
    // SMT-LIB: (mod 7 (- 3)) = 7 - (-3) * (div 7 (- 3)) = 7 - (-3)*(-2) = 7 - 6 = 1
    assert_eq!(m, 1);
}
