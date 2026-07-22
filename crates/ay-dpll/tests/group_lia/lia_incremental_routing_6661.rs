// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Routing regressions for #6661: LIA standalone incremental handles all
//! formula shapes (mod/div, equality-substitution) without falling back to the
//! legacy split-loop pipeline.

use ntest::timeout;

/// `(mod x 3)` — previously guarded to the legacy path in incremental mode.
/// Now handled by `solve_lia_standalone_incremental()` via `preprocess_lia()`.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_mod_routes_incremental_6661() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const x Int)
        (assert (= (mod x 3) 2))
        (assert (>= x 0))
        (assert (<= x 20))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    // Model value must satisfy (mod x 3) = 2, i.e. x ≡ 2 (mod 3).
    let val_str = &outputs[1];
    let x_val: i64 = extract_int_value(val_str, "x");
    assert_eq!(
        x_val % 3,
        2,
        "model x={x_val} does not satisfy (mod x 3) = 2"
    );
    assert!((0..=20).contains(&x_val), "model x={x_val} out of [0, 20]");
}

/// `(div x 5)` — same guard as mod; must route through incremental.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_div_routes_incremental_6661() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const x Int)
        (assert (= (div x 5) 3))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    // (div x 5) = 3 means x ∈ [15, 19] (SMT-LIB Euclidean division).
    let x_val: i64 = extract_int_value(&outputs[1], "x");
    assert!(
        (15..=19).contains(&x_val),
        "model x={x_val} does not satisfy (div x 5) = 3, expected x ∈ [15, 19]"
    );
}

/// UNSAT mod/div case: `(mod x 2) = 0` AND `(mod x 2) = 1` is contradictory.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_mod_unsat_6661() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 2) 0))
        (assert (= (mod x 2) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Equality-substitution: `(= y (+ x 1))` — previously guarded because
/// `has_int_real_equality_substitution()` detected it.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_eq_subst_routes_incremental_6661() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (assert (>= x 5))
        (assert (<= x 10))
        (check-sat)
        (get-value (x y))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let x_val = extract_int_value(&outputs[1], "x");
    let y_val = extract_int_value(&outputs[1], "y");
    assert_eq!(
        y_val,
        x_val + 1,
        "model y={y_val} != x+1={} (x={x_val})",
        x_val + 1
    );
    assert!((5..=10).contains(&x_val), "model x={x_val} out of [5, 10]");
}

/// #6698 regression: transitive equality chain with asymmetric bounds.
///
/// `a=b, c=a, c>5, b<10` — after variable substitution eliminates `b` and `c`,
/// the minimizer must not corrupt model values against the preprocessed formula
/// (which no longer constrains the eliminated variables).
///
/// The zone branch removed the guards without deferring minimization and
/// silently produced invalid models. This test checks actual model values.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_transitive_eq_model_6698() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
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
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat", "expected sat, got: {outputs:?}");

    let a_val = extract_int_value(&outputs[1], "a");
    let b_val = extract_int_value(&outputs[1], "b");
    let c_val = extract_int_value(&outputs[1], "c");

    // a = b
    assert_eq!(a_val, b_val, "model a={a_val} != b={b_val}");
    // c = a
    assert_eq!(c_val, a_val, "model c={c_val} != a={a_val}");
    // c > 5
    assert!(c_val > 5, "model c={c_val} not > 5");
    // b < 10
    assert!(b_val < 10, "model b={b_val} not < 10");
}

/// Combined mod/div + equality-substitution: both guards fire simultaneously.
#[test]
#[timeout(60_000)]
fn test_lia_standalone_mod_and_eq_subst_combined_6661() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-models true)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (assert (= (mod x 3) 0))
        (assert (>= x 0))
        (assert (<= x 20))
        (check-sat)
        (get-value (x y))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let x_val = extract_int_value(&outputs[1], "x");
    let y_val = extract_int_value(&outputs[1], "y");
    assert_eq!(x_val % 3, 0, "model x={x_val} not divisible by 3");
    assert_eq!(y_val, x_val + 1, "model y={y_val} != x+1");
    assert!((0..=20).contains(&x_val), "model x={x_val} out of [0, 20]");
}

/// Extract an integer value from get-value output like `((x 7))` or `((x 7) (y 8))`.
fn extract_int_value(output: &str, var: &str) -> i64 {
    // get-value output format: ((var value) ...)
    // Values can be negative: (- 7) or just 7.
    let pattern = format!("({var} ");
    let start = output
        .find(&pattern)
        .unwrap_or_else(|| panic!("variable {var} not found in get-value output: {output}"));
    let rest = &output[start + pattern.len()..];

    // Find the closing paren for this variable's value
    let mut depth = 0i32;
    let mut end = 0;
    for (i, ch) in rest.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                if depth == 0 {
                    end = i;
                    break;
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    let val_str = rest[..end].trim();

    // Handle (- N) format for negative numbers
    if val_str.starts_with("(- ") && val_str.ends_with(')') {
        let inner = val_str[3..val_str.len() - 1].trim();
        -inner
            .parse::<i64>()
            .unwrap_or_else(|e| panic!("cannot parse negative int '{inner}' from '{val_str}': {e}"))
    } else {
        val_str
            .parse::<i64>()
            .unwrap_or_else(|e| panic!("cannot parse int '{val_str}': {e}"))
    }
}
