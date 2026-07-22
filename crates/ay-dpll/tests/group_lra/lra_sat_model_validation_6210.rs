// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests that LRA solver model values satisfy asserted constraints.
//!
//! When check-sat returns sat, (get-value ...) must produce values consistent
//! with all asserted constraints. These tests complement the debug_assert
//! guards proposed in #6210.
//!
//! Part of #6210

use ay_frontend::sexp::{parse_sexp, SExpr};
use ntest::timeout;

/// Extract the string content from a Symbol, Numeral, or Decimal SExpr.
fn sexpr_str(s: &SExpr) -> Option<&str> {
    match s {
        SExpr::Symbol(v) | SExpr::Numeral(v) | SExpr::Decimal(v) => Some(v.as_str()),
        _ => None,
    }
}

/// Parse a single SMT-LIB rational value (integer, decimal, or (/ n d)) to f64.
/// Returns None for unrecognized formats.
fn sexpr_to_f64(s: &SExpr) -> Option<f64> {
    match s {
        SExpr::Numeral(n) => n.parse::<f64>().ok(),
        SExpr::Decimal(d) => d.parse::<f64>().ok(),
        SExpr::List(parts) if parts.len() == 3 => {
            // (/ numerator denominator)
            if sexpr_str(&parts[0]) == Some("/") {
                let n = sexpr_to_f64(&parts[1])?;
                let d = sexpr_to_f64(&parts[2])?;
                return Some(n / d);
            }
            // (- expr expr) shouldn't happen for values, but handle gracefully
            None
        }
        SExpr::List(parts) if parts.len() == 2 => {
            // (- value)
            if sexpr_str(&parts[0]) == Some("-") {
                return sexpr_to_f64(&parts[1]).map(|v| -v);
            }
            None
        }
        _ => None,
    }
}

/// Extract named variable value from get-value output line.
/// Parses `((name value) ...)` and returns the f64 value for the given name.
fn extract_value(output: &str, var_name: &str) -> f64 {
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))
        .unwrap_or_else(|| panic!("missing get-value output in: {output}"));
    let parsed = parse_sexp(value_line).unwrap_or_else(|e| panic!("parse get-value: {e}"));
    let SExpr::List(ref bindings) = parsed else {
        panic!("expected list, got: {parsed:?}");
    };
    for binding in bindings {
        let SExpr::List(ref pair) = binding else {
            continue;
        };
        if pair.len() == 2 {
            if sexpr_str(&pair[0]) == Some(var_name) {
                return sexpr_to_f64(&pair[1])
                    .unwrap_or_else(|| panic!("cannot parse value for {var_name}: {:?}", pair[1]));
            }
        }
    }
    panic!("variable {var_name} not found in get-value output: {value_line}");
}

/// Simple bound: x in [3, 5]. Model value must be in range.
#[test]
#[timeout(10_000)]
fn test_lra_model_within_simple_bounds() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 3.0))
        (assert (<= x 5.0))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");

    let x = extract_value(&output, "x");
    assert!((3.0..=5.0).contains(&x), "x = {x} not in [3, 5]");
}

/// Strict bounds: x in (3, 5). Model value must be strictly in range.
#[test]
#[timeout(10_000)]
fn test_lra_model_strict_bounds() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 3.0))
        (assert (< x 5.0))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");

    let x = extract_value(&output, "x");
    assert!(x > 3.0 && x < 5.0, "x = {x} not in (3, 5)");
}

/// Equality pins value exactly.
#[test]
#[timeout(10_000)]
fn test_lra_model_equality_pinned() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 7.0))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");

    let x = extract_value(&output, "x");
    assert!((x - 7.0).abs() < 1e-9, "x should be exactly 7, got {x}");
}

/// Multi-variable sum constraint: x + y <= 10, x >= 3, y >= 5.
/// Model values must satisfy all three constraints.
#[test]
#[timeout(10_000)]
fn test_lra_model_multi_var_sum() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= (+ x y) 10.0))
        (assert (>= x 3.0))
        (assert (>= y 5.0))
        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");

    let x = extract_value(&output, "x");
    let y = extract_value(&output, "y");
    assert!(x >= 3.0, "x = {x} < 3");
    assert!(y >= 5.0, "y = {y} < 5");
    assert!(x + y <= 10.0 + 1e-9, "x + y = {} > 10", x + y);
}

/// Push/pop + re-assert: model must be valid after scope restoration.
#[test]
#[timeout(10_000)]
fn test_lra_model_after_push_pop_reassert() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 2.0))

        (push 1)
        (assert (<= x 8.0))
        (check-sat)
        (get-value (x))
        (pop 1)

        (assert (<= x 8.0))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    // Both check-sat should return sat
    let sats: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect();
    assert_eq!(sats, vec!["sat", "sat"]);

    // Both get-value outputs should show x in [2, 8]
    let value_lines: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|l| l.starts_with("(("))
        .collect();
    assert_eq!(
        value_lines.len(),
        2,
        "expected 2 get-value outputs, got {}",
        value_lines.len()
    );
    for (i, line) in value_lines.iter().enumerate() {
        let parsed = parse_sexp(line).unwrap_or_else(|e| panic!("parse get-value [{i}]: {e}"));
        let SExpr::List(ref bindings) = parsed else {
            panic!("expected list at [{i}], got: {parsed:?}");
        };
        let SExpr::List(ref pair) = bindings[0] else {
            panic!("expected binding pair at [{i}]");
        };
        let x = sexpr_to_f64(&pair[1])
            .unwrap_or_else(|| panic!("cannot parse x value at [{i}]: {:?}", pair[1]));
        assert!((2.0..=8.0).contains(&x), "scope {i}: x = {x} not in [2, 8]");
    }
}

/// Tight bounds with propagation: forces the solver to propagate implications.
/// y = x + 1, z = y + 1, z >= 5 implies x >= 3.
#[test]
#[timeout(10_000)]
fn test_lra_propagation_validity_tight_bounds() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        ; Create a chain: x >= 0, y = x + 1, z = y + 1
        ; This forces propagation of bounds through the chain.
        (assert (>= x 0.0))
        (assert (<= x 10.0))
        (assert (= y (+ x 1.0)))
        (assert (= z (+ y 1.0)))
        (assert (>= z 5.0))
        (check-sat)
        (get-value (x y z))
    "#;
    let output = crate::common::solve(smt);
    assert!(output.starts_with("sat"), "Expected sat, got: {output}");

    let x = extract_value(&output, "x");
    let y = extract_value(&output, "y");
    let z = extract_value(&output, "z");

    // Verify chain constraints
    assert!(x >= 0.0, "x = {x} < 0");
    assert!(x <= 10.0, "x = {x} > 10");
    assert!(
        (y - (x + 1.0)).abs() < 1e-9,
        "y = {y} != x + 1 = {}",
        x + 1.0
    );
    assert!(
        (z - (y + 1.0)).abs() < 1e-9,
        "z = {z} != y + 1 = {}",
        y + 1.0
    );
    assert!(z >= 5.0 - 1e-9, "z = {z} < 5");
}
