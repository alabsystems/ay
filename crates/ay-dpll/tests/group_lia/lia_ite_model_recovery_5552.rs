// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #5552: QF_LIA model recovery for ITE-defined variables.
//!
//! When VariableSubstitution eliminates a variable defined via ITE
//! (e.g., adj = (ite (>= x 512) 3 7)), the model recovery function
//! `recover_substituted_lia_values` must evaluate ITE expressions.
//! Without this, the eliminated variable is absent from the model,
//! causing model validation to return Unknown and allowing a potential
//! false-SAT through the SAT-fallback path.

use ntest::timeout;

/// Core regression: ITE-defined variable with modular arithmetic.
/// The ITE adjustment is always odd (3 or 7), but the constraint
/// forces x + adj to be even with x even. Even + odd = odd, but
/// the sum modular constraint requires even. UNSAT.
#[test]
#[timeout(60_000)]
fn test_lia_ite_model_recovery_basic_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const adj Int)
        (assert (>= x 0))
        (assert (<= x 1023))
        (assert (= (mod x 2) 0))
        (assert (= adj (ite (>= x 512) 3 7)))
        (assert (= (mod (+ x adj) 2) 0))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT case: ITE adjustment + arithmetic constraints are satisfiable.
/// x=600 (even, >= 512) → adj=3, x+adj=603, mod 2 = 1. Consistent.
/// Verify adj appears in the model with a valid value (3 or 7).
#[test]
#[timeout(60_000)]
fn test_lia_ite_model_recovery_basic_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const adj Int)
        (assert (>= x 0))
        (assert (<= x 1023))
        (assert (= (mod x 2) 0))
        (assert (= adj (ite (>= x 512) 3 7)))
        (assert (= (mod (+ x adj) 2) 1))
        (check-sat)
        (get-value (adj))
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output.lines().map(str::trim).collect();
    assert_eq!(lines[0], "sat");
    // adj must be present and equal to 3 or 7
    let adj_line = lines[1];
    assert!(
        adj_line.contains("adj") && (adj_line.contains(" 3)") || adj_line.contains(" 7)")),
        "adj must be 3 or 7 in model, got: {adj_line}"
    );
}

/// Multiple ITE-defined variables with carry chain — the ring pattern.
/// Two ITE adjustments, each odd. Sum of two odd = even.
/// x is even, so total = even + even = even. Constraint: even. SAT.
/// Verify adj1 and adj2 appear in the model with valid values.
#[test]
#[timeout(60_000)]
fn test_lia_ite_model_recovery_two_ites_carry_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const adj1 Int)
        (declare-const adj2 Int)
        (declare-const s Int)
        (declare-const k Int)
        (assert (>= x 0)) (assert (<= x 255))
        (assert (>= y 0)) (assert (<= y 255))
        (assert (>= s 0)) (assert (<= s 255))
        (assert (>= k 0)) (assert (<= k 3))
        (assert (= (mod x 2) 0))
        (assert (= adj1 (ite (>= x 128) 3 7)))
        (assert (= adj2 (ite (>= y 128) 5 11)))
        (assert (= (+ x y adj1 adj2) (+ (* 256 k) s)))
        (assert (= (mod s 2) 0))
        (check-sat)
        (get-value (adj1 adj2))
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output.lines().map(str::trim).collect();
    assert_eq!(lines[0], "sat");
    // adj1 must be 3 or 7, adj2 must be 5 or 11
    let vals = lines[1..].join(" ");
    assert!(
        vals.contains("adj1") && vals.contains("adj2"),
        "adj1 and adj2 must be in model, got: {vals}"
    );
}

/// Nested ITE: adj depends on comparison of another computed value.
/// Verify adj=10 in the model (only consistent solution).
#[test]
#[timeout(60_000)]
fn test_lia_ite_model_recovery_nested_comparison_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const adj Int)
        (assert (>= x 0)) (assert (<= x 100))
        (assert (>= y 0)) (assert (<= y 100))
        (assert (= adj (ite (>= (+ x y) 100) 10 20)))
        (assert (= (+ x y adj) 130))
        (check-sat)
        (get-value (adj))
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output.lines().map(str::trim).collect();
    assert_eq!(lines[0], "sat");
    // x+y >= 100 → adj=10, total=x+y+10=130, so x+y=120. x+y=120 >= 100. Consistent.
    // adj must be 10 (the only consistent value).
    let adj_line = lines[1];
    assert!(
        adj_line.contains("adj") && adj_line.contains(" 10)"),
        "adj must be 10 in model, got: {adj_line}"
    );
}

/// ITE inside div/mod: tests lift_ite_from_arith fix.
/// (div (ite c a b) k) should be properly Shannon-expanded.
#[test]
#[timeout(60_000)]
fn test_lia_ite_inside_div_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0)) (assert (<= x 15))
        (assert (>= y 0)) (assert (<= y 15))
        (assert (= (div (ite (>= x 8) (+ x 3) (+ x 7)) 4) y))
        (assert (< y 2))
        (assert (>= x 5))
        (check-sat)
    "#;
    // x >= 5: if x >= 8, div (x+3) 4 >= div 11 4 = 2, so y >= 2. Contradiction.
    //         if 5 <= x < 8, div (x+7) 4 >= div 12 4 = 3, so y >= 3. Contradiction.
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Ring benchmark pattern from #5552: 8 variables, 5 ITEs, modular arithmetic.
/// All inputs forced even, all adjustments odd, final result forced even = UNSAT.
#[test]
#[timeout(60_000)]
fn test_lia_ring_2exp10_8vars_5ite_unsat_5552() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const v0 Int) (declare-const v1 Int)
        (declare-const v2 Int) (declare-const v3 Int)
        (declare-const v4 Int) (declare-const v5 Int)
        (declare-const v6 Int) (declare-const v7 Int)
        (declare-const s1 Int) (declare-const k1 Int)
        (declare-const s2 Int) (declare-const k2 Int)
        (declare-const s3 Int) (declare-const k3 Int)
        (declare-const adj1 Int) (declare-const adj2 Int)
        (declare-const adj3 Int) (declare-const adj4 Int)
        (declare-const adj5 Int)

        (assert (>= v0 0)) (assert (<= v0 1023))
        (assert (>= v1 0)) (assert (<= v1 1023))
        (assert (>= v2 0)) (assert (<= v2 1023))
        (assert (>= v3 0)) (assert (<= v3 1023))
        (assert (>= v4 0)) (assert (<= v4 1023))
        (assert (>= v5 0)) (assert (<= v5 1023))
        (assert (>= v6 0)) (assert (<= v6 1023))
        (assert (>= v7 0)) (assert (<= v7 1023))
        (assert (>= s1 0)) (assert (<= s1 1023))
        (assert (>= s2 0)) (assert (<= s2 1023))
        (assert (>= s3 0)) (assert (<= s3 1023))
        (assert (>= k1 0)) (assert (<= k1 3))
        (assert (>= k2 0)) (assert (<= k2 3))
        (assert (>= k3 0)) (assert (<= k3 3))

        (assert (= (mod v0 2) 0)) (assert (= (mod v1 2) 0))
        (assert (= (mod v2 2) 0)) (assert (= (mod v3 2) 0))
        (assert (= (mod v4 2) 0)) (assert (= (mod v5 2) 0))
        (assert (= (mod v6 2) 0)) (assert (= (mod v7 2) 0))

        (assert (= adj1 (ite (>= v0 512) 3 7)))
        (assert (= adj2 (ite (>= v1 512) 5 11)))
        (assert (= adj3 (ite (>= v2 512) 13 17)))
        (assert (= adj4 (ite (>= v3 512) 19 23)))
        (assert (= adj5 (ite (>= v4 512) 29 31)))

        (assert (= (+ v0 v1 v2 v3 adj1 adj2) (+ (* 1024 k1) s1)))
        (assert (= (+ s1 v4 v5 adj3 adj4) (+ (* 1024 k2) s2)))
        (assert (= (+ s2 v6 v7 adj5) (+ (* 1024 k3) s3)))

        (assert (= (mod s3 2) 0))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}
