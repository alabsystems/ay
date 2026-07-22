// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for QF_LIA check-sat-assuming preprocessing parity (#6728).
//!
//! Exercises formula shapes that require full LIA preprocessing (FlattenAnd,
//! VariableSubstitution, NormalizeArithSom, ITE lifting, mod/div elimination)
//! under the check-sat-assuming path. Before #6728, QfLia assumptions routed
//! through the AUFLIA combiner which only applied ITE lifting and mod/div.

use ntest::timeout;

/// Variable substitution: assertion provides `x = y + 1`, assumption uses `x`.
/// Without VariableSubstitution on the assumption path, the solver may not
/// propagate the equality and could return Unknown instead of Sat.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_var_substitution_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (assert (= x (+ y 1)))
        (assert (= p (> x 0)))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // Must be sat: y >= 0 makes x = y+1 > 0.
    assert!(
        result.trim() == "sat",
        "Expected sat for var-substitution shape, got: {result}"
    );
}

/// Variable substitution with UNSAT: assumption contradicts the substitution.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_var_substitution_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (= x (+ y 1)))
        (assert (= p (> x 5)))
        (assert (= q (<= y 3)))
        (check-sat-assuming (p q))
    "#;
    let result = crate::common::solve(smt);
    // x = y+1, x > 5 => y > 4, but y <= 3 => contradiction.
    assert!(
        result.trim() == "unsat",
        "Expected unsat for var-substitution contradiction, got: {result}"
    );
}

/// Mod/div under assumptions: assumption references a mod expression.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_mod_div_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const p Bool)
        (assert (= p (= (mod x 3) 0)))
        (assert (>= x 0))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // x = 0, 3, 6, ... all satisfy (mod x 3) = 0 with x >= 0.
    assert!(
        result.trim() == "sat",
        "Expected sat for mod-under-assumption, got: {result}"
    );
}

/// Mod/div UNSAT under assumptions.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_mod_div_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (= p (= (mod x 2) 0)))
        (assert (= q (= (mod x 2) 1)))
        (check-sat-assuming (p q))
    "#;
    let result = crate::common::solve(smt);
    // (mod x 2) can't be both 0 and 1.
    assert!(
        result.trim() == "unsat",
        "Expected unsat for mod contradiction under assumptions, got: {result}"
    );
}

/// SOM normalization under assumptions: `(* 2 (+ x y))` should distribute.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_som_normalization_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (assert (= p (= (* 2 (+ x y)) 10)))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // x + y = 5, many solutions.
    assert!(
        result.trim() == "sat",
        "Expected sat for SOM normalization shape, got: {result}"
    );
}

/// ITE lifting under assumptions.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_ite_lifting_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (assert (= p (> (ite (> x 0) x (- x)) y)))
        (assert (<= y 0))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // |x| > y where y <= 0 — any nonzero x works.
    assert!(
        result.trim() == "sat",
        "Expected sat for ITE-lifting shape, got: {result}"
    );
}

/// Combined: variable substitution + mod/div under check-sat-assuming.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_combined_subst_mod_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const p Bool)
        (assert (= x (* 2 y)))
        (assert (= p (= (mod x 2) 0)))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // x = 2*y is always even, so (mod x 2) = 0.
    assert!(
        result.trim() == "sat",
        "Expected sat for combined subst+mod shape, got: {result}"
    );
}

/// Basic check-sat-assuming SAT sanity (trivial case).
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_basic_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const p Bool)
        (assert (= p (> x 0)))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    assert!(
        result.trim() == "sat",
        "Expected sat for basic assumption, got: {result}"
    );
}

/// Basic check-sat-assuming UNSAT sanity.
#[test]
#[timeout(60_000)]
fn test_qf_lia_assume_basic_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (= p (> x 0)))
        (assert (= q (< x 0)))
        (assert (= x 0))
        (check-sat-assuming (p))
    "#;
    let result = crate::common::solve(smt);
    // x = 0 but p requires x > 0.
    assert!(
        result.trim() == "unsat",
        "Expected unsat for basic assumption contradiction, got: {result}"
    );
}
