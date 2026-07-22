// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_NRA soundness gate tests.
//!
//! Consumer: neural-verification-consumer uses QF_NRA for neural network verification
//! (quadratic constraints, ReLU patterns). optimization_consumer uses QF_LRA with nonlinear
//! auto-upgrade to QF_NRA.
//!
//! NRA is an incomplete theory — the solver may return `unknown` on satisfiable
//! formulas. The soundness gate tests focus on:
//! - Must not return `sat` on unsatisfiable formulas
//! - Must not return `unsat` on satisfiable formulas
//! - When `sat` is returned, model must validate
//! - Fully-determined formulas (all vars pinned) exercise SAT model validation

use ntest::timeout;

use super::helpers::{assert_not_sat, assert_not_unsat, assert_sat_validates};

// --- 1. SAT with model validation (fully-determined) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_sat_validates_model() {
    // Fully-determined: all variables are pinned to concrete values.
    // The NRA solver should return SAT and the model must validate.
    assert_sat_validates(
        r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x 2.0))
        (assert (= y 3.0))
        (assert (= (* x y) 6.0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT: nonlinear contradiction (must not return sat) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_unsat_not_sat() {
    // x^2 < 0 is unsatisfiable over reals. Must not return sat.
    assert_not_sat(
        r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (< (* x x) 0.0))
        (check-sat)
    "#,
    );
}

// --- 3. SAT: neural-verification-consumer ReLU linearization pattern ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_relu_pattern() {
    // ReLU linearization: y = max(0, x) encoded as:
    //   y >= 0, y >= x, (y = 0 OR y = x)
    // With x = 3 => y = 3. Fully determined, NRA should find SAT.
    assert_sat_validates(
        r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= y 0.0))
        (assert (>= y x))
        (assert (or (= y 0.0) (= y x)))
        (assert (= x 3.0))
        (assert (= y 3.0))
        (check-sat)
    "#,
    );
}

// --- 4. SAT: nonlinear feasibility (must not return unsat) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_quadratic_not_unsat() {
    // x * x = 4 with x > 0 is satisfiable (x = 2).
    // NRA may return unknown but must not return unsat.
    assert_not_unsat(
        r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 4.0))
        (assert (> x 0.0))
        (check-sat)
    "#,
    );
}

// --- 5. Incremental push/pop scope (fully-determined base) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_incremental_scope() {
    // Use fully-determined base (x = 2, y = 3, x*y = 6) to get SAT.
    // Push contradiction (x*y != 6), expect UNSAT.
    // Pop, expect SAT again.
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x 2.0))
        (assert (= y 3.0))
        (assert (= (* x y) 6.0))
        (check-sat)
        (push 1)
        (assert (not (= (* x y) 6.0)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let commands = ay_frontend::parse(smt).expect("parse");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    let results: Vec<&str> = outputs
        .iter()
        .map(|s| s.trim())
        .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results: {results:?}"
    );
    // First: SAT (fully determined)
    assert_eq!(results[0], "sat", "base scope should be sat: {results:?}");
    // Second: contradiction must be unsat (adding negation of a true ground fact)
    assert_eq!(
        results[1], "unsat",
        "contradicted scope should be unsat: {results:?}"
    );
    // Third: after pop, should be sat again
    assert_eq!(results[2], "sat", "post-pop should be sat: {results:?}");
}

// --- 6. optimization_consumer pattern: must not return unsat on satisfiable nonlinear ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_nra_optimization_consumer_not_false_unsat() {
    // optimization_consumer pattern: declared QF_NRA, uses multiplication.
    // Must not return false-unsat.
    assert_not_unsat(
        r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (* x y) 12.0))
        (assert (= x 3.0))
        (assert (= y 4.0))
        (check-sat)
    "#,
    );
}
