// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for bound axiom injection (#4919).
//!
//! Verifies that Z3-style bound ordering axioms (mk_bound_axioms) are correctly
//! generated and don't cause unsound results. Each axiom is a binary clause
//! encoding a tautological implication between bound atoms on the same variable.
//!
//! Example: for x with atoms `x >= 3` and `x >= 5`:
//!   - (x >= 5) → (x >= 3) encoded as `¬(x >= 5) ∨ (x >= 3)`
//!
//! These axioms move bound propagation from the theory solver (O(n) round-trips)
//! to BCP (O(1) unit propagation), significantly accelerating QF_LIA/QF_LRA.

use ntest::timeout;

/// Basic LIA with multiple bounds: bound axioms should not affect correctness.
/// x >= 3, x >= 5, x <= 10 — SAT (e.g., x=5).
#[test]
#[timeout(10_000)]
fn test_lia_multiple_bounds_sat_4919() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 3))
(assert (>= x 5))
(assert (<= x 10))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Contradictory bounds: x >= 5 and x <= 3 — UNSAT.
/// Bound axioms encode ¬(x >= 5) ∨ ¬(x <= 3) which BCP can use
/// to derive the conflict faster.
#[test]
#[timeout(10_000)]
fn test_lia_contradictory_bounds_unsat_4919() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 5))
(assert (<= x 3))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Integer trichotomy: x >= k+1 or x <= k for all integers.
/// This test forces the solver to use the trichotomy axiom.
/// x = 5 exactly: (>= x 5) and (<= x 5).
#[test]
#[timeout(10_000)]
fn test_lia_trichotomy_exact_4919() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 5))
(assert (<= x 5))
(assert (not (= x 5)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// LRA variant: multiple Real bounds. Bound axioms should work for rationals too.
#[test]
#[timeout(10_000)]
fn test_lra_multiple_bounds_sat_4919() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 1.0))
(assert (>= x 3.5))
(assert (<= x 10.0))
(assert (>= x 2.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Multiple variables with overlapping bounds.
/// Tests that bound axioms are correctly scoped per variable.
#[test]
#[timeout(10_000)]
fn test_lia_multi_var_bounds_4919() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1))
(assert (>= x 5))
(assert (<= x 10))
(assert (>= y 3))
(assert (<= y 7))
; x + y = 12 is satisfiable (e.g., x=5, y=7)
(assert (= (+ x y) 12))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Model validation after bound axiom injection.
/// Ensures the model is correct despite the additional axiom clauses.
#[test]
#[timeout(10_000)]
fn test_lia_bounds_model_correct_4919() {
    let smt = r#"
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(assert (>= x 3))
(assert (>= x 5))
(assert (<= x 10))
(assert (= x 7))
(check-sat)
(get-value (x))
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("7"),
        "Expected x = 7 in get-value, got: {}",
        outputs[1]
    );
}

/// Dense bounds: many bounds on the same variable.
/// Tests that the O(n) axiom generation doesn't blow up.
#[test]
#[timeout(10_000)]
fn test_lia_dense_bounds_4919() {
    // Create 20 lower bounds: x >= 1, x >= 2, ..., x >= 20
    // and 1 upper bound: x <= 25
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n",
    );
    for i in 1..=20 {
        smt.push_str(&format!("(assert (>= x {i}))\n"));
    }
    smt.push_str("(assert (<= x 25))\n");
    smt.push_str("(check-sat)\n");

    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// UFLIA bound axiom forwarding: uninterpreted functions + integer bounds.
/// The bound axiom injection only works if UfLiaSolver forwards
/// sort_atom_index() and generate_bound_axiom_terms() to its inner LIA solver.
/// Without forwarding, these methods return empty/no-op defaults and bound
/// axioms are silently skipped for QF_UFLIA problems.
#[test]
#[timeout(10_000)]
fn test_uflia_bound_axiom_forwarding_4919() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (>= x 1))
(assert (>= x 5))
(assert (<= x 10))
; f(x) = x + 1, which combined with bounds should be satisfiable
(assert (= (f x) (+ x 1)))
(assert (>= (f x) 6))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// UFLIA bound axiom forwarding: contradictory bounds with UF.
/// Ensures the LIA-side bound axioms propagate through the UfLiaSolver adapter.
#[test]
#[timeout(10_000)]
fn test_uflia_bound_axiom_unsat_4919() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (>= x 10))
(assert (<= x 3))
; f(x) is irrelevant — bounds on x are contradictory
(assert (= (f x) 42))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// AUFLIA bound axiom forwarding: arrays + uninterpreted functions + integer bounds.
/// Tests that AufLiaSolver also correctly forwards bound axiom generation.
#[test]
#[timeout(10_000)]
fn test_auflia_bound_axiom_forwarding_4919() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun arr () (Array Int Int))
(declare-const i Int)
(assert (>= i 1))
(assert (>= i 5))
(assert (<= i 10))
(assert (>= (select arr i) 0))
(assert (<= (select arr i) 100))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}
