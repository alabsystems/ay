// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Quantifier regressions for #7150: nested triggers, multi-triggers, and
//! interleaving E-matching with arithmetic refinement.

use ntest::timeout;

fn assert_sat_or_unknown(outputs: &[String], label: &str) {
    assert!(
        outputs.len() == 1 && (outputs[0] == "sat" || outputs[0] == "unknown"),
        "{label}: expected sat or unknown, got: {outputs:?}"
    );
}

/// Simple UF E-matching on a ground application.
#[test]
#[timeout(60000)]
fn test_quantifier_simple_ematching_ground_term_7150() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (> (f x) 0)))
        (assert (> (f 5) 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_sat_or_unknown(&outputs, "simple E-matching ground term");
}

/// Nested trigger `f(g(x), y)` must match the corresponding depth-2 ground term.
#[test]
#[timeout(60000)]
fn test_quantifier_depth2_nested_trigger_unsat_7150() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int) (y Int))
            (! (p (f (g x) y))
               :pattern ((f (g x) y)))))
        (assert (not (p (f (g 5) 0))))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Multi-triggers require all trigger terms to match with a consistent binding.
#[test]
#[timeout(60000)]
fn test_quantifier_multi_trigger_unsat_7150() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun p (S S) Bool)
        (declare-const a S)
        (declare-const b S)
        (assert (forall ((x S) (y S))
            (! (p (f x) (g y))
               :pattern ((f x) (g y)))))
        (assert (not (p (f a) (g b))))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Triggerless arithmetic refinement can introduce a new ground `f(6)` term that
/// must immediately drive a triggered E-matching round on the same check-sat call.
#[test]
#[timeout(60000)]
fn test_quantifier_cegqi_then_ematching_unsat_7150() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int))
            (! (=> (> (f x) 0) (= (g x) 1))
               :pattern ((f x)))))
        (assert (forall ((y Int))
            (=> (> y 5) (> (f y) 0))))
        (assert (not (= (g 6) 1)))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Exists witness search over arithmetic should still find a satisfying value.
#[test]
#[timeout(60000)]
fn test_quantifier_cegqi_exists_witness_sat_7150() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (and (> x 5) (< x 10))))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}
