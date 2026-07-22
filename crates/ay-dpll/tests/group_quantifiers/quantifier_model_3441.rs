// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for quantifier model correctness (#3441).
//!
//! After HBR disable (ay#3424 Tarjan soundness fix), ay returned SAT for
//! formulas containing universally quantified constraints that the model
//! violated. The root cause: triggerless forall quantifiers (equality-only
//! bodies where `=` is a builtin, so no E-matching trigger is extracted)
//! were handled exclusively by CEGQI, which returned Unknown without
//! refinement. Combined with mixed forall+exists CEGQI forcing Unknown
//! for ALL results (including genuine UNSAT from enumerative instantiation).
//!
//! Fix: (1) Run enumerative instantiation for ALL triggerless quantifiers
//! (not just non-CEGQI ones), providing direct ground instances.
//! (2) Re-verify UNSAT in mixed CEGQI case instead of forcing Unknown.

use ntest::timeout;

/// Core regression: forall a. NOT(= a i_prime) is false when a = i_prime.
/// Formula with exists + forall + ground assertion.
/// Previously returned SAT (unsound), then Unknown (incomplete).
#[test]
#[timeout(60_000)]
fn test_quantifier_model_forall_equality_unsat_3441() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun i () Int)
        (declare-fun i_prime () Int)
        (assert (exists ((a Int)) (= a i)))
        (assert (= i_prime (+ i 1)))
        (assert (forall ((a Int)) (not (= a i_prime))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Same formula with UFLIA logic.
#[test]
#[timeout(60_000)]
fn test_quantifier_model_forall_equality_unsat_uflia_3441() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun i () Int)
        (declare-fun i_prime () Int)
        (assert (exists ((a Int)) (= a i)))
        (assert (= i_prime (+ i 1)))
        (assert (forall ((a Int)) (not (= a i_prime))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Simpler variant: pure forall without exists.
/// forall a. NOT(= a x) is false for any x (counterexample: a = x).
#[test]
#[timeout(60_000)]
fn test_quantifier_forall_equality_pure_unsat_3441() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun x () Int)
        (assert (forall ((a Int)) (not (= a x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// forall a. a > 0 is false (counterexample: a = 0 or a = -1).
/// Tests enumerative instantiation with arithmetic predicates.
#[test]
#[timeout(60_000)]
fn test_quantifier_forall_greater_than_unsat_3441() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun x () Int)
        (assert (= x 0))
        (assert (forall ((a Int)) (> a x)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // x = 0, forall a. a > 0 is false (a = 0 is not > 0)
    assert_eq!(outputs, vec!["unsat"]);
}

/// Valid forall should still be SAT: forall a. (a = a) is trivially true.
#[test]
#[timeout(60_000)]
fn test_quantifier_forall_reflexive_sat_3441() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun x () Int)
        (assert (= x 5))
        (assert (forall ((a Int)) (= a a)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // forall a. a = a is trivially true, x = 5 is satisfiable
    // Accept sat or unknown (unknown is safe for incomplete handling)
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got {outputs:?}",
    );
}
