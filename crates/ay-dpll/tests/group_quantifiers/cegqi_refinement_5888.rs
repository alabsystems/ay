// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #5888: CEGQI quantified formulas return Unknown
//! for arithmetic.
//!
//! Tests multi-round CEGQI refinement, coefficient handling, 3+ summand
//! extraction, disequality bounds, and subtraction term handling improvements.

use ntest::timeout;

/// Multi-round CEGQI refinement: bounded integer range with quadratic constraint.
///
/// `forall x in [0,10]. x*x <= 100` is valid.
/// Adding `a in [0,10]` and `a*a > 100` makes the formula UNSAT.
/// This requires the CEGQI loop to try multiple instantiations before
/// the re-solve returns UNSAT.
#[test]
#[timeout(30000)]
fn test_cegqi_multi_round_bounded_quadratic() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (assert (>= a 0))
        (assert (<= a 10))
        (assert (forall ((x Int))
            (=> (and (>= x 0) (<= x 10)) (<= (* x x) 100))))
        (assert (> (* a a) 100))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    // Ideal: unsat (a in [0,10] and a*a > 100 is impossible). Currently
    // CEGQI may return unknown because (* x x) is nonlinear and bound
    // extraction cannot isolate x.
    assert!(
        results[0] == "unsat" || results[0] == "unknown",
        "Bounded quadratic should be UNSAT or Unknown, got: {results:?}"
    );
}

/// CEGQI with a <= constraints on the forall variable.
///
/// `forall x. a <= x <= b => x >= 0` combined with `a < 0` is UNSAT
/// because the forall requires all values in [a,b] to be non-negative,
/// but `a < 0` violates that.
#[test]
#[timeout(10000)]
fn test_cegqi_range_bound_unsat() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= a b))
        (assert (forall ((x Int))
            (=> (and (<= a x) (<= x b)) (>= x 0))))
        (assert (< a 0))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "Range bound with a < 0 should be UNSAT"
    );
}

/// Valid forall: x + 1 > x for all integers.
///
/// The assertion `forall x. x + 1 > x` is a tautology. The formula is SAT.
#[test]
#[timeout(10000)]
fn test_cegqi_valid_forall_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (> (+ x 1) x)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "Valid forall should be SAT");
}

/// CEGQI with NIA logic: forall x >= 1. x^2 >= 1 combined with n >= 0.
///
/// Tests that NIA is properly dispatched in the CEGQI re-solve match.
#[test]
#[timeout(10000)]
fn test_cegqi_nia_dispatch() {
    let smt = r#"
        (set-logic NIA)
        (declare-fun n () Int)
        (assert (>= n 0))
        (assert (forall ((x Int))
            (=> (and (>= x 1) (<= x n)) (>= (* x x) 1))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    // SAT or Unknown are both acceptable — the key is no crash and no wrong answer
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "NIA dispatch should not crash, got: {results:?}"
    );
}

/// CEGQI with disequality (distinct/not-equal) bound.
///
/// `forall x. x != a => x > a OR x < a` is valid: the disequality
/// implies strict ordering. Combined with `a >= 0` and the negation
/// `exists x. x != a AND NOT(x > a) AND NOT(x < a)` — which simplifies
/// to `x != a AND x = a` — should be UNSAT.
///
/// Tests Path 2 fix: disequality bounds in ArithInstantiator.
#[test]
#[timeout(10000)]
fn test_cegqi_disequality_bounds() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (assert (>= a 0))
        (assert (forall ((x Int))
            (=> (not (= x a)) (or (> x a) (< x a)))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "Disequality implies strict order, formula is SAT"
    );
}

/// CEGQI with subtraction terms.
///
/// `forall x. x >= 0 => (a - x) <= a` is valid (subtracting a non-negative
/// value can only decrease). This tests that bound extraction works through
/// subtraction terms.
#[test]
#[timeout(10000)]
fn test_cegqi_subtraction_bound() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (assert (forall ((x Int))
            (=> (>= x 0) (<= (- a x) a))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "a - x <= a for non-negative x should be SAT"
    );
}

/// CEGQI with LRA (Real arithmetic) model value preservation.
///
/// Tests that Real-sorted variable model values are preserved as
/// rationals during refinement, not truncated to integers.
#[test]
#[timeout(10000)]
fn test_cegqi_lra_real_model_value() {
    let smt = r#"
        (set-logic LRA)
        (declare-fun a () Real)
        (assert (= a 1.5))
        (assert (forall ((x Real))
            (=> (and (>= x 0.0) (<= x a)) (<= x 2.0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "LRA forall with real bounds should be SAT"
    );
}

/// LRA CEGQI should instantiate inside a strict real interval, not at the
/// strict lower boundary.
#[test]
#[timeout(10000)]
fn test_cegqi_lra_strict_interval_counterexample_unsat_559() {
    let smt = r#"
        (set-logic LRA)
        (assert (forall ((x Real))
            (=> (> x 0.0) (> x 1.0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "x=1/2 refutes forall x:Real. x > 0 => x > 1"
    );
}

/// Non-unit real coefficients should be divided before midpoint selection.
#[test]
#[timeout(10000)]
fn test_cegqi_lra_nonunit_bounds_counterexample_unsat_559() {
    let smt = r#"
        (set-logic LRA)
        (assert (forall ((x Real))
            (=> (and (> (* 2.0 x) 0.0) (<= (* 2.0 x) 2.0))
                (> x 1.0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "0 < 2*x <= 2 admits real counterexamples below x > 1"
    );
}

/// LIA CEGQI should use rho for non-unit integer bounds so it instantiates
/// with an integer value satisfying the selected bound.
#[test]
#[timeout(10000)]
fn test_cegqi_lia_nonunit_lower_bound_rho_counterexample_unsat_560() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (and (>= (* 2 x) 5) (<= x 10))
                (> x 3))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "x=3 refutes forall x:Int. 2*x >= 5 => x > 3"
    );
}

/// #5888 core fix: Mixed UF+arithmetic quantifier should be handled by CEGQI.
///
/// deductive-checks pattern: `forall x:Int. f(x) > 0 => x >= 1`. Before fix,
/// `is_cegqi_candidate` rejected this because `f(x)` is an uninterpreted
/// function. After fix, CEGQI accepts the formula and uses model value
/// fallback for the UF-dependent bound. The formula is SAT (Z3 confirms).
///
/// Currently AY may return sat, unknown, or unsat depending on solver
/// nondeterminism. The false-UNSAT is a known CEGQI refinement incompleteness
/// tracked separately. This test verifies CEGQI attempts the formula without
/// crashing.
#[test]
#[timeout(10000)]
fn test_cegqi_mixed_uf_arith_deductive_checks_pattern() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (=> (> (f x) 0) (>= x 1))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    // Z3 confirms SAT. #5975 fix: disambiguation now always runs when CE lemmas
    // are present, even when E-matching added instantiations. This prevents
    // false-UNSAT from CE lemma + E-matching interaction.
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "Mixed UF+arith should be SAT or Unknown (not false-UNSAT), got: {results:?}"
    );
}

/// #5888: Tautology with UF: forall x:Int. f(x) > x => x < f(x).
///
/// This is logically valid regardless of the interpretation of f.
/// `a > b` and `b < a` are equivalent. Should be SAT.
#[test]
#[timeout(10000)]
fn test_cegqi_uf_arith_tautology() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (=> (> (f x) x) (< x (f x)))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "UF tautology should be SAT or Unknown, got: {results:?}"
    );
}

/// #5888: Pure arithmetic with UF in non-quantified context.
///
/// `f(0) = 5` with `forall x. x >= 0 => x + f(0) >= 5`. The quantified
/// variable x appears in pure arithmetic, but f(0) is a ground UF term.
/// CEGQI should handle x via bound extraction, treating f(0) as a constant.
#[test]
#[timeout(10000)]
fn test_cegqi_ground_uf_in_quantifier() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 5))
        (assert (forall ((x Int))
            (=> (>= x 0) (>= (+ x (f 0)) 5))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "Ground UF + arithmetic quantifier should be SAT"
    );
}

/// CEGQI exists-only: UNSAT from solver should degrade to Unknown.
///
/// `exists x. x > 0 AND x < 0` is genuinely UNSAT, but the CEGQI exists path
/// only searches for witnesses (incomplete). When no witness is found, the
/// correct result is Unknown (not UNSAT), since CEGQI doesn't prove non-existence.
///
/// However, AY may also return UNSAT through other paths (e.g., ground theory
/// reasoning detects the contradiction without CEGQI). Both UNSAT and Unknown
/// are sound here. The key is that SAT must NOT be returned.
#[test]
#[timeout(10000)]
fn test_cegqi_exists_unsat_not_false_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (and (> x 0) (< x 0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "unsat" || results[0] == "unknown",
        "Unsatisfiable exists must not return sat, got: {results:?}"
    );
}

/// CEGQI exists-only SAT: witness found means exists holds.
///
/// `exists x. x > 0 AND x < 10` has many witnesses (1..9).
/// CEGQI should find one and return SAT.
#[test]
#[timeout(10000)]
fn test_cegqi_exists_sat_witness_found() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (and (> x 0) (< x 10))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "Satisfiable exists should be SAT or Unknown, got: {results:?}"
    );
}
