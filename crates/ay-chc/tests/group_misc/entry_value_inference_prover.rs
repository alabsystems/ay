// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prover integration tests for entry-value inference in PDR.
//!
//! These tests exercise the entry-value inference heuristic end-to-end,
//! verifying that PDR correctly infers initial bounds for predicate variables
//! from transition constraints. The 100ms SAT-check timeout in
//! `is_sat_for_entry_value_inference` is exercised implicitly through the
//! full PDR solve path.

use ay_chc::{testing, ChcParser, PdrConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;

/// Two-variable counter with constant offset (y = 2x).
/// Entry-value inference should discover the relationship y = 2x from the
/// transition constraint and initial values, aiding invariant discovery.
///
/// This exercises the entry-value inference SAT probe with a satisfiable
/// combined constraint (init values + transition guard).
#[test]
#[timeout(30_000)]
fn entry_value_inference_aids_two_counter_invariant() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
    (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y 2))) (inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (not (= y (* 2 x)))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).expect("parse");
    let solver = testing::new_portfolio_solver(problem.clone(), PortfolioConfig::test_default());
    let result = solver.solve();

    if let PortfolioResult::Safe(model) = &result {
        let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "Safe result has invalid proof"
        );
    }

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "PDR should prove safe with entry-value inference aiding y=2x discovery, got: {result:?}"
    );
}

/// Counter with unsatisfiable combined context: init x=0, property x>=0.
/// The relaxed context fallback in entry-value inference should handle this gracefully.
#[test]
#[timeout(30_000)]
fn entry_value_inference_unsat_context_fallback() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x1 Int))
    (=> (and (inv x) (= x1 (+ x 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).expect("parse");
    let solver = testing::new_portfolio_solver(problem.clone(), PortfolioConfig::test_default());
    let result = solver.solve();

    if let PortfolioResult::Safe(model) = &result {
        let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "Safe result has invalid proof"
        );
    }

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "simple increasing counter should be safe, got: {result:?}"
    );
}

/// Three-variable problem where entry-value inference must handle
/// a transition with both equality and inequality constraints.
/// The 100ms timeout should not interfere with standard-size problems.
#[test]
#[timeout(60_000)]
fn entry_value_inference_mixed_constraints_within_timeout() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (c Int))
    (=> (and (= a 0) (= b 10) (= c 0)) (inv a b c))))
(assert (forall ((a Int) (b Int) (c Int) (a1 Int) (b1 Int) (c1 Int))
    (=> (and (inv a b c) (= a1 (+ a 1)) (= b1 (- b 1)) (= c1 (+ a1 b1)))
        (inv a1 b1 c1))))
(assert (forall ((a Int) (b Int) (c Int))
    (=> (and (inv a b c) (not (= (+ a b) 10))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).expect("parse");
    let solver = testing::new_portfolio_solver(problem.clone(), PortfolioConfig::test_default());
    let result = solver.solve();

    if let PortfolioResult::Safe(model) = &result {
        let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "Safe result has invalid proof"
        );
    }

    // a+b is invariant at 10: (a+1) + (b-1) = a + b = 10
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "a+b=10 invariant should be provable, got: {result:?}"
    );
}
