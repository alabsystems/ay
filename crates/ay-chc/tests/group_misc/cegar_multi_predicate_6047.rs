// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integration tests for CEGAR soundness on multi-predicate CHC problems (#6047).
//!
//! The CEGAR engine's `validate_counterexample()` had a soundness bug where
//! multi-predicate problems (>1 predicate) trusted abstract feasibility checks
//! without BMC validation. This caused false-Unsafe results on safe problems.
//!
//! Fix: multi-predicate counterexamples are now rejected (treated as spurious),
//! causing CEGAR to return Unknown. Other engines (PDR) solve correctly.
//!
//! These tests exercise multi-predicate CHC problems through the portfolio to
//! verify end-to-end correctness. They complement the unit test in
//! `cegar/engine/tests.rs::test_cegar_no_false_unsafe_multi_predicate_6047`.

use ay_chc::{testing, ChcParser, PortfolioConfig, PortfolioResult};
use ntest::timeout;

fn solve_portfolio(input: &str) -> PortfolioResult {
    let problem = ChcParser::parse(input).unwrap();
    let config = PortfolioConfig::test_default();
    let solver = testing::new_portfolio_solver(problem, config);
    solver.solve()
}

// NOTE: Model verification (verify_model) is intentionally omitted here.
// Multi-predicate model verification has known issues — the PDR verifier
// doesn't handle multi-predicate invariant maps correctly. The focus of
// these tests is CEGAR soundness (no false-Unsafe), not proof validity.

/// Two predicates, sequential: P(x) -> Q(x) -> false.
/// Safe because the query constraint (x < 0) is unreachable from init (x = 0).
///
/// This is the integration-level version of the CEGAR unit test in
/// `test_cegar_no_false_unsafe_multi_predicate_6047`.
/// Before the fix, CEGAR returned false-Unsafe on this problem.
#[test]
#[timeout(10_000)]
fn test_portfolio_multi_pred_sequential_safe_6047() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Init: x = 0 => P(x)
(assert (forall ((x Int))
  (=> (= x 0) (P x))))

; Transfer: P(x) => Q(x)
(assert (forall ((x Int))
  (=> (P x) (Q x))))

; Query: Q(x) /\ x < 0 => false
(assert (forall ((x Int))
  (=> (and (Q x) (< x 0)) false)))

(check-sat)
"#;
    let result = solve_portfolio(input);
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "Multi-pred sequential safe problem must not return Unsafe (#6047), got: {result:?}"
    );
}

/// Two predicates with self-loop: P counts up, Q receives value.
/// Safe because x >= 0 always holds (init x=0, step x=x+1).
#[test]
#[timeout(10_000)]
fn test_portfolio_multi_pred_loop_transfer_safe_6047() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Init: x = 0 => P(x)
(assert (forall ((x Int))
  (=> (= x 0) (P x))))

; Self-loop: P(x) => P(x + 1)
(assert (forall ((x Int))
  (=> (P x) (P (+ x 1)))))

; Transfer: P(x) => Q(x)
(assert (forall ((x Int))
  (=> (P x) (Q x))))

; Query: Q(x) /\ x < 0 => false
(assert (forall ((x Int))
  (=> (and (Q x) (< x 0)) false)))

(check-sat)
"#;
    let result = solve_portfolio(input);
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "Multi-pred loop+transfer safe problem must not return Unsafe (#6047), got: {result:?}"
    );
}

/// Three predicates in a chain: P -> Q -> R -> false.
/// Safe because the query constraint is unreachable.
#[test]
#[timeout(10_000)]
fn test_portfolio_three_pred_chain_safe_6047() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)

; Init: x = 5 => P(x)
(assert (forall ((x Int))
  (=> (= x 5) (P x))))

; Transfer: P(x) => Q(x)
(assert (forall ((x Int))
  (=> (P x) (Q x))))

; Transfer: Q(x) => R(x)
(assert (forall ((x Int))
  (=> (Q x) (R x))))

; Query: R(x) /\ x > 10 => false (unreachable since x=5)
(assert (forall ((x Int))
  (=> (and (R x) (> x 10)) false)))

(check-sat)
"#;
    let result = solve_portfolio(input);
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "3-pred chain safe problem must not return Unsafe (#6047), got: {result:?}"
    );
}

/// Two predicates, genuinely unsafe: P(x) -> Q(x) -> false.
/// Unsafe because x = 0 is reachable and x >= 0 is the query constraint.
#[test]
#[timeout(10_000)]
fn test_portfolio_multi_pred_sequential_unsafe_6047() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Init: x = 0 => P(x)
(assert (forall ((x Int))
  (=> (= x 0) (P x))))

; Transfer: P(x) => Q(x)
(assert (forall ((x Int))
  (=> (P x) (Q x))))

; Query: Q(x) /\ x >= 0 => false (reachable since x=0)
(assert (forall ((x Int))
  (=> (and (Q x) (>= x 0)) false)))

(check-sat)
"#;
    let result = solve_portfolio(input);
    assert!(
        !matches!(result, PortfolioResult::Safe(_)),
        "Multi-pred genuinely unsafe problem must not return Safe (#6047), got: {result:?}"
    );
}

/// Two predicates with two variables: P(x,y) -> Q(x,y) -> false.
/// Safe because x >= 0 and y >= 0 hold (init x=0, y=0; step x=x+1, y=y+2).
#[test]
#[timeout(10_000)]
fn test_portfolio_multi_pred_two_var_safe_6047() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; Init: x = 0, y = 0 => P(x, y)
(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y 0)) (P x y))))

; Self-loop: P(x, y) => P(x+1, y+2)
(assert (forall ((x Int) (y Int))
  (=> (P x y) (P (+ x 1) (+ y 2)))))

; Transfer: P(x, y) => Q(x, y)
(assert (forall ((x Int) (y Int))
  (=> (P x y) (Q x y))))

; Query: Q(x, y) /\ x + y < 0 => false (unreachable)
(assert (forall ((x Int) (y Int))
  (=> (and (Q x y) (< (+ x y) 0)) false)))

(check-sat)
"#;
    let result = solve_portfolio(input);
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "Multi-pred 2-var safe problem must not return Unsafe (#6047), got: {result:?}"
    );
}
