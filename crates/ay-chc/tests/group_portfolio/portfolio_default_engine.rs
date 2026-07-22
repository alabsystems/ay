// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[path = "../common/smt_inputs.rs"]
mod smt_inputs;

use ay_chc::{testing, ChcParser, PdrConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use smt_inputs::SAFE_INPUT;

const UNSAFE_INPUT: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (Inv x))))
(assert
  (forall ((x Int))
    (=>
      (Inv x)
      (Inv (+ x 1)))))
(assert
  (forall ((x Int))
    (=>
      (and (Inv x) (>= x 5))
      false)))
(check-sat)
(exit)
"#;

#[test]
#[timeout(10_000)]
fn portfolio_default_engine_solves_safe() {
    let problem = ChcParser::parse(SAFE_INPUT).unwrap();
    let solver = testing::new_portfolio_solver(problem.clone(), PortfolioConfig::test_default());
    let result = solver.solve();

    // Issue #758: Verify the proof when AY returns Safe.
    if let PortfolioResult::Safe(model) = &result {
        let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(model),
            "BUG: Safe result has invalid proof"
        );
    }

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "expected Safe, got {result:?}"
    );
}

#[test]
#[timeout(10_000)]
fn portfolio_default_engine_solves_unsafe() {
    let problem = ChcParser::parse(UNSAFE_INPUT).unwrap();
    let solver = testing::new_portfolio_solver(problem, PortfolioConfig::test_default());
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "expected Unsafe, got {result:?}"
    );
}
