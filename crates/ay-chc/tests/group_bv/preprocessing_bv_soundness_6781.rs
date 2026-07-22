// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Public-entrypoint regression coverage for CHC preprocessing bug #6781.
//!
//! The narrowed reproducer already exists in `portfolio.rs` unit tests, but the
//! consumer-facing solve surfaces were not covered directly. These integration
//! tests exercise the parsed benchmark through:
//! - the stable portfolio constructor in `ay_chc::engines`
//! - `AdaptivePortfolio::solve()`, which downstream consumers call
//!
//! The bug was a false-UNSAT from preprocessing collapse. The stable portfolio
//! path must return `Unsafe` on this benchmark; the adaptive path may
//! conservatively return verified `Unknown`. `Safe` would be unsound.

use ay_chc::{
    engines, AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcParser, EngineConfig,
    PortfolioConfig, PortfolioResult, VerifiedChcResult,
};
use std::time::Duration;

const MINIMAL_FALSE_UNSAT_REPRO_6781: &str = r#"
(set-logic HORN)
(declare-fun |bb0| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb1| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb2| ((_ BitVec 32) (Array (_ BitVec 32) Bool)) Bool)

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
    (=> (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true))
        (bb0 obj_valid))))

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
    (=> (bb0 obj_valid)
        (bb1 obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (bb1 obj_valid)
        (bb2 x obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (and (bb2 x obj_valid)
             (not (select obj_valid #x00000002)))
        false)))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (and (bb2 x obj_valid)
             (not (bvsgt x #x00000000)))
        false)))

(check-sat)
(exit)
"#;

fn parse_minimal_false_unsat_repro() -> ay_chc::ChcProblem {
    let problem = ChcParser::parse(MINIMAL_FALSE_UNSAT_REPRO_6781)
        .expect("issue #6781 reproducer should parse");
    problem
        .validate()
        .expect("issue #6781 reproducer should be a valid CHC problem");
    assert!(
        problem.has_bv_sorts(),
        "issue #6781 reproducer must exercise BV preprocessing"
    );
    problem
}

fn minimal_repro_portfolio_config() -> PortfolioConfig {
    PortfolioConfig::with_engines(vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
        5, false, None,
    ))])
    .parallel(false)
    .preprocessing(true)
}

#[test]
#[serial_test::serial]
fn portfolio_minimal_bv_preprocessing_repro_returns_unsafe() {
    let problem = parse_minimal_false_unsat_repro();
    let solver = engines::new_portfolio_solver(problem, minimal_repro_portfolio_config());
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "stable portfolio entrypoint regressed on #6781 reproducer: expected Unsafe, got {result:?}"
    );
}

#[test]
#[serial_test::serial]
fn adaptive_minimal_bv_preprocessing_repro_returns_unsafe_or_unknown() {
    let problem = parse_minimal_false_unsat_repro();
    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(5)),
    );
    let result = solver.solve();

    assert!(
        matches!(
            result,
            VerifiedChcResult::Unsafe(_) | VerifiedChcResult::Unknown(_)
        ),
        "adaptive public API regressed on #6781 reproducer: expected Unsafe or Unknown, got {result:?}"
    );
}
