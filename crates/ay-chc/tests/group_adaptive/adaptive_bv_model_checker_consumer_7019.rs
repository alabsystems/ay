// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression guard for #7019's remaining model-checker-consumer BV lane.
//!
//! `chc_bv64_simple_model_checker_consumer.smt2` used to abort inside Farkas linear parsing when
//! BV64 constants were lowered into large Rational64 coefficients. The adaptive
//! entrypoint must now return a verified Safe result instead of crashing.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const BV64_SIMPLE_MODEL_CHECKER_CONSUMER_BENCHMARK_7019: &str =
    include_str!("../../../../benchmarks/smt/chc_bv64_simple_model_checker_consumer.smt2");

#[test]
#[timeout(120_000)]
fn adaptive_bv64_simple_model_checker_consumer_benchmark_is_safe_7019() {
    let problem = ChcParser::parse(BV64_SIMPLE_MODEL_CHECKER_CONSUMER_BENCHMARK_7019)
        .unwrap_or_else(|err| {
            panic!("chc_bv64_simple_model_checker_consumer.smt2 should parse: {err}");
        });
    problem.validate().unwrap_or_else(|err| {
        panic!("chc_bv64_simple_model_checker_consumer.smt2 should validate: {err}")
    });

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(10)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#7019: chc_bv64_simple_model_checker_consumer.smt2 is safe (z3 returns sat). \
         AdaptivePortfolio returned {result:?}."
    );
}
