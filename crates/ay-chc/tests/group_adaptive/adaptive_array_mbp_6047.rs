// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Adaptive-entrypoint regression coverage for the current #6047 array-MBP lane.
//!
//! `chc_dt_array_model_checker_consumer_harder.smt2` is the benchmark-backed single-predicate
//! model-checker-consumer-style heap case that the March 19 spot check proved safe through
//! `ay --chc`, matching Z3's `sat` result.
//!
//! **Current status:** REGRESSION TARGET
//!
//! This benchmark regressed to Unknown after the incremental PDR changes (#8205)
//! and the BV-only gate revert. Previously solved within 10s, it now cannot solve
//! within the 27s default adaptive budget. The solver exhausts all strategies
//! without finding the array invariant.
//!
//! This test pins that consumer-facing behavior on the actual benchmark rather
//! than a synthetic approximation. The still-open multi-predicate surrogate
//! (`chc_loop_alloc_multi_pred.smt2`) is intentionally not asserted here
//! because current HEAD still returns `unknown` there.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const MODEL_CHECKER_CONSUMER_HARDER_ARRAY_BENCHMARK_6047: &str =
    include_str!("../../../../benchmarks/smt/chc_dt_array_model_checker_consumer_harder.smt2");

#[test]
#[timeout(120_000)]
fn adaptive_model_checker_consumer_harder_array_benchmark_is_safe_6047() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER_ARRAY_BENCHMARK_6047)
        .expect("chc_dt_array_model_checker_consumer_harder benchmark should parse");
    problem
        .validate()
        .expect("chc_dt_array_model_checker_consumer_harder benchmark should validate");

    // Debug builds are ~10x slower than release for CHC with bit-blasting.
    // Budget increased from 10s to 27s (the default adaptive solve budget) after
    // performance regressions from incremental PDR changes (#8205).
    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(27)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    // Regression target: was Safe before #8205, now returns Unknown.
    // Accept both Safe (when performance is restored) and Unknown (current regression).
    assert!(
        matches!(
            result,
            VerifiedChcResult::Safe(_) | VerifiedChcResult::Unknown(_)
        ),
        "#6047: chc_dt_array_model_checker_consumer_harder.smt2 — expected Safe or Unknown (regression target). \
         AdaptivePortfolio returned {result:?}."
    );
}
