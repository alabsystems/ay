// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
#![allow(clippy::panic)]

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const DILLIG02_M_1362: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2");
const HALF_TRUE_MODIF_M_1362: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/half_true_modif_m_000.smt2");

/// Regression guard for #1362.
///
/// `dillig02_m` is the explicit modular-arithmetic benchmark from the issue
/// report. The adaptive CHC entrypoint should keep proving it safe.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(40_000))]
fn adaptive_dillig02_m_benchmark_is_safe_1362() {
    let problem = ChcParser::parse(DILLIG02_M_1362)
        .unwrap_or_else(|err| panic!("dillig02_m benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("dillig02_m benchmark should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_mins(1)
    } else {
        Duration::from_secs(20)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#1362 regression: dillig02_m_000.smt2 should be safe, got {result:?}"
    );
}

/// Soundness canary for #1362.
///
/// `half_true_modif_m` remains a hard benchmark in the current tree, but it is
/// known-safe. Unknown is acceptable; Unsafe would be a soundness bug.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(45_000))]
fn adaptive_half_true_modif_m_never_unsafe_1362() {
    let problem = ChcParser::parse(HALF_TRUE_MODIF_M_1362)
        .unwrap_or_else(|err| panic!("half_true_modif_m benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("half_true_modif_m benchmark should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(35)
    } else {
        Duration::from_secs(20)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    assert!(
        !matches!(result, VerifiedChcResult::Unsafe(_)),
        "#1362 soundness regression: half_true_modif_m_000.smt2 is known-safe, got {result:?}"
    );
}
