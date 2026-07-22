// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::panic)]

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const DILLIG12_M_BENCHMARK_4751: &str =
    include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig12_m_000.smt2");

/// Regression guard for #4751.
///
/// Dedicated test binary (not part of `group_misc`): the release-profile solve
/// uses ~14s of a 20s wall-clock budget, so running it under `--test-threads=8`
/// alongside other heavy solves measures scheduler contention instead of the
/// solver (repo precedent: `u64_overflow_bv_derisk`). Cargo runs test binaries
/// sequentially, so this binary gets the machine to itself.
///
/// This is the full CHC-COMP `dillig12_m_000.smt2` benchmark from the issue
/// report, not the reduced E=1 variant. The benchmark is known-safe and should
/// stay solvable through the adaptive entrypoint.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(40_000))]
fn adaptive_dillig12_m_benchmark_is_safe_4751() {
    let problem = ChcParser::parse(DILLIG12_M_BENCHMARK_4751)
        .unwrap_or_else(|err| panic!("dillig12_m benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("dillig12_m benchmark should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
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
        "#4751 regression: dillig12_m_000.smt2 is safe, but AdaptivePortfolio returned {result:?}"
    );
}
