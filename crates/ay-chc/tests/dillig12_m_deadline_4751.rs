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
/// Dedicated test binary (not part of `group_misc`): the solve uses tens of
/// seconds of wall clock, so running it under `--test-threads=8` alongside
/// other heavy solves measures scheduler contention instead of the solver
/// (repo precedent: `u64_overflow_bv_derisk`). Cargo runs test binaries
/// sequentially, so this binary gets the machine to itself.
///
/// This is the full CHC-COMP `dillig12_m_000.smt2` benchmark from the issue
/// report, not the reduced E=1 variant. The benchmark is known-safe and should
/// stay solvable through the adaptive entrypoint.
///
/// # Sized as a hang guard, not a stopwatch
///
/// Both profiles get the same budget, and it is generous. This asserts a
/// CAPABILITY — that the adaptive entrypoint still proves this benchmark safe —
/// and the wall clock is only here to stop a hang from wedging the suite.
/// Precedent: `b862ba0e1 test(chc): size the chccomp synthesis guard as a hang
/// guard, not a stopwatch`.
///
/// The previous split (90s debug / 20s release) rested on a release solve
/// costing ~14s. That is no longer what the solve does. Proving this benchmark
/// now runs through a Stage-0 case split on the mode, and the `E = 1` branch is
/// only provable via the guarded/unguarded scaled-equality lemmas plus
/// Entry-CEGAR discharge — real work that the earlier code simply did not do,
/// because before it the benchmark was not provable at ANY budget. Measured
/// here, unloaded: **36.8s debug, 40.9s release**, the two profiles within ~10%
/// of each other because the portfolio is deadline-scheduled rather than
/// throughput-bound. A 20s release budget therefore did not measure a
/// regression, it just cut the solve off partway.
#[test]
#[timeout(150_000)]
fn adaptive_dillig12_m_benchmark_is_safe_4751() {
    let problem = ChcParser::parse(DILLIG12_M_BENCHMARK_4751)
        .unwrap_or_else(|err| panic!("dillig12_m benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("dillig12_m benchmark should validate: {err}"));

    // ~2.2x the measured need in either profile: enough that ordinary machine
    // variance cannot fail it, small enough that a genuine hang still trips.
    let budget = Duration::from_secs(90);

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
