// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #6564: release-only false-UNSAT from an incomplete
//! slack-variable propagation reason.
//!
//! Root cause: slack-variable propagation used `bound.reason_pairs()` which
//! only witnesses the slack bound, not the contributing original-variable
//! bounds. This produced unsound learned clauses in release mode (debug
//! mode's `verify_propagation_semantic` masked the bug).
//!
//! The fix (#6564) reconstructs reasons from the original linear expression
//! via `collect_interval_reasons` for slack variables.
//!
//! The original failure was exposed by an externally licensed SMT-LIB corpus
//! benchmark. The gate uses a hand-authored Apache-2.0 structural reduction so
//! a clean checkout exercises the same implied-row mechanism hermetically.
//!
//! This test runs ONLY in release mode (the bug never manifests in debug) and
//! repeats 10 times to catch the non-deterministic HashMap iteration order
//! that triggers the unsound path.
//!
//! The full-lane release sweep for `#6564` lives in the `ay` CLI test surface,
//! where subprocess timeouts are hard wall-clock limits.
//!
//! Part of #6564

// All imports are release-only since the test function is cfg-gated.
#[cfg(not(debug_assertions))]
use anyhow::Result;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 6;

/// Release-only regression: a slack-derived bound must always remain SAT.
///
/// Fixing `y = 0` and asserting `x + y <= 3` derives `x <= 3` through a
/// slack row. The disjunction registers that derived atom while preserving the
/// explicit witness `x = 2, y = 0`.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_slack_reason_reduction_is_always_sat_in_release_6564() -> Result<()> {
    use crate::common::{run_executor_file_with_timeout, workspace_path, SolverOutcome};

    let path =
        workspace_path("benchmarks/smt/regression/qf_lra_release_soundness/slack_reason_sat.smt2");
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    for run in 0..10 {
        let got = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "release run {run} returned {got:?} on the #6564 slack-reason reduction"
        );
    }
    Ok(())
}
