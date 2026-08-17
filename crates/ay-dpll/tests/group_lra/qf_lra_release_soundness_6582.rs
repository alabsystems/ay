// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #6582: release-only false-UNSAT from erased strict
//! interval endpoints.
//!
//! Root cause: `compute_expr_interval()` collapsed strict/non-strict endpoints
//! into plain `BigRational`, so open-zero boundaries were indistinguishable
//! from closed-zero. This caused the interval propagation engine to derive
//! unsound compound-atom truth values.
//!
//! The fix (Packet 2) introduces `IntervalEndpoint` with a `strict` flag and
//! replaces raw sign checks with endpoint-aware helpers.
//!
//! The original failures were exposed by externally licensed SMT-LIB corpus
//! benchmarks. These release tests use hand-authored Apache-2.0 reductions of
//! both open-zero endpoint directions, so the mandatory gate is hermetic.
//!
//! Part of #6582

// All imports are release-only since the test function is cfg-gated.
#[cfg(not(debug_assertions))]
use anyhow::Result;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 10;

#[cfg(not(debug_assertions))]
const FALSE_UNSAT_CANARY_RUNS: usize = 3;

/// Release-only regression: an open-zero lower endpoint must remain SAT.
///
/// `x > 0` and `y >= 0` imply `x + y > 0`; the first disjunct is false,
/// while `x = 1, y = 0` is an explicit satisfying witness.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_open_zero_lower_endpoint_release_sat_6582() -> Result<()> {
    use crate::common::{run_executor_file_with_timeout, workspace_path, SolverOutcome};

    let path = workspace_path(
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_lower_sat.smt2",
    );
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    for run in 0..5 {
        let got = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "release run {run} returned {got:?} on the #6582 open-zero lower reduction"
        );
    }
    Ok(())
}

/// Release-only regression: an open-zero upper endpoint must remain SAT.
///
/// `x < 0` and `y <= 0` imply `x + y < 0`; the first disjunct is false,
/// while `x = -1, y = 0` is an explicit satisfying witness.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_open_zero_upper_endpoint_release_sat_6582() -> Result<()> {
    use crate::common::{run_executor_file_with_timeout, workspace_path, SolverOutcome};

    let path = workspace_path(
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_upper_sat.smt2",
    );
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    for run in 0..FALSE_UNSAT_CANARY_RUNS {
        let got = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "release run {run} returned {got:?} on the #6582 open-zero upper reduction"
        );
    }
    Ok(())
}
