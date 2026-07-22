// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #6564: release-only false-UNSAT on
//! `constraints-tempo-width-10.smt2` (QF_LRA).
//!
//! Root cause: slack-variable propagation used `bound.reason_pairs()` which
//! only witnesses the slack bound, not the contributing original-variable
//! bounds. This produced unsound learned clauses in release mode (debug
//! mode's `verify_propagation_semantic` masked the bug).
//!
//! The fix (#6564) reconstructs reasons from the original linear expression
//! via `collect_interval_reasons` for slack variables.
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
#[cfg(not(debug_assertions))]
use anyhow::Result;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 6;

/// Release-only regression: constraints-tempo-width-10 must always return SAT.
///
/// The benchmark metadata says `:status sat` and Z3 confirms SAT.
/// Before the #6564 fix, release mode returned false-UNSAT ~70% of the time
/// due to unsound slack-variable propagation reasons.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_constraints_tempo_width_10_is_always_sat_in_release_6564() -> Result<()> {
    use crate::common::{
        check_z3_or_skip, run_executor_file_with_timeout, run_z3_file, workspace_path,
        SolverOutcome,
    };

    let path = workspace_path("benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2");
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    if check_z3_or_skip() {
        assert_eq!(
            run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)?,
            SolverOutcome::Sat
        );
    }

    for run in 0..10 {
        let got = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "release run {run} disagreed on constraints-tempo-width-10 (#6564)"
        );
    }
    Ok(())
}
