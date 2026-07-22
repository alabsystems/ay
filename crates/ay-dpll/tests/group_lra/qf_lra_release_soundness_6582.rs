// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #6582: release-only false-UNSAT on QF_LRA benchmarks.
//!
//! Root cause: `compute_expr_interval()` collapsed strict/non-strict endpoints
//! into plain `BigRational`, so open-zero boundaries were indistinguishable
//! from closed-zero. This caused the interval propagation engine to derive
//! unsound compound-atom truth values.
//!
//! The fix (Packet 2) introduces `IntervalEndpoint` with a `strict` flag and
//! replaces raw sign checks with endpoint-aware helpers.
//!
//! `constraints-tempo-width-10` is fixed by Packet 1 (propagation guard) +
//! Packet 2 (endpoint strictness). The remaining 2 benchmarks
//! (`constraints-tempo-width-60`, `simple_startup_6nodes`) no longer return
//! false `unsat`, but they still time out in the current release solver. Keep
//! those as release soundness canaries until the deeper simplex/performance
//! work lands.
//!
//! Part of #6582

// All imports are release-only since the test function is cfg-gated.
#[cfg(not(debug_assertions))]
use anyhow::Result;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 10;

#[cfg(not(debug_assertions))]
const FALSE_UNSAT_CANARY_TIMEOUT_SECS: u64 = 10;

#[cfg(not(debug_assertions))]
const FALSE_UNSAT_CANARY_Z3_TIMEOUT_SECS: u64 = 20;

#[cfg(not(debug_assertions))]
const FALSE_UNSAT_CANARY_RUNS: usize = 3;

/// Release-only regression: constraints-tempo-width-10 must return SAT.
///
/// Before the #6582 fix, release mode returned false-UNSAT because the interval
/// propagation path erased endpoint strictness, causing unsound compound-atom
/// implications.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_constraints_tempo_width_10_release_sat_6582() -> Result<()> {
    use crate::common::{
        check_z3_or_skip, run_executor_file_with_timeout, run_z3_file, workspace_path,
        SolverOutcome,
    };

    let path = workspace_path("benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2");
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    if check_z3_or_skip() {
        assert_eq!(
            run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)?,
            SolverOutcome::Sat,
            "Z3 disagrees on expected SAT for constraints-tempo-width-10"
        );
    }

    for run in 0..5 {
        let got = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "release run {run} returned {got:?} for constraints-tempo-width-10 (#6582)"
        );
    }
    Ok(())
}

/// Release soundness canary: width-60 is known SAT in Z3 and must never
/// regress back to false-UNSAT in AY release, even though current HEAD still
/// times out within the canary budget.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_constraints_tempo_width_60_release_no_false_unsat_6582() -> Result<()> {
    use crate::common::{
        assert_z3_sat_or_known_status, run_executor_file_with_timeout, workspace_path,
        SolverOutcome,
    };

    let path = workspace_path("benchmarks/smtcomp/QF_LRA/constraints-tempo-width-60.smt2");
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    assert_z3_sat_or_known_status(
        &path,
        FALSE_UNSAT_CANARY_Z3_TIMEOUT_SECS,
        "constraints-tempo-width-60",
    )?;

    for run in 0..FALSE_UNSAT_CANARY_RUNS {
        let got = run_executor_file_with_timeout(&path, FALSE_UNSAT_CANARY_TIMEOUT_SECS)?;
        assert!(
            matches!(
                got,
                SolverOutcome::Sat | SolverOutcome::Unknown | SolverOutcome::Timeout
            ),
            "release run {run} returned false-UNSAT for constraints-tempo-width-60 (#6582): {got:?}"
        );
    }
    Ok(())
}

/// Release soundness canary: the 6-node startup case is SAT in Z3 and must not
/// regress back to false-UNSAT in AY release while the remaining performance
/// work is still open.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_simple_startup_6nodes_release_no_false_unsat_6582() -> Result<()> {
    use crate::common::{
        assert_z3_sat_or_known_status, run_executor_file_with_timeout, workspace_path,
        SolverOutcome,
    };

    let path =
        workspace_path("benchmarks/smtcomp/QF_LRA/simple_startup_6nodes.missing.induct.smt2");
    assert!(path.exists(), "Benchmark not found: {}", path.display());

    assert_z3_sat_or_known_status(
        &path,
        FALSE_UNSAT_CANARY_Z3_TIMEOUT_SECS,
        "simple_startup_6nodes.missing.induct",
    )?;

    for run in 0..FALSE_UNSAT_CANARY_RUNS {
        let got = run_executor_file_with_timeout(&path, FALSE_UNSAT_CANARY_TIMEOUT_SECS)?;
        assert!(
            matches!(
                got,
                SolverOutcome::Sat | SolverOutcome::Unknown | SolverOutcome::Timeout
            ),
            "release run {run} returned false-UNSAT for simple_startup_6nodes.missing.induct (#6582): {got:?}"
        );
    }
    Ok(())
}
