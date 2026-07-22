// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #6242: false-UNSAT on QF_LRA benchmarks.
//!
//! These benchmarks historically exposed false-UNSAT answers where Z3 reports
//! SAT. Current `HEAD` no longer proves the wrong answer on the two smallest
//! startup cases, but it still fails to solve them within the canary budget, so
//! the tests track that explicit incomplete behavior instead of silently
//! accepting any non-UNSAT result.
//!
//! Root cause: NOT the unit theory lemma enqueue reason (mod.rs:2184) nor
//! the LRA strictness propagation. Both of those are correct fixes but
//! do not resolve the false-UNSAT. The actual root cause is deeper in
//! the LRA theory propagation or conflict explanation pipeline.
//!
//! Part of #6242

use crate::common::{
    run_executor_file_with_timeout, run_executor_smt_with_timeout, workspace_path, SolverOutcome,
};
use anyhow::Result;
use ntest::timeout;

const STARTUP_CANARY_TIMEOUT_SECS: u64 = 5;

/// Smallest false-UNSAT reproducer from #6242: simple_startup_10nodes.bug.induct.
/// This is a 150-line industrial QF_LRA benchmark (TTA Startup).
/// The expected answer is SAT (set-info :status sat in the benchmark).
/// Current behavior on `HEAD` is slower: the executor does not finish within
/// the 5-second canary budget. When this starts returning SAT, tighten the
/// assertion to `SolverOutcome::Sat`.
#[test]
#[timeout(10_000)]
fn test_false_unsat_simple_startup_10nodes_6242() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/simple_startup_10nodes.bug.induct.smt2");
    assert!(
        path.exists(),
        "Benchmark not found: {}. Run from workspace root or check benchmarks.",
        path.display()
    );
    assert_eq!(
        run_executor_file_with_timeout(&path, STARTUP_CANARY_TIMEOUT_SECS)?,
        SolverOutcome::Timeout,
        "#6242 canary changed for simple_startup_10nodes; tighten the assertion to SAT once the benchmark stops timing out"
    );
    Ok(())
}

/// Second smallest false-UNSAT reproducer: simple_startup_14nodes.bug.induct.
/// Current behavior on `HEAD` is the same timeout canary as the 10-node case.
#[test]
#[timeout(10_000)]
fn test_false_unsat_simple_startup_14nodes_6242() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/simple_startup_14nodes.bug.induct.smt2");
    assert!(
        path.exists(),
        "Benchmark not found: {}. Run from workspace root or check benchmarks.",
        path.display()
    );
    assert_eq!(
        run_executor_file_with_timeout(&path, STARTUP_CANARY_TIMEOUT_SECS)?,
        SolverOutcome::Timeout,
        "#6242 canary changed for simple_startup_14nodes; tighten the assertion to SAT once the benchmark stops timing out"
    );
    Ok(())
}

/// Minimal inline reproducer: Bool/Real with LP-style differences.
/// This attempts to capture the false-UNSAT pattern in a small formula.
/// If this passes while the benchmark tests fail, the minimal formula
/// doesn't capture the triggering pattern.
#[test]
#[timeout(15_000)]
fn test_lra_bool_real_mixed_difference_sat_6242() -> Result<()> {
    // Simplified from simple_startup_10nodes pattern:
    // Boolean state variables with Real timing constraints.
    let result = run_executor_smt_with_timeout(
        "(set-logic QF_LRA)
         (declare-fun b0 () Bool)
         (declare-fun b1 () Bool)
         (declare-fun t0 () Real)
         (declare-fun t1 () Real)
         (declare-fun d () Real)
         (assert (>= d 0.0))
         (assert (<= d 10.0))
         (assert (=> b0 (and (>= t0 0.0) (<= t0 100.0))))
         (assert (=> b1 (and (>= t1 0.0) (<= t1 100.0))))
         (assert (=> (and b0 b1) (<= (- t1 t0) d)))
         (assert (or b0 b1))
         (check-sat)",
        5,
    );
    assert_eq!(
        result?,
        SolverOutcome::Sat,
        "mixed Bool/Real LRA formula should be SAT"
    );
    Ok(())
}
