// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #8529: false-SAT on QF_LRA benchmarks due to invalid
//! theory propagation accepted in release builds.
//!
//! Root cause: `verify_propagation_semantic` was gated behind
//! `#[cfg(debug_assertions)]` (#8782), meaning invalid LRA propagations were
//! caught and skipped in debug mode but silently accepted in release mode.
//! The invalid propagations corrupted the DPLL(T) search, causing the solver
//! to return SAT on UNSAT benchmarks (synched.base.smt2).
//!
//! The fix promotes `verify_propagation_semantic` to all builds so invalid
//! propagations are caught and skipped regardless of build profile.
//!
//! Part of #8529

use anyhow::Result;

/// Timeout for individual benchmark runs (seconds).
const BENCHMARK_TIMEOUT_SECS: u64 = 15;

/// Number of consecutive runs to verify determinism.
/// Non-deterministic bugs (pre-fix #8529 was ~50/50 SAT/UNSAT) need multiple
/// runs to catch. 15 runs gives >99.99% detection rate for a 50% flip bug.
const DETERMINISM_RUNS: usize = 15;

/// synched.base.smt2 must return UNSAT in release builds.
///
/// Before the #8529 fix, release mode consistently returned false-SAT because
/// the LRA theory solver emitted invalid propagations that were only caught
/// by the debug-only `verify_propagation_semantic` check.
#[test]
#[ntest::timeout(300_000)]
fn test_synched_base_release_unsat_8529() -> Result<()> {
    use crate::common::{
        check_z3_or_skip, run_executor_file_with_timeout, run_z3_file, workspace_path,
        SolverOutcome,
    };

    let path = workspace_path("benchmarks/smtcomp/QF_LRA/synched.base.smt2");
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!("SKIP: benchmark file not found: {}", path.display());
        return Ok(());
    }

    // Verify Z3 agrees this is UNSAT
    if check_z3_or_skip() {
        let z3_result = run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            z3_result,
            SolverOutcome::Unsat,
            "Z3 reference disagrees: expected UNSAT on synched.base.smt2"
        );
    }

    // Run multiple times to detect non-determinism (#8529 was ~50/50 pre-fix)
    for run in 0..DETERMINISM_RUNS {
        let result = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)?;
        assert_eq!(
            result,
            SolverOutcome::Unsat,
            "Run {}/{}: synched.base.smt2 returned {:?}, expected UNSAT (#8529 regression)",
            run + 1,
            DETERMINISM_RUNS,
            result
        );
    }

    Ok(())
}
