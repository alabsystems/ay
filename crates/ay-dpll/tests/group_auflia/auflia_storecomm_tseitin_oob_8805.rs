// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #8805 (P0 panic) + #8785 (P1 false UNSAT) on QF_AUFLIA
//! storecomm_invalid benchmarks.
//!
//! ## Root Cause (#8805)
//!
//! `Tseitin::from_state` (introduced by #8786 to preserve term->var mappings
//! across incremental encoding) seeds `term_to_var` with entries at 1-indexed
//! SAT variable numbers that can exceed Tseitin's internal `next_var` counter.
//! When a newly-encoded sub-term references a seeded var via `get_var(term)`,
//! `next_var` is NOT bumped — so `result.num_vars = next_var - 1` understates
//! the true maximum variable referenced in `result.clauses`.
//!
//! `merge_local_mappings_from_tseitin` then failed to advance `local_next_var`
//! past those high-index seeded vars. A subsequent `solver.ensure_num_vars(
//! *local_next_var)` left the SAT solver's `num_vars` below the variable
//! referenced by the clause, and `add_clause_db_checked` panicked with
//! `"BUG: Clause contains out-of-bounds literal"`.
//!
//! The fix in `split_incremental.rs::merge_local_mappings_from_tseitin`
//! scans `result.clauses` for the maximum referenced variable and advances
//! `local_next_var` accordingly.
//!
//! ## Scope of This Test
//!
//! This regression test verifies the OOB panic is gone. The remaining
//! false-UNSAT behavior (#8785) is tracked separately — these benchmarks
//! may still return `unsat` (wrong; z3 says `sat`) or `unknown` (timeout),
//! but they MUST NOT panic.

#![allow(clippy::panic)]

use anyhow::{Context, Result};

use crate::common::{run_executor_file_with_timeout, workspace_path};

const TIMEOUT_SECS: u64 = 20;

/// Verify ay does not panic on the given QF_AUFLIA benchmark.
///
/// Prior to the fix, `cargo build --release && timeout 30 ay <file>` produced
/// a panic at `crates/ay-sat/src/solver/clause_add_internal.rs:88`. After the
/// fix, the solver returns a well-formed outcome (sat, unsat, or unknown) —
/// correctness of that outcome is covered by #8785, not by this test.
fn assert_no_panic_on_release(relative_path: &str) -> Result<()> {
    let path = workspace_path(relative_path);
    if !path.exists() {
        eprintln!(
            "skipping optional storecomm_invalid benchmark not checked into repo: {}",
            path.display()
        );
        return Ok(());
    }

    // If the executor panics, `run_executor_file_with_timeout` propagates the
    // panic via the spawned thread join, which `anyhow` converts into an Err.
    // Any Ok() outcome (Sat, Unsat, Unknown) confirms absence of the OOB panic.
    let outcome = run_executor_file_with_timeout(&path, TIMEOUT_SECS)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    // Explicitly accept any outcome — the test only guards against the panic.
    let _ = outcome;
    Ok(())
}

/// storecomm_invalid_t1_pp_sf_ni_00040_002: triggered the OOB panic in #8805.
#[test]
#[ntest::timeout(60_000)]
fn test_storecomm_invalid_00040_002_no_tseitin_oob_panic_8805() -> Result<()> {
    assert_no_panic_on_release(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00040_002.cvc.smt2",
    )
}

/// storecomm_invalid_t1_pp_sf_ni_00040_003: triggered the OOB panic in #8805.
#[test]
#[ntest::timeout(60_000)]
fn test_storecomm_invalid_00040_003_no_tseitin_oob_panic_8805() -> Result<()> {
    assert_no_panic_on_release(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00040_003.cvc.smt2",
    )
}

/// storecomm_invalid_t1_pp_sf_ni_00030_008: triggered the OOB panic in #8805.
#[test]
#[ntest::timeout(60_000)]
fn test_storecomm_invalid_00030_008_no_tseitin_oob_panic_8805() -> Result<()> {
    assert_no_panic_on_release(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
    )
}
