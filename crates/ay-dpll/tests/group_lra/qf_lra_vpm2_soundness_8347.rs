// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #8347: QF_LRA soundness disagreement on vpm2-30.smt2.
//!
//! Root cause: implied bound propagation was disabled (#9031) due to soundness
//! concerns in bound refinements. The unsound path was bound *refinements*
//! (creating permanent SAT clauses from stale implied bounds), not implied
//! bound *propagation* (which always traces reasons back to direct bounds).
//!
//! The fix re-enables implied bound propagation (sound) while keeping bound
//! refinements disabled (unsound). This test verifies that AY never returns
//! UNSAT on vpm2-30.smt2, which Z3 and benchmark metadata confirm is SAT.
//!
//! Part of #8347

use crate::common::{run_executor_file_with_timeout, workspace_path, SolverOutcome};
use anyhow::Result;

/// vpm2-30.smt2 is a dense LP benchmark (445+ atom-indexed vars, 793 compound
/// wakeup vars). Z3 returns SAT in ~0.9s. AY must NOT return UNSAT.
/// Timeout/Unknown is acceptable — the soundness constraint is: never UNSAT.
#[test]
#[ntest::timeout(30_000)]
fn test_vpm2_30_never_returns_unsat_8347() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/vpm2-30.smt2");
    // `benchmarks/smtcomp/` is gitignored (see .gitignore, only two QF_LRA files
    // are whitelisted), so a clean checkout has no corpus. Gate on presence the
    // same way the two sibling tests below already do, rather than hard-failing
    // on an absent fixture. The soundness guard (never UNSAT) is unchanged.
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!(
            "SKIP test_vpm2_30_never_returns_unsat_8347: corpus benchmark not found: {}",
            path.display()
        );
        return Ok(());
    }

    // Run with a short timeout — we only need to verify the answer is not UNSAT.
    // If AY solves it quickly, great. If it times out, that's acceptable.
    let result = run_executor_file_with_timeout(&path, 5)?;
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG (#8347): AY returned UNSAT on vpm2-30.smt2 but Z3 says SAT. \
         This was the original false-UNSAT bug from implied bound persistence."
    );
    Ok(())
}

/// Broader check: sc-6.induction3.cvc.smt2 was another false-UNSAT victim.
/// Z3 returns SAT; AY must not return UNSAT.
#[test]
#[ntest::timeout(30_000)]
fn test_sc6_induction3_never_returns_unsat_8347() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/sc-6.induction3.cvc.smt2");
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!("Benchmark not found, skipping: {}", path.display());
        return Ok(());
    }

    let result = run_executor_file_with_timeout(&path, 5)?;
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG (#8347): AY returned UNSAT on sc-6.induction3.cvc.smt2 but Z3 says SAT."
    );
    Ok(())
}

/// sc-8.induction3.cvc.smt2 was another false-UNSAT victim.
#[test]
#[ntest::timeout(30_000)]
fn test_sc8_induction3_never_returns_unsat_8347() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/sc-8.induction3.cvc.smt2");
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!("Benchmark not found, skipping: {}", path.display());
        return Ok(());
    }

    let result = run_executor_file_with_timeout(&path, 5)?;
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG (#8347): AY returned UNSAT on sc-8.induction3.cvc.smt2 but Z3 says SAT."
    );
    Ok(())
}
