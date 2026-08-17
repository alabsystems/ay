// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Release-mode regression tests for #6546.
//!
//! The AUFLIA eager-step + lazy-ROW2 path now clears the in-repo size-5,
//! size-7, and size-9 AUFLIA `storeinv` benchmarks. Keep those benchmarks as
//! the executable regression floor so future changes do not silently drop back
//! to `unknown`/timeout on the formulas that `#6546` now solves.
//!
//! Part of #6546

#[cfg(not(debug_assertions))]
#[cfg(not(debug_assertions))]
use anyhow::{Context, Result};

#[cfg(not(debug_assertions))]
use std::sync::{Mutex, MutexGuard, OnceLock};

#[cfg(not(debug_assertions))]
use crate::common::{
    check_z3_or_skip, run_executor_file_with_timeout, run_executor_smt_with_timeout, run_z3_file,
    workspace_path, SolverOutcome,
};

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 30;

#[cfg(not(debug_assertions))]
static STOREINV_RELEASE_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

#[cfg(not(debug_assertions))]
fn lock_storeinv_release() -> MutexGuard<'static, ()> {
    STOREINV_RELEASE_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[cfg(not(debug_assertions))]
fn assert_release_unsat_path(relative_path: &str, allow_missing: bool) -> Result<()> {
    // These benchmarks spawn a full Executor and consume the full 30s timeout
    // budget. Serialize this integration binary and keep the test-level
    // timeouts below large enough for the whole queued binary because
    // `ntest::timeout` counts time spent waiting on this mutex.
    let _guard = lock_storeinv_release();

    let path = workspace_path(relative_path);
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        if allow_missing {
            eprintln!(
                "skipping optional storeinv release benchmark not checked into repo: {}",
                path.display()
            );
            return Ok(());
        }
        panic!("benchmark not found: {}", path.display());
    }

    if check_z3_or_skip() {
        let z3_result = run_z3_file(&path, BENCHMARK_TIMEOUT_SECS)
            .with_context(|| format!("z3 failed on {}", path.display()))?;
        assert_eq!(
            z3_result,
            SolverOutcome::Unsat,
            "Z3 disagrees on expected unsat benchmark {}",
            path.display()
        );
    }

    let ay_result = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_eq!(
        ay_result,
        SolverOutcome::Unsat,
        "release executor regressed on {} (#6546)",
        path.display()
    );

    Ok(())
}

#[cfg(not(debug_assertions))]
fn assert_release_unsat(relative_path: &str) -> Result<()> {
    assert_release_unsat_path(relative_path, false)
}

#[cfg(not(debug_assertions))]
fn assert_release_unsat_if_present(relative_path: &str) -> Result<()> {
    assert_release_unsat_path(relative_path, true)
}

/// Nested `storeinv` size-5 should stay solved in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_nf_size5_release_unsat_6546() -> Result<()> {
    assert_release_unsat("benchmarks/smt/QF_AUFLIA/storeinv_nf_size5.smt2")
}

/// Flattened `storeinv` size-5 should stay solved in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_sf_size5_release_unsat_6546() -> Result<()> {
    assert_release_unsat("benchmarks/smt/QF_AUFLIA/storeinv_sf_size5.smt2")
}

/// Nested `storeinv` size-7 should stay solved in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_nf_size7_release_unsat_6546() -> Result<()> {
    assert_release_unsat("benchmarks/smt/QF_AUFLIA/storeinv_nf_size7.smt2")
}

/// Flattened `storeinv` size-7 should stay solved in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_sf_size7_release_unsat_6546() -> Result<()> {
    assert_release_unsat("benchmarks/smt/QF_AUFLIA/storeinv_sf_size7.smt2")
}

/// Nested `storeinv` size-9 should stay solved in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_nf_size9_release_unsat_6546() -> Result<()> {
    assert_release_unsat("benchmarks/smt/QF_AUFLIA/storeinv_nf_size9.smt2")
}

/// Flattened SMT-COMP storeinv with aliased witness selects should stay solved.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_t1_pp_sf_ai_00007_release_unsat_6546() -> Result<()> {
    assert_release_unsat_if_present(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_t1_pp_sf_ai_00007_001.cvc.smt2",
    )
}

/// Soundness: cross-index store-store equalities can still leave the base
/// arrays different at one written index on each side. AY must not report
/// UNSAT for these SAT formulas.
#[cfg(not(debug_assertions))]
fn assert_release_not_unsat_smt(smt: &str, scenario: &str) -> Result<()> {
    let _guard = lock_storeinv_release();

    let ay_result = run_executor_smt_with_timeout(smt, BENCHMARK_TIMEOUT_SECS)
        .with_context(|| format!("ay executor failed on {scenario}"))?;
    assert_ne!(
        ay_result,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG: ay returned unsat on SAT store-store equality scenario {scenario} (#6546)",
    );

    Ok(())
}

/// Regression guard for SAT formulas that currently identify the live AUFLIA
/// `#6546` fallout window on current `HEAD`.
#[cfg(not(debug_assertions))]
fn assert_release_sat_smt(smt: &str, scenario: &str) -> Result<()> {
    let _guard = lock_storeinv_release();

    let ay_result = run_executor_smt_with_timeout(smt, BENCHMARK_TIMEOUT_SECS)
        .with_context(|| format!("ay executor failed on {scenario}"))?;
    assert_eq!(
        ay_result,
        SolverOutcome::Sat,
        "release executor regressed on SAT AUFLIA scenario {scenario} (#6546)",
    );

    Ok(())
}

/// Soundness guard for file-based SAT benchmarks: AY must not return UNSAT
/// on benchmarks marked `:status sat`. Returning Unknown or Sat is acceptable.
#[cfg(not(debug_assertions))]
fn assert_release_not_unsat_file(relative_path: &str) -> Result<()> {
    let _guard = lock_storeinv_release();

    let path = workspace_path(relative_path);
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!(
            "skipping optional storeinv soundness benchmark: {}",
            path.display()
        );
        return Ok(());
    }

    let ay_result = run_executor_file_with_timeout(&path, BENCHMARK_TIMEOUT_SECS)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_ne!(
        ay_result,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG: ay returned unsat on SAT benchmark {} (#6546)",
        path.display()
    );

    Ok(())
}

/// SAT: equality of stores at different indices does not force the base arrays
/// to match at the left write index.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_nf_00004_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_smt(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (assert (not (= i1 i2)))
        (assert (= (store a1 i1 v1) (store a2 i2 v2)))
        (assert (not (= (select a1 i1) (select a2 i1))))
        (check-sat)
        "#,
        "left write index remains satisfiable",
    )
}

/// SAT: equality of stores at different indices does not force the base arrays
/// to match at the right write index.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_nf_00005_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_smt(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (assert (not (= i1 i2)))
        (assert (= (store a1 i1 v1) (store a2 i2 v2)))
        (assert (not (= (select a1 i2) (select a2 i2))))
        (check-sat)
        "#,
        "right write index remains satisfiable",
    )
}

// ── SMT-COMP file-based invalid (SAT) storeinv soundness guards ──────────
//
// These benchmarks are `:status sat`. AY returning `unknown` or timing out is
// acceptable (completeness gap), but returning `unsat` is a soundness bug.

/// T1 nested-form size 2 (`:status sat`).
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00002_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00002_001.cvc.smt2",
    )
}

/// T1 nested-form size 4 (`:status sat`).
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00004_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00004_001.cvc.smt2",
    )
}

/// T1 nested-form size 5 (`:status sat`).
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00005_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00005_001.cvc.smt2",
    )
}

/// T1 nested-form size 6 (`:status sat`).
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00006_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00006_001.cvc.smt2",
    )
}

/// T1 nested-form size 7 (`:status sat`).
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00007_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00007_001.cvc.smt2",
    )
}

/// T1 nested-form size 10 (`:status sat`). Returns `unknown` (timeout) —
/// guards against future false-UNSAT if scalability improves.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_storeinv_invalid_t1_nf_00010_must_not_be_unsat_6546() -> Result<()> {
    assert_release_not_unsat_file(
        "benchmarks/smtcomp/QF_AUFLIA/storeinv_invalid_t1_pp_nf_ai_00010_001.cvc.smt2",
    )
}

/// Current-head AUFLIA SAT repro from `#4906`: a store permutation with an
/// extra write must stay SAT in release mode.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_auflia_model_equality_no_sort_panic_release_sat_6546() -> Result<()> {
    assert_release_sat_smt(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun base () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)

        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun b1 () (Array Int Int))
        (declare-fun b2 () (Array Int Int))
        (declare-fun b3 () (Array Int Int))

        (assert (= a1 (store base 1 v1)))
        (assert (= a2 (store a1 2 v2)))
        (assert (= b1 (store base 2 v2)))
        (assert (= b2 (store b1 1 v1)))
        (assert (= b3 (store b2 3 v3)))
        (assert (not (= a2 b3)))
        (check-sat)
        "#,
        "store permutation with extra store",
    )
}

/// Current-head AUFLIA symbolic-index SAT repro from `#4906`: the release
/// executor must not regress on the richer store-permutation path.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn test_auflia_model_equality_symbolic_indices_release_sat_6546() -> Result<()> {
    assert_release_sat_smt(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun base () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun i3 () Int)
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)

        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun b1 () (Array Int Int))
        (declare-fun b2 () (Array Int Int))
        (declare-fun b3 () (Array Int Int))

        (assert (distinct i1 i2))
        (assert (distinct i1 i3))
        (assert (distinct i2 i3))
        (assert (= a1 (store base i1 v1)))
        (assert (= a2 (store a1 i2 v2)))
        (assert (= b1 (store base i2 v2)))
        (assert (= b2 (store b1 i1 v1)))
        (assert (= b3 (store b2 i3 v3)))
        (assert (not (= a2 b3)))
        (check-sat)
        "#,
        "symbolic-index store permutation",
    )
}
