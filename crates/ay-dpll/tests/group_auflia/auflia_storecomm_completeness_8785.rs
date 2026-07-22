// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Narrow #8785 coverage for the remaining QF_AUFLIA `storecomm_invalid`
//! completeness/performance blocker.
//!
//! The SMT-COMP `storecomm_invalid` fixtures are annotated `:status sat` and Z3
//! returns `sat`. AY must not return false `unsat`; exact `sat` remains the
//! desired completeness target where the local benchmark corpus is available.

use anyhow::{Context, Result};
use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common::{
    run_executor_file_with_timeout, run_executor_smt_with_timeout, workspace_path, SolverOutcome,
};

const STORECOMM_INVALID_30_008: &str =
    "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2";
const STORECOMM_INVALID_10_001: &str =
    "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00010_001.cvc.smt2";
const STORECOMM_VALID_10_001: &str =
    "benchmarks/smtcomp/QF_AUFLIA/storecomm_t3_pp_sf_ni_00010_001.cvc.smt2";
const STORECOMM_INVALID_30_008_TRACKED: &str =
    include_str!("data/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2");

#[test]
#[ntest::timeout(10_000)]
fn test_row2_exact_select_conflict_is_unsat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (not (= i j)))
        (assert (not (= (select (store a i 7) j) (select a j))))
        (check-sat)
        "#,
        5,
    )?;

    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#8785 ROW2 exact-select conflict must be discharged by array reasoning, got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_row2_inline_conflict_with_lia_derived_index_diseq_is_unsat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (= j (+ i 1)))
        (assert (not (= (select (store a i 7) j) (select a j))))
        (check-sat)
        "#,
        5,
    )?;

    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#8785 inline ROW2 conflict must use the LIA-derived i != j reason, got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_store_permutation_exact_select_conflict_is_unsat_9177() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun k () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert (= lhs (store (store a 1 e1) 2 e2)))
        (assert (= rhs (store (store a 2 e2) 1 e1)))
        (assert (= k (sk lhs rhs)))
        (assert (not (= (select lhs k) (select rhs k))))
        (check-sat)
        "#,
        5,
    )?;

    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#9177 store-permutation arrays are extensionally equal, so exact-select disequality must be UNSAT; got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_row2_conflict_through_explicit_store_chain_reason_is_unsat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (= b (store a i 7)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
        "#,
        5,
    )?;

    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#8785 explicit array equality + ROW2 store-chain reason must be UNSAT, got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_storecomm_invalid_minimized_index_alias_sat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun l1 () (Array Int Int))
        (declare-fun l2 () (Array Int Int))
        (declare-fun l3 () (Array Int Int))
        (declare-fun r1 () (Array Int Int))
        (declare-fun r2 () (Array Int Int))
        (declare-fun r3 () (Array Int Int))
        (assert (= l1 (store a 1 e1)))
        (assert (= l2 (store l1 2 e2)))
        (assert (= l3 (store l2 1 e1)))
        (assert (= r1 (store a 3 e3)))
        (assert (= r2 (store r1 2 e2)))
        (assert (= r3 (store r2 1 e1)))
        (declare-fun i () Int)
        (assert (= i 3))
        (assert (not (= (select l3 i) (select r3 i))))
        (check-sat)
        "#,
        5,
    )?;

    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "#8785 minimized storecomm SAT target with index alias i=3 must not return {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_storecomm_invalid_index_alias_model_keeps_original_binding_8785() -> Result<()> {
    let commands = parse(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-models true)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun l1 () (Array Int Int))
        (declare-fun l2 () (Array Int Int))
        (declare-fun l3 () (Array Int Int))
        (declare-fun r1 () (Array Int Int))
        (declare-fun r2 () (Array Int Int))
        (declare-fun r3 () (Array Int Int))
        (assert (= l1 (store a 1 e1)))
        (assert (= l2 (store l1 2 e2)))
        (assert (= l3 (store l2 1 e1)))
        (assert (= r1 (store a 3 e3)))
        (assert (= r2 (store r1 2 e2)))
        (assert (= r3 (store r2 1 e1)))
        (declare-fun i () Int)
        (assert (= i 3))
        (assert (not (= (select l3 i) (select r3 i))))
        (check-sat)
        (get-value (i))
        "#,
    )
    .context("parse minimized index-alias model regression")?;
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .context("execute minimized index-alias model regression")?;
    let transcript = output.join("\n");

    assert!(
        output.iter().any(|line| line.trim() == "sat"),
        "#8785 minimized storecomm SAT target should return sat.\nTranscript:\n{transcript}",
    );
    assert!(
        output.iter().any(|line| line.trim() == "((i 3))"),
        "#8785 alias substitution must recover the original `(= i 3)` model binding.\nTranscript:\n{transcript}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(10_000)]
fn test_storecomm_invalid_minimized_skolem_witness_sat_model_8785() -> Result<()> {
    let commands = parse(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-models true)
        (declare-fun a () (Array Int Int))
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun l1 () (Array Int Int))
        (declare-fun r1 () (Array Int Int))
        (assert (= l1 (store a 1 e1)))
        (assert (= r1 (store a 2 e2)))
        (declare-fun i () Int)
        (assert (= i (sk l1 r1)))
        (assert (not (= (select l1 i) (select r1 i))))
        (check-sat)
        (get-value (i))
        "#,
    )
    .context("parse minimized Skolem-witness storecomm regression")?;
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .context("execute minimized Skolem-witness storecomm regression")?;
    let transcript = output.join("\n");
    let status = output
        .iter()
        .map(|line| line.trim())
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"));

    assert_ne!(
        status,
        Some("unsat"),
        "SOUNDNESS BUG (#8785): minimized storecomm SAT target with UF Skolem witness must not return false unsat.\nTranscript:\n{transcript}",
    );
    match status {
        Some("sat") => assert!(
            output
                .iter()
                .any(|line| matches!(line.trim(), "((i 1))" | "((i 2))")),
            "#8785 Skolem witness model should recover a concrete store index for i.\nTranscript:\n{transcript}",
        ),
        Some("unknown") => assert!(
            output
                .iter()
                .any(|line| line.contains("model is not available")),
            "#8785 unknown result should reject get-value instead of fabricating a model.\nTranscript:\n{transcript}",
        ),
        other => panic!(
            "#8785 minimized storecomm SAT target should return a solver status, got {other:?}.\nTranscript:\n{transcript}"
        ),
    }
    Ok(())
}

#[test]
#[ntest::timeout(15_000)]
fn test_storecomm_invalid_two_store_skolem_no_false_unsat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun i () Int)
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (declare-fun l1 () (Array Int Int))
        (declare-fun l2 () (Array Int Int))
        (declare-fun r1 () (Array Int Int))
        (declare-fun r2 () (Array Int Int))
        (assert (= l1 (store a1 1 e1)))
        (assert (= l2 (store l1 1 e1)))
        (assert (= r1 (store a1 2 e2)))
        (assert (= r2 (store r1 1 e1)))
        (assert (= i (sk l2 r2)))
        (assert (not (= (select l2 i) (select r2 i))))
        (check-sat)
        "#,
        10,
    )?;

    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG (#8785): two-store storecomm Skolem witness is SAT (Z3 returns sat with i=2), but ay returned false UNSAT",
    );
    assert!(
        matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown | SolverOutcome::Timeout),
        "#8785 two-store storecomm Skolem witness should return a bounded solver outcome, got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(20_000)]
fn test_storecomm_invalid_10_001_smallest_live_sat_target_8785() -> Result<()> {
    let path = workspace_path(STORECOMM_INVALID_10_001);
    if !path.exists() {
        eprintln!(
            "skipping optional storecomm_invalid benchmark not checked into repo: {}",
            path.display()
        );
        return Ok(());
    }

    let outcome = run_executor_file_with_timeout(&path, 8)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "#8785 smallest checked-in storecomm_invalid SAT target should match Z3 `sat`; got {outcome:?}"
    );
    Ok(())
}

#[test]
#[ntest::timeout(20_000)]
fn test_storecomm_valid_10_001_smallest_live_unsat_target_9177() -> Result<()> {
    let path = workspace_path(STORECOMM_VALID_10_001);
    if !path.exists() {
        eprintln!(
            "skipping optional storecomm benchmark not checked into repo: {}",
            path.display()
        );
        return Ok(());
    }

    let outcome = run_executor_file_with_timeout(&path, 8)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#9177 smallest checked-in storecomm valid target should match Z3 `unsat`; got {outcome:?}"
    );
    Ok(())
}

#[test]
#[ntest::timeout(20_000)]
fn test_storecomm_invalid_30_008_bounded_no_false_unsat_8785() -> Result<()> {
    let path = workspace_path(STORECOMM_INVALID_30_008);
    if !path.exists() {
        eprintln!(
            "skipping optional storecomm_invalid benchmark not checked into repo: {}",
            path.display()
        );
        return Ok(());
    }

    let outcome = run_executor_file_with_timeout(&path, 8)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "#8785 storecomm_invalid_30_008 should match Z3 `sat`; got {outcome:?}"
    );
    Ok(())
}

#[test]
#[ntest::timeout(20_000)]
fn test_storecomm_invalid_30_008_tracked_fixture_no_false_unsat_8785() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(STORECOMM_INVALID_30_008_TRACKED, 8)
        .context("execute tracked #8785 storecomm_invalid_30_008 fixture")?;
    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "SOUNDNESS BUG (#8785): tracked storecomm_invalid_30_008 is SAT according to Z3; AY must not report UNSAT",
    );
    assert!(
        matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown),
        "#8785 tracked storecomm_invalid_30_008 should solve SAT or fail closed as Unknown; got {outcome:?}",
    );
    Ok(())
}

#[test]
#[ntest::timeout(25_000)]
fn test_storecomm_invalid_30_008_tracks_open_sat_target_8785() -> Result<()> {
    let path = workspace_path(STORECOMM_INVALID_30_008);
    if !path.exists() {
        eprintln!(
            "skipping optional storecomm_invalid benchmark not checked into repo: {}",
            path.display()
        );
        return Ok(());
    }

    let outcome = run_executor_file_with_timeout(&path, 10)
        .with_context(|| format!("ay executor failed on {}", path.display()))?;
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "#8785 tracked SAT target should match Z3 `sat`; got {outcome:?}"
    );
    Ok(())
}
