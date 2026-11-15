// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing API error-record/finish/try-consumption boundaries only. No test
//! installs an owner, replaces the native producer, or injects a solver verdict.

use super::*;
use crate::api::Logic;
use crate::{ExecutorError, SolveResult};
use ay_core::original_query::{QueryError, StopReason};

fn record(solver: &mut Solver, error: QueryError) {
    solver.record_executor_failure_unknown(&ExecutorError::ModelExtraction(error));
}

#[test]
fn compatibility_finish_retains_each_exact_typed_extraction_cause() {
    for error in [
        QueryError::Exhausted,
        QueryError::Interrupted(StopReason::Cancelled),
        QueryError::Interrupted(StopReason::Deadline),
        QueryError::Invalid("flat closure refused"),
    ] {
        let mut solver = Solver::new(Logic::QfUf);
        record(&mut solver, error);
        let finished = solver.finish_verified_result(SolveResult::Unknown);
        assert_eq!(finished, SolveResult::Unknown);
        assert!(!finished.was_model_validated());
        assert!(!finished.has_sat_emission_witness());
        assert_eq!(solver.model_extraction_failure(), Some(error));
        assert!(!solver.executor.last_result_is_sat());
    }
}

#[test]
fn existing_try_consumption_returns_extraction_error_not_successful_unknown() {
    let mut solver = Solver::new(Logic::QfUf);
    let original = QueryError::Interrupted(StopReason::Deadline);
    record(&mut solver, original);
    let finished = solver.finish_verified_result(SolveResult::Unknown);
    let fallible = solver.fail_on_artifact_export(finished);
    assert!(matches!(fallible, Err(SolverError::ExecutorError(
        ExecutorError::ModelExtraction(error))) if error == original));
    assert_eq!(solver.model_extraction_failure(), Some(original));
}

#[test]
fn next_decision_boundary_and_both_resets_retire_retained_extraction_error() {
    let mut solver = Solver::new(Logic::QfUf);
    record(&mut solver, QueryError::Exhausted);
    solver.clear_last_solve_state(true, false);
    assert!(solver.model_extraction_failure().is_none());
    record(&mut solver, QueryError::Exhausted);
    solver
        .try_reset_assertions()
        .expect("normal reset assertions");
    assert!(solver.model_extraction_failure().is_none());
    record(&mut solver, QueryError::Exhausted);
    solver.try_reset().expect("normal full reset");
    assert!(solver.model_extraction_failure().is_none());
}

#[test]
fn unrelated_artifact_error_replaces_extraction_cause_and_keeps_legacy_contract() {
    let mut solver = Solver::new(Logic::QfUf);
    record(&mut solver, QueryError::Invalid("previous cohort"));
    solver.record_executor_failure_unknown(&ExecutorError::ArtifactExport(
        "original artifact refusal".to_owned(),
    ));
    assert!(solver.model_extraction_failure().is_none());
    let result = solver.fail_on_artifact_export(());
    assert!(matches!(result, Err(SolverError::ExecutorError(
        ExecutorError::ArtifactExport(detail))) if detail == "original artifact refusal"));
}

#[test]
fn caught_panic_supersedes_retained_typed_extraction_failure() {
    for error in [
        QueryError::Exhausted,
        QueryError::Interrupted(StopReason::Cancelled),
        QueryError::Interrupted(StopReason::Deadline),
        QueryError::Invalid("flat closure refused"),
    ] {
        let mut solver = Solver::new(Logic::QfUf);
        let result: Result<(), SolverError> = solver.catch_solve_panic(|solver| {
            record(solver, error);
            assert_eq!(solver.model_extraction_failure(), Some(error));
            panic!("unwind after recording extraction refusal");
        });
        assert!(matches!(result, Err(SolverError::SolverPanic(message))
            if message == "unwind after recording extraction refusal"));
        assert!(solver.model_extraction_failure().is_none());
        assert!(solver.last_artifact_export_error().is_none());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::InternalError));
        assert_eq!(
            solver.last_executor_error.as_deref(),
            Some("solver panic: unwind after recording extraction refusal")
        );
        assert!(solver.executor.last_result_is_unknown());
        assert!(solver.try_get_model_str().is_err());
        assert!(solver.model_for_consumer().is_none());
        assert!(solver.last_proof().is_none());
        assert!(solver.try_get_unsat_core().is_err());
        assert!(solver.unsat_assumptions().is_none());
    }
}
