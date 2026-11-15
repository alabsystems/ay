// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::Model;
use crate::executor_types::{Result as ExecResult, SolveResult};
use ay_core::original_query::{QueryError, StopReason};

mod fixture;
mod owner;
mod pipelines;
mod shared;

fn assert_terminal(result: ExecResult<SolveResult>, expected: QueryError) {
    assert!(matches!(result, Err(ExecutorError::ModelExtraction(error)) if error == expected));
}

#[test]
fn legacy_and_checked_success_move_the_same_payload_without_cloning() {
    let mut euf = ay_euf::EufModel::default();
    euf.term_values
        .insert(ay_core::TermId(7), "owned-model-value".to_owned());
    let original = euf.term_values[&ay_core::TermId(7)].as_ptr();
    let legacy = TheoryModels {
        euf: Some(euf),
        ..TheoryModels::default()
    };
    let moved = model_extraction_result(legacy).expect("legacy accepting transport");
    let checked = model_extraction_result(Ok(moved)).expect("checked accepting transport");
    assert_eq!(
        checked.euf.as_ref().unwrap().term_values[&ay_core::TermId(7)].as_ptr(),
        original
    );
}

#[test]
fn all_query_error_variants_remain_exact_typed_terminal_errors() {
    for error in [
        QueryError::Exhausted,
        QueryError::Interrupted(StopReason::Cancelled),
        QueryError::Interrupted(StopReason::Deadline),
        QueryError::Invalid("unsupported prepared extraction"),
    ] {
        let result = model_extraction_result(Err::<TheoryModels, _>(error));
        assert!(matches!(result, Err(actual) if actual == error));
        let mut exec = Executor::new();
        assert_terminal(Err(exec.terminal_model_extraction_error(error)), error);
        let public = crate::api::SolverError::from(ExecutorError::ModelExtraction(error));
        assert!(matches!(public, crate::api::SolverError::ExecutorError(
            ExecutorError::ModelExtraction(actual)) if actual == error));
    }
}

#[test]
fn terminal_refusal_retires_stale_result_model_and_all_sat_markers() {
    let mut exec = Executor::new();
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(Model::empty());
    exec.last_model_validated = true;
    exec.finite_table_cert_grant_active = true;
    exec.const_interp_cert_grant_active = true;
    let error = exec.terminal_model_extraction_error(QueryError::Exhausted);
    assert!(matches!(
        error,
        ExecutorError::ModelExtraction(QueryError::Exhausted)
    ));
    assert!(exec.last_result().is_none());
    assert!(exec.last_model.is_none());
    assert!(!exec.last_model_validated);
    assert!(exec.last_sat_certificate.is_none());
    assert!(exec.last_unsat_certificate.is_none());
    assert!(exec.dt_theory_model.is_none());
    assert!(!exec.finite_table_cert_grant_active);
    assert!(!exec.const_interp_cert_grant_active);
}
