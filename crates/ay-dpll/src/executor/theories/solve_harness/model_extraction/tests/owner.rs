// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These controls meter only the extraction callback, not the mock pipeline's
//! SAT/preparation/search work. They do not install an original native owner.

use super::fixture::{setup, Counts};
use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn extraction_query(result: ExecResult<SolveResult>) -> std::result::Result<(), QueryError> {
    match result {
        Err(ExecutorError::ModelExtraction(error)) => Err(error),
        _ => Err(QueryError::Invalid("fixture expected terminal extraction")),
    }
}

#[test]
fn same_owner_work_exhaustion_is_terminal_across_clone_and_raw_stop_reset() {
    let raw = Arc::new(AtomicBool::new(false));
    let stop = Arc::clone(&raw);
    let end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(1, 1024),
        end,
        Arc::new(move || stop.load(Ordering::SeqCst)),
    );
    let clone = owner.clone();
    let mut exec = setup();
    exec.solve_deadline.set(Some(end));
    let counts = Arc::new(Counts::default());
    let first = owner.with_work(|work| {
        extraction_query(exec.checked_mock_incremental(&counts, || {
            work.charge(2)?;
            Ok(TheoryModels::default())
        }))
    });
    assert_eq!(
        first,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    raw.store(false, Ordering::SeqCst);
    let second = clone.with_work(|_| {
        counts.extracts.fetch_add(1, Ordering::SeqCst);
        Ok(())
    });
    assert_eq!(second, first);
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert!(exec.last_model.is_none());
    assert!(exec.last_result().is_none());
}

#[test]
fn same_owner_storage_refusal_never_becomes_a_candidate_unknown() {
    let end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let owner = OriginalAdmission::new(FiniteAdmissionGrant::new(1024, 0), end, Arc::new(|| false));
    let mut exec = setup();
    exec.solve_deadline.set(Some(end));
    let counts = Arc::new(Counts::default());
    let result = owner.with_work(|work| {
        extraction_query(exec.checked_mock_persistent(&counts, || {
            work.admit(0, 1)?;
            Ok(TheoryModels::default())
        }))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert_eq!(counts.unsets.load(Ordering::SeqCst), 1);
    assert!(exec.last_result().is_none());
    assert!(exec.last_model.is_none());
    assert_eq!(owner.check(), result);
}

#[test]
fn original_precise_deadline_refusal_survives_reset_and_future_zero_offer() {
    let mut exec = setup();
    let stopped = std::cell::Cell::new(true);
    let mut sink = |_: usize, _: usize| {
        if stopped.get() {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut work = ay_core::original_query::WorkBudget::with_admission(1024, &mut sink);
    let counts = Arc::new(Counts::default());
    assert_terminal(
        exec.checked_mock_incremental(&counts, || {
            work.charge(0)?;
            Ok(TheoryModels::default())
        }),
        QueryError::Interrupted(StopReason::Deadline),
    );
    stopped.set(false);
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    assert_eq!(counts.extracts.load(Ordering::SeqCst), 1);
    assert!(exec.last_result().is_none());
    assert!(exec.last_model.is_none());
}
