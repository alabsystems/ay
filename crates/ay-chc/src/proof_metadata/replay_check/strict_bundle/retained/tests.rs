// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::ReplayLimit;
use ay_core::time::Instant;
use std::{cell::Cell, time::Duration};

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn rejected_query(source: &str, expected: &str) {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let obligation = ChcReplayObligation {
        name: "original-query-rejection".to_string(),
        kind: crate::ChcReplayObligationKind::Safety,
        clause_index: 0,
        smtlib: source.to_string(),
    };
    let error = discharge_retained(&obligation, &mut progress)
        .err()
        .expect("a rejected query cannot mint a retained discharge");
    assert!(error.to_string().contains(expected), "{error}");
    assert!(
        progress.check().is_err(),
        "the original refusal stays sticky"
    );
}

#[test]
fn sat_rejection_keeps_the_actual_unsat_discharge_cause() {
    rejected_query(
        "(assert true) (check-sat)",
        "retained obligation did not establish UNSAT",
    );
}

#[test]
fn non_plain_query_rejection_is_not_misreported_as_resource_exhaustion() {
    rejected_query(
        "(assert false) (check-sat) (check-sat)",
        "retained obligation is not a plain hard query",
    );
}

#[test]
fn terminal_stop_still_refuses_success_and_cannot_be_reset() {
    let allow = Cell::new(true);
    let mut callback = || allow.get();
    let original = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    allow.set(false);
    assert!(finish_discharge(&mut progress, Ok(())).is_err());
    allow.set(true);
    assert!(progress.check().is_err());
    assert_eq!(progress.deadline(), original);
}

#[test]
fn existing_error_survives_terminal_stop_without_reviving_the_owner() {
    let allow = Cell::new(true);
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allow.get()
    };
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let before = calls.get();
    allow.set(false);
    let result: ChcResult<()> = Err(verification_error("original proof rejection"));
    let error = finish_discharge(&mut progress, result).unwrap_err();
    assert!(error.to_string().contains("original proof rejection"));
    assert!(calls.get() > before, "the terminal owner was still polled");
    allow.set(true);
    assert!(progress.check().is_err());
}

#[test]
fn healthy_terminal_admission_preserves_the_original_deadline() {
    let mut callback = || true;
    let original = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    assert_eq!(finish_discharge(&mut progress, Ok(7)).unwrap(), 7);
    assert_eq!(progress.deadline(), original);
    progress.check().unwrap();
}
