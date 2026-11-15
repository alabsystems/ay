// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const ROW_CAUSE: &str = "test-only earlier row source rejection";

#[test]
fn healthy_owner_observation_is_borrowed_none_and_adds_no_polls_or_debits() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let original = deadline();
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    let before = calls.get();
    for _ in 0..10 {
        assert_eq!(owner.diagnostic_refusal(), None);
    }
    assert_eq!(calls.get(), before);
    assert_eq!(owner.deadline(), original);
    finish_validation(&mut owner, Ok(())).unwrap();
    assert_eq!(calls.get(), before + 2); // Existing final charge, not the accessor.
    assert_eq!(owner.diagnostic_refusal(), None);
}

#[test]
fn recorded_callback_false_survives_the_earlier_row_error_and_callback_reset() {
    let calls = Cell::new(0usize);
    let allow = Cell::new(true);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allow.get()
    };
    let original = deadline();
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    allow.set(false);
    assert!(owner.check().is_err());
    let stopped_calls = calls.get();
    let first = owner.diagnostic_refusal();
    assert_eq!(
        first,
        Some("retained request original callback returned false")
    );
    let row_error = finish_validation::<()>(&mut owner, Err(verification_error(ROW_CAUSE)));
    assert!(row_error.unwrap_err().to_string().contains(ROW_CAUSE));
    allow.set(true);
    assert!(owner.check().is_err());
    assert_eq!(owner.diagnostic_refusal(), first);
    assert_eq!(calls.get(), stopped_calls);
    assert_eq!(owner.deadline(), original);
}

#[test]
fn actual_work_and_byte_overflow_keep_first_cause_without_reset_or_callback_reentry() {
    for (work, bytes, expected) in [
        (
            usize::MAX,
            0,
            "retained request cumulative work debit overflow",
        ),
        (
            0,
            usize::MAX,
            "retained request cumulative byte debit overflow",
        ),
    ] {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let original = deadline();
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
        let before = calls.get();
        assert!(!owner.charge(work, bytes)); // Real initial Rc debit makes this overflow.
        assert_eq!(owner.diagnostic_refusal(), Some(expected));
        let row_error = finish_validation::<()>(&mut owner, Err(verification_error(ROW_CAUSE)));
        assert!(row_error.unwrap_err().to_string().contains(ROW_CAUSE));
        assert_eq!(owner.diagnostic_refusal(), Some(expected));
        assert!(owner.check().is_err());
        assert_eq!(calls.get(), before);
        assert_eq!(owner.deadline(), original);
    }
}

#[test]
fn healthy_final_poll_preserves_semantic_row_error_without_inventing_owner_refusal() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let before = calls.get();
    let row_error = finish_validation::<()>(&mut owner, Err(verification_error(ROW_CAUSE)));
    assert!(row_error.unwrap_err().to_string().contains(ROW_CAUSE));
    assert_eq!(calls.get(), before + 2);
    assert_eq!(owner.diagnostic_refusal(), None);
}
