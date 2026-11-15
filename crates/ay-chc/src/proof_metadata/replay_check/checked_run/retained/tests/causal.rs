// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Causal diagnostics only; these private fixtures cannot mint proof authority.

use super::*;

#[test]
fn existing_error_keeps_its_cause_when_terminal_callback_refuses() {
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
    let result: ChcResult<()> = Err(verification_error("original retained row rejection"));
    let error = finish_validation(&mut progress, result).unwrap_err();
    assert!(error
        .to_string()
        .contains("original retained row rejection"));
    assert!(
        calls.get() > before,
        "the terminal original owner was still polled"
    );
    let stopped_calls = calls.get();
    allow.set(true);
    assert!(progress.check().is_err());
    assert_eq!(
        calls.get(),
        stopped_calls,
        "no callback/grant renewal after refusal"
    );
}

#[test]
fn existing_error_after_latched_refusal_never_reenters_the_owner() {
    let allow = Cell::new(true);
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allow.get()
    };
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    allow.set(false);
    assert!(progress.check().is_err());
    let stopped_calls = calls.get();
    allow.set(true);
    let result: ChcResult<()> = Err(verification_error("underlying strict v4 replay rejection"));
    let error = finish_validation(&mut progress, result).unwrap_err();
    assert!(error
        .to_string()
        .contains("underlying strict v4 replay rejection"));
    assert_eq!(calls.get(), stopped_calls);
    assert!(progress.check().is_err());
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn successful_validation_is_revoked_by_a_late_original_stop() {
    let allow = Cell::new(true);
    let mut callback = || allow.get();
    let original = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    allow.set(false);
    assert!(finish_validation(&mut progress, Ok(17)).is_err());
    allow.set(true);
    assert!(progress.check().is_err());
    assert_eq!(progress.deadline(), original);
}

#[test]
fn completed_error_still_polls_the_original_owner_when_healthy() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let original = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    let before = calls.get();
    let result: ChcResult<()> = Err(verification_error("complete source rejection"));
    let error = finish_validation(&mut progress, result).unwrap_err();
    assert!(error.to_string().contains("complete source rejection"));
    assert!(calls.get() > before);
    assert_eq!(progress.deadline(), original);
}

#[test]
fn healthy_validation_preserves_the_value_and_original_deadline() {
    let mut callback = || true;
    let original = deadline();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(original), &mut callback).unwrap();
    assert_eq!(finish_validation(&mut progress, Ok(23)).unwrap(), 23);
    assert_eq!(progress.deadline(), original);
    progress.check().unwrap();
}

#[test]
fn malformed_retained_authority_keeps_its_actual_cause_at_terminal_refusal() {
    let calls = Cell::new(0usize);
    let refuse_at = Cell::new(usize::MAX);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() < refuse_at.get()
    };
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    // Validation's entry check has two existing owner callbacks; permit both
    // and refuse only the first callback of its post-rejection terminal check.
    refuse_at.set(calls.get() + 3);
    let row = row(b"private malformed fixture", b"private nonproof fixture");
    let payload = SealedReplayObligationPayload::Smt {
        obligation_identity_sha256: String::new(),
        query_bytes: Vec::new(),
        strict_bundle_bytes: None,
        alethe_bytes: None,
        source_authority: SmtSourceAuthority::Legacy,
    };
    let error = payload
        .validate_retained_with_resources(&row, &mut progress)
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("retained strict row lacks aligned live-query authority"));
    assert_eq!(
        calls.get(),
        refuse_at.get(),
        "terminal owner refusal was observed"
    );
    let stopped_calls = calls.get();
    refuse_at.set(usize::MAX);
    assert!(progress.check().is_err());
    assert_eq!(
        calls.get(),
        stopped_calls,
        "a malformed row never revives the owner"
    );
}
