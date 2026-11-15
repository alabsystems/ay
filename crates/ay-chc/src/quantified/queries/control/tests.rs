// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn shared_debits_use_parent_remaining_bytes_and_no_full_allowance_reservation() {
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    parent.debit(MAX_WORK - 2, MAX_BYTES - 3).unwrap();
    let shared = Control::with_source(deadline(), &token, &parent);
    assert!(shared.poll().is_ok());
    assert!(shared.charge(2, 3).is_ok());
    assert_eq!(shared.bytes_used(), 3);
    assert!(parent.debit(0, 0).is_some());
    assert!(shared.charge(0, 1).is_err());
    assert!(parent.poll().is_none());
    assert!(shared.charge(0, 0).is_err());
    assert_eq!(shared.bytes_used(), 3);
}

#[test]
fn comparison_work_has_no_sixty_four_byte_multiplier_and_new_adapters_cannot_reset_it() {
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    parent.debit(MAX_WORK / 2, 0).unwrap();
    {
        let first = Control::with_source(deadline(), &token, &parent);
        first.charge(MAX_WORK / 4, 0).unwrap();
        assert_eq!(first.bytes_used(), 0);
    }
    let second = Control::with_source(deadline(), &token, &parent);
    second.charge(MAX_WORK / 4, 64).unwrap();
    // The comparison consumed all remaining WORK, but only 64 copied bytes.
    parent.bytes(MAX_BYTES - 64).unwrap();
    assert!(parent.poll().is_some());
    let third = Control::with_source(deadline(), &token, &parent);
    assert!(third.charge(1, 0).is_err());
    assert!(second.poll().is_err());
    assert!(parent.poll().is_none());
}

#[test]
fn parent_changes_after_borrow_are_seen_before_any_local_copy_permission() {
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    let shared = Control::with_source(deadline(), &token, &parent);
    parent.bytes(MAX_BYTES).unwrap();
    assert!(shared.charge(0, 1).is_err());
    assert_eq!(shared.bytes_used(), 0);
    assert!(parent.poll().is_none());
    let fresh = SourceControl::new(deadline(), &token);
    assert!(Control::with_source(deadline(), &token, &fresh)
        .charge(1, 1)
        .is_ok());
}

#[test]
fn parent_deadline_and_cancellation_cannot_be_renewed_by_an_adapter() {
    let token = CancellationToken::new();
    let expired = SourceControl::new(Instant::now(), &token);
    let longer = Control::with_source(deadline(), &token, &expired);
    assert!(longer.poll().is_err());
    assert!(longer.charge(0, 0).is_err());
    let parent = SourceControl::new(deadline(), &token);
    let shared = Control::with_source(deadline(), &token, &parent);
    token.cancel();
    assert!(shared.poll().is_err());
    token.reset();
    assert!(parent.poll().is_none());
    assert!(shared.poll().is_err());
    assert!(Control::with_source(deadline(), &token, &parent)
        .poll()
        .is_err());
    assert!(!token.is_cancelled());
}

#[test]
fn local_refusal_stops_every_parent_phase_without_cancelling_the_user_token() {
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    let shared = Control::with_source(deadline(), &token, &parent);
    assert!(shared.refuse::<()>("invalid mapped source clause").is_err());
    assert!(parent.debit(0, 0).is_none());
    assert!(Control::with_source(deadline(), &token, &parent)
        .poll()
        .is_err());
    assert!(!token.is_cancelled());
    let fresh = SourceControl::new(deadline(), &token);
    let shorter = Control::with_source(Instant::now(), &token, &fresh);
    assert!(shorter.poll().is_err());
    assert!(fresh.poll().is_none());
    assert!(!token.is_cancelled());
    let fresh = SourceControl::new(deadline(), &token);
    let injected = Control::with_source(deadline(), &token, &fresh);
    injected.stop_at.set(Some(1));
    assert!(injected.poll().is_err());
    injected.stop_at.set(None);
    assert!(fresh.poll().is_none());
    assert!(injected.charge(0, 0).is_err());
    assert!(Control::new(deadline(), &token).poll().is_ok());
}

#[test]
fn standalone_control_retains_independent_exact_legacy_limits() {
    let token = CancellationToken::new();
    let standalone = Control::new(deadline(), &token);
    assert!(standalone.charge(MAX_WORK, MAX_BYTES).is_ok());
    assert!(standalone.charge(0, 0).is_ok());
    assert!(standalone.charge(0, 1).is_err());
    assert!(standalone.poll().is_err());
    assert!(Control::new(deadline(), &token).charge(1, 1).is_ok());
}
