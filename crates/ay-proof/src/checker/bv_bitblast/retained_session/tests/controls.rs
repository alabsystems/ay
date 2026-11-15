// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn every_inventory_and_slot_allocation_callback_refusal_is_terminal() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 2);
    let payloads = [
        RetainedStepPayload {
            step: 0,
            payload: vec![0],
        },
        RetainedStepPayload {
            step: 1,
            payload: vec![0],
        },
    ];
    for operation in [
        RetainedOperation::Capture,
        RetainedOperation::Replay(&payloads),
    ] {
        let count = Cell::new(0);
        let kind = || match operation {
            RetainedOperation::Capture => RetainedOperation::Capture,
            RetainedOperation::Replay(rows) => RetainedOperation::Replay(rows),
        };
        let admitted =
            RetainedSession::new(credits(&proof, &terms, deadline()), kind(), &mut |_, _| {
                count.set(count.get() + 1);
                true
            })
            .unwrap();
        drop(admitted);
        assert!(count.get() > 2);
        for stop_at in 1..=count.get() {
            let seen = Cell::new(0);
            assert!(RetainedSession::new(
                credits(&proof, &terms, deadline()),
                kind(),
                &mut |_, _| {
                    seen.set(seen.get() + 1);
                    seen.get() != stop_at
                },
            )
            .is_err());
            assert_eq!(seen.get(), stop_at, "refused callback must stay latched");
        }
    }
}

#[test]
fn replay_stop_including_final_callback_poison_session_without_search() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let payloads = capture(&terms, &proof);
    let calls = producer_test_counter::count();
    let count = Cell::new(0);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Replay(&payloads),
        &mut |_, _| true,
    )
    .unwrap();
    session
        .validate_step(ProofId(0), &mut |_, _| {
            count.set(count.get() + 1);
            true
        })
        .unwrap();
    session.finish(&mut |_, _| true).unwrap();
    let total = count.get();
    assert!(total > 6);
    // Phase-local exhaustive callback tests live in the bridge/codec. At this
    // integration boundary include entry, inner work and final publication.
    for stop_at in [1, 2, 3, total / 2, total - 1, total] {
        let seen = Cell::new(0);
        let mut session = RetainedSession::new(
            credits(&proof, &terms, deadline()),
            RetainedOperation::Replay(&payloads),
            &mut |_, _| true,
        )
        .unwrap();
        assert!(session
            .validate_step(ProofId(0), &mut |_, _| {
                seen.set(seen.get() + 1);
                seen.get() != stop_at
            })
            .is_err());
        assert_eq!(seen.get(), stop_at);
        assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
        assert!(session.finish(&mut |_, _| true).is_err());
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn caught_callback_panic_cannot_reuse_credit_or_publish_output() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let calls = producer_test_counter::count();
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _ = session.validate_step(ProofId(0), &mut |_, _| panic!("session stop"));
    }))
    .is_err());
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert!(session.finish(&mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn original_deadline_is_not_renewed_after_preparation_or_at_finish() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let end = Instant::now() + Duration::from_secs(1);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, end),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(session.original_deadline(), end);
    // Expire the original clock without starting proof search. This is a
    // bounded one-second test wait, not a per-lemma deadline or grace grant.
    while Instant::now() < end {
        std::thread::sleep(end.saturating_duration_since(Instant::now()));
    }
    let seen = Cell::new(0);
    let calls = producer_test_counter::count();
    assert_eq!(
        session.validate_step(ProofId(0), &mut |_, _| {
            seen.set(seen.get() + 1);
            true
        }),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(seen.get(), 0);
    assert_eq!(
        session.finish(&mut |_, _| true),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn finish_refusal_discards_successful_capture_instead_of_publishing_bytes() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    session.validate_step(ProofId(0), &mut |_, _| true).unwrap();
    assert_eq!(session.output.len(), 1);
    let calls = Cell::new(0);
    assert_eq!(
        session.finish(&mut |_, _| {
            calls.set(calls.get() + 1);
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 1);
}
