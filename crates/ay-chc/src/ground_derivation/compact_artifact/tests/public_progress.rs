// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

fn proof_run() -> crate::ChcPdrProofRun {
    let (problem, derivation, mut owner) = fixture(2);
    compact::validate(&problem, &derivation, &mut owner).expect("original source validation");
    let evidence = compact::CompactEvidence::new(derivation, owner);
    let counterexample =
        crate::Counterexample::new(Vec::new()).with_compact_ground_derivation(evidence);
    crate::ChcPdrProofRun::new(
        problem,
        crate::VerifiedChcResult::Unsafe(crate::VerifiedCounterexample::from_validated(
            counterexample,
        )),
        "compact-public-export-test",
    )
}

#[test]
fn public_precancellation_precedes_malformed_bytes() {
    let calls = Cell::new(0);
    let error = validate_chc_compact_ground_derivation_artifact_with_progress(
        &ChcProblem::new(),
        b"{",
        &mut || {
            calls.set(calls.get() + 1);
            false
        },
    )
    .expect_err("the borrowed caller refuses before JSON parsing");
    assert_eq!(error.reason, Reason::Interrupted);
    assert_eq!(calls.get(), 1);
}

#[test]
fn public_borrowed_callback_stops_within_decode_or_original_replay() {
    let (problem, artifact) = artifact(3);
    let calls = Cell::new(0);
    validate_chc_compact_ground_derivation_artifact_with_progress(
        &problem,
        artifact.bytes(),
        &mut || {
            calls.set(calls.get() + 1);
            true
        },
    )
    .expect("healthy public replay");
    assert!(
        calls.get() > 80,
        "callback must cover internal work, not just phases"
    );
    for stop_at in [1, 8, 40, 80] {
        calls.set(0);
        let error = validate_chc_compact_ground_derivation_artifact_with_progress(
            &problem,
            artifact.bytes(),
            &mut || {
                calls.set(calls.get() + 1);
                calls.get() != stop_at
            },
        )
        .expect_err("no partial validated capability on callback refusal");
        assert_eq!(error.reason, Reason::Interrupted);
        assert_eq!(calls.get(), stop_at, "refusal cannot resume the callback");
    }
}

#[test]
fn public_callback_panic_returns_no_validated_evidence() {
    let (problem, artifact) = artifact(2);
    let calls = Cell::new(0);
    let error = validate_chc_compact_ground_derivation_artifact_with_progress(
        &problem,
        artifact.bytes(),
        &mut || {
            calls.set(calls.get() + 1);
            if calls.get() == 40 {
                panic!("caller interrupted during compact replay");
            }
            true
        },
    )
    .expect_err("caught callback panic is a refusal, never authority");
    assert_eq!(error.reason, Reason::Interrupted);
    assert_eq!(calls.get(), 40);
}

#[test]
fn public_snapshot_checks_after_inner_decoder_and_scratch_cleanup() {
    let (problem, artifact) = artifact(2);
    let inner_calls = Cell::new(0usize);
    let original = Owner::capture().expect("healthy original owner");
    let mut count = || {
        inner_calls.set(inner_calls.get() + 1);
        true
    };
    let checked = validate_with_owner(
        &problem,
        artifact.bytes(),
        &mut original.with_progress(&mut count),
    )
    .expect("inner validation completes before its envelope is destroyed");
    drop(checked);
    let publication_poll = inner_calls.get() + 1;

    for panics in [false, true] {
        let calls = Cell::new(0);
        let failure = validate_chc_compact_ground_derivation_artifact_with_progress(
            &problem,
            artifact.bytes(),
            &mut || {
                calls.set(calls.get() + 1);
                if calls.get() == publication_poll {
                    assert!(!panics, "stop at the post-cleanup publication fence");
                    return false;
                }
                true
            },
        )
        .expect_err("a complete inner replay cannot bypass the cleanup fence");
        assert_eq!(failure.reason, Reason::Interrupted);
        assert_eq!(calls.get(), publication_poll);
    }
}

#[test]
fn export_first_callback_false_and_panic_permanently_refuse_original_owner() {
    for panics in [false, true] {
        let run = proof_run();
        let calls = Cell::new(0);
        let error = run
            .unsafe_compact_ground_derivation_artifact_bytes_with_progress(&mut || {
                calls.set(calls.get() + 1);
                assert!(!panics, "caller refused by unwind before publication");
                false
            })
            .expect_err("first borrowed refusal is terminal");
        assert_eq!(error.reason, Reason::Interrupted);
        assert_eq!(calls.get(), 1);
        assert!(
            run.unsafe_compact_ground_derivation_artifact_bytes()
                .is_err(),
            "same carried witness cannot revive with a new callback"
        );
    }
}

#[test]
fn export_new_ambient_refusal_before_callback_attachment_is_retained() {
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    let run = proof_run();
    let one_shot = Arc::new(AtomicBool::new(true));
    {
        let signal = Arc::clone(&one_shot);
        let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
            signal.swap(false, Ordering::AcqRel)
        }));
        assert!(run
            .unsafe_compact_ground_derivation_artifact_bytes()
            .is_err());
    }
    assert!(!one_shot.load(Ordering::Acquire));
    assert!(
        run.unsafe_compact_ground_derivation_artifact_bytes()
            .is_err(),
        "pre-attachment ambient refusal is not silently forgotten"
    );
}
