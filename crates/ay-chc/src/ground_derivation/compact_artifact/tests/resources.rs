// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

#[test]
fn retained_original_stop_cannot_be_replaced_before_encoding() {
    let (problem, derivation, _) = fixture(2);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let _original = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed) != 0
    }));
    let mut owner = Owner::capture().expect("first original poll allows");
    let _replacement = enter_check_stop(Arc::new(|| false));
    assert!(encode_with_owner(&problem, &derivation, &mut owner).is_err());
    assert!(owner.poll().is_err());
}

#[test]
fn cancellation_at_sampled_decode_boundaries_never_publishes_partial_evidence() {
    let (problem, artifact) = artifact(2);
    let bytes = artifact.into_bytes();
    let calls = Arc::new(AtomicUsize::new(0));
    {
        let observed = Arc::clone(&calls);
        let _scope = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::Relaxed);
            false
        }));
        let _ = validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
            .expect("healthy control");
    }
    let total = calls.load(Ordering::Relaxed);
    // Sample early, middle, and terminal polls of the complete decode.
    for stop_at in [0, 1, total / 4, total / 2, total.saturating_sub(1)] {
        let count = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&count);
        let _scope = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::Relaxed) >= stop_at
        }));
        let failure = validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
            .expect_err("original refusal");
        assert_eq!(failure.reason, Reason::Interrupted);
    }
}

#[test]
fn decode_preallocation_spends_original_memory_before_parsing() {
    let (problem, artifact) = artifact(2);
    let bytes = artifact.into_bytes();
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(1024));
    let failure = validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
        .expect_err("retained byte admission");
    assert_eq!(failure.reason, Reason::SourceWorkLimitExceeded);
}

#[test]
fn original_guard_ledger_spans_source_encoding_decoding_and_replay() {
    let (problem, derivation, _) = fixture(2);
    let original = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _entered = original.enter();
    let mut owner = Owner::capture().expect("original guard");
    let replacement = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _replaced = replacement.enter();
    encode_with_owner(&problem, &derivation, &mut owner).expect("whole round trip");
    assert!(original.ledger_ticks() > 0);
    assert_eq!(
        replacement.ledger_ticks(),
        0,
        "ambient replacement grants no new credit"
    );
}

#[test]
fn exact_and_short_original_guard_cover_the_whole_round_trip() {
    let (problem, derivation, _) = fixture(2);
    let used = {
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _entered = guard.enter();
        let mut owner = Owner::capture().expect("measure original owner");
        encode_with_owner(&problem, &derivation, &mut owner).expect("healthy round trip");
        guard.ledger_ticks()
    };
    assert!(used > 1);
    for (limit, expected) in [(used + 1, true), (used, false), (used - 1, false)] {
        let original = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(limit)));
        let _entered = original.enter();
        let mut owner = Owner::capture().expect("original finite grant");
        let replacement = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _replacement = replacement.enter();
        let result = encode_with_owner(&problem, &derivation, &mut owner);
        assert_eq!(
            result.is_ok(),
            expected,
            "original cumulative limit {limit}"
        );
        assert_eq!(replacement.ledger_ticks(), 0);
        if expected {
            assert_eq!(original.ledger_ticks(), used);
        } else {
            assert!(owner.poll().is_err(), "a short owner stays refused");
        }
    }
}
