// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn decode_reservation_includes_legacy_owners_but_is_not_charged_again_on_replay() {
    let mut snapshot = boolean_bundle();
    snapshot.term_entries.push((
        TermData::Const(Constant::String("λ".repeat(4096))),
        Sort::String,
    ));
    let bytes = encoded(&snapshot, Vec::new());
    drop(snapshot);
    let decode = measured_decode(&bytes);
    let replay = measured_replay(&bytes);
    assert!(decode.charged_bytes > 8192);
    assert_eq!(
        replay.decoded_owner_reservation_bytes,
        Some(decode.charged_bytes)
    );
    assert!(replay.charged_work > decode.charged_work);
    assert!(replay.charged_bytes > decode.charged_bytes);
    // This is parse/scratch/owner reservation history, not a live-capacity or
    // allocator/RSS measurement. Empty inventory plainly does not mean zero.
    let owned = decoded(&bytes).result.unwrap();
    let (mut work, mut storage) = (0usize, 0usize);
    replay_versioned(&owned, end(), &mut |w, b| {
        work = work.checked_add(w).unwrap();
        storage = storage.checked_add(b).unwrap();
        true
    })
    .unwrap();
    assert_eq!(replay.charged_work, decode.charged_work + work);
    assert_eq!(replay.charged_bytes, decode.charged_bytes + storage);
}

#[test]
fn complete_decode_exact_and_one_short_local_caps_are_nonvacuous() {
    let bytes = boolean_bytes();
    let usage = measured_decode(&bytes);
    assert!(usage.charged_work > 0 && usage.charged_bytes > 0);
    let mut exact = limits();
    exact.max_work = u64::try_from(usage.charged_work).unwrap();
    exact.max_storage_bytes = usage.charged_bytes;
    let accepted = decode_bundle(&bytes, &exact, &wire(), end(), &mut |_, _| true);
    assert!(accepted.result.is_ok());
    assert_eq!(accepted.usage, usage);
    for (work, storage) in [
        (usage.charged_work - 1, usage.charged_bytes),
        (usage.charged_work, usage.charged_bytes - 1),
    ] {
        let mut short = limits();
        short.max_work = u64::try_from(work).unwrap();
        short.max_storage_bytes = storage;
        let refused = decode_bundle(&bytes, &short, &wire(), end(), &mut |_, _| true);
        assert!(matches!(refused.result, Err(TransportError::Limit { .. })));
        assert_eq!(refused.usage.decoded_owner_reservation_bytes, None);
    }
}

#[test]
fn total_replay_caps_cannot_be_reset_after_decode_succeeds() {
    let bytes = boolean_bytes();
    let decode = measured_decode(&bytes);
    let replay = measured_replay(&bytes);
    assert!(replay.charged_work > decode.charged_work);
    assert!(replay.charged_bytes > decode.charged_bytes);
    let mut exact = limits();
    exact.max_work = u64::try_from(replay.charged_work).unwrap();
    exact.max_storage_bytes = replay.charged_bytes;
    let accepted = replay_bundle(&bytes, &exact, &wire(), end(), &mut |_, _| true);
    assert!(accepted.result.is_ok());
    assert_eq!(accepted.usage, replay);
    for (work, storage) in [
        (replay.charged_work - 1, replay.charged_bytes),
        (replay.charged_work, replay.charged_bytes - 1),
    ] {
        let mut short = limits();
        short.max_work = u64::try_from(work).unwrap();
        short.max_storage_bytes = storage;
        assert!(
            decode_bundle(&bytes, &short, &wire(), end(), &mut |_, _| true)
                .result
                .is_ok()
        );
        let refused = replay_bundle(&bytes, &short, &wire(), end(), &mut |_, _| true);
        assert!(matches!(
            refused.result,
            Err(ReadError::Transport(TransportError::Limit { .. }))
        ));
        assert_eq!(
            refused.usage.decoded_owner_reservation_bytes,
            decode.decoded_owner_reservation_bytes
        );
    }
}

#[test]
fn caller_work_and_storage_grants_remain_shared_across_independent_wire_reads() {
    let bytes = boolean_bytes();
    let usage = measured_replay(&bytes);
    let outer = limits();
    let inner = wire();
    let original_deadline = end();
    for (work_limit, byte_limit) in [
        (usage.charged_work, usize::MAX),
        (usize::MAX, usage.charged_bytes),
    ] {
        let (mut work, mut storage) = (0usize, 0usize);
        let mut progress = |w, b| {
            work = work.checked_add(w).unwrap();
            storage = storage.checked_add(b).unwrap();
            work <= work_limit && storage <= byte_limit
        };
        replay_bundle(&bytes, &outer, &inner, original_deadline, &mut progress)
            .result
            .unwrap();
        for _ in 0..2 {
            assert!(matches!(
                replay_bundle(&bytes, &outer, &inner, original_deadline, &mut progress).result,
                Err(ReadError::Transport(TransportError::Refused))
            ));
        }
    }
}

#[test]
fn minimum_of_all_three_original_deadlines_refuses_before_progress() {
    let bytes = boolean_bytes();
    let before = producer_test_counter::count();
    for earliest in 0..3 {
        let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
        let mut outer = limits();
        let mut inner = wire();
        let mut original = end();
        match earliest {
            0 => original = expired,
            1 => outer.deadline = expired,
            2 => inner.deadline = expired,
            _ => unreachable!(),
        }
        let mut calls = 0;
        let mut progress = |_, _| {
            calls += 1;
            true
        };
        let decode = decode_bundle(&bytes, &outer, &inner, original, &mut progress);
        let replay = replay_bundle(&bytes, &outer, &inner, original, &mut progress);
        assert!(matches!(decode.result, Err(TransportError::Deadline)));
        assert!(matches!(
            replay.result,
            Err(ReadError::Transport(TransportError::Deadline))
        ));
        assert_eq!(decode.usage, OwningUsage::default());
        assert_eq!(replay.usage, OwningUsage::default());
        assert_eq!(calls, 0);
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn decode_entry_interior_and_final_cleanup_stops_publish_no_owner() {
    let bytes = boolean_bytes();
    let mut total = 0;
    let baseline = decode_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
        total += 1;
        true
    });
    assert!(baseline.result.is_ok());
    assert!(total > 6);
    for stop in [1, 2, total / 2, total - 1, total] {
        let mut calls = 0;
        let refused = decode_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(refused.result, Err(TransportError::Refused)));
        assert_eq!(calls, stop);
        if stop == total {
            assert_eq!(refused.usage, baseline.usage);
            assert!(refused.usage.decoded_owner_reservation_bytes.is_some());
        }
    }
}

#[test]
fn replay_entry_interior_and_final_cleanup_stops_publish_no_certificate() {
    let bytes = boolean_bytes();
    let mut total = 0;
    let baseline = replay_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
        total += 1;
        true
    });
    assert!(baseline.result.is_ok());
    assert!(total > 6);
    let before = producer_test_counter::count();
    for stop in [1, 2, total / 2, total - 1, total] {
        let mut calls = 0;
        let refused = replay_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(
            refused.result,
            Err(ReadError::Transport(TransportError::Refused))
        ));
        assert_eq!(calls, stop);
        if stop == total {
            assert_eq!(refused.usage, baseline.usage);
            assert!(refused.usage.decoded_owner_reservation_bytes.is_some());
        }
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn final_transport_stop_overrides_a_semantic_error_without_erasing_reservations() {
    let mut invalid = boolean_bundle();
    invalid.obligation_assertions.clear();
    let bytes = encoded(&invalid, Vec::new());
    let mut total = 0;
    let baseline = replay_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
        total += 1;
        true
    });
    assert!(matches!(baseline.result, Err(ReadError::Proof(_))));
    assert!(baseline.usage.decoded_owner_reservation_bytes.is_some());
    assert!(total > 2);
    let mut calls = 0;
    let refused = replay_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
        calls += 1;
        calls != total
    });
    assert!(matches!(
        refused.result,
        Err(ReadError::Transport(TransportError::Refused))
    ));
    assert_eq!(calls, total);
    assert_eq!(refused.usage, baseline.usage);
}
