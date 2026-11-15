// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bundle::retained::{replay_exact_bundle, ExactInventoryError};

fn exact(bytes: &[u8]) -> OwningOutcome<BundleReCheck, ReadError> {
    replay_exact_bundle(bytes, &limits(), &wire(), end(), &mut |_, _| true)
}

fn mismatched_bytes() -> Vec<u8> {
    let mut snapshot = boolean_bundle();
    snapshot.obligation_assertions.reverse();
    encoded(&snapshot, Vec::new())
}

#[test]
fn general_replay_accepts_overbroad_reordered_and_duplicate_inventories_but_exact_refuses() {
    let base = boolean_bundle();
    let [positive, negative] = base.obligation_assertions.as_slice() else {
        panic!("two authored assumptions");
    };
    let before = producer_test_counter::count();
    for inventory in [
        vec![*positive, *negative, base.true_term.unwrap()],
        vec![*negative, *positive],
        vec![*positive, *negative, *positive],
    ] {
        let mut snapshot = base.clone();
        snapshot.obligation_assertions = inventory;
        let bytes = encoded(&snapshot, Vec::new());
        let general = checked(&bytes).result.unwrap();
        assert!(general.quality.is_complete());
        assert_eq!(general.assume_terms, [*positive, *negative]);
        let refused = exact(&bytes);
        assert!(matches!(
            refused.result,
            Err(ReadError::Inventory(ExactInventoryError::Mismatch))
        ));
        assert!(refused.usage.decoded_owner_reservation_bytes.is_some());
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn repeated_and_unused_assumes_keep_their_slots_but_inventory_uses_first_occurrences() {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("exact-duplicates", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_assume(positive, None);
    proof.add_resolution(Vec::new(), positive, left, right);
    let snapshot = SerializableProofBundle::from_proof(&proof, &terms, vec![positive, negative]);
    let bytes = encoded(&snapshot, Vec::new());
    drop((snapshot, proof, terms));
    let before = producer_test_counter::count();
    let checked = exact(&bytes).result.unwrap();
    assert!(checked.quality.is_complete());
    assert_eq!(checked.quality.assume_count, 4);
    assert_eq!(
        checked.assume_terms,
        [positive, positive, negative, positive]
    );
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn general_authored_conjunction_closure_is_not_silently_normalized_by_exact_reader() {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("exact-conjunction", Sort::Bool);
    let negative = terms.mk_not(positive);
    let conjunction = terms.mk_app(Symbol::named("and"), [positive, negative], Sort::Bool);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(Vec::new(), positive, left, right);
    let snapshot = SerializableProofBundle::from_proof(&proof, &terms, vec![conjunction]);
    let bytes = encoded(&snapshot, Vec::new());
    assert_eq!(
        checked(&bytes).result.unwrap().assume_terms,
        [positive, negative]
    );
    assert!(matches!(
        exact(&bytes).result,
        Err(ReadError::Inventory(ExactInventoryError::Mismatch))
    ));
}

#[test]
fn exact_retained_reads_outlive_source_owners_and_never_replace_proof_evidence() {
    let before = producer_test_counter::count();
    let (bytes, expected) = {
        let snapshot = bundle();
        let (expected, payloads) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
        assert_eq!(payloads.len(), 1);
        (encoded(&snapshot, payloads), expected)
    };
    assert_eq!(producer_test_counter::count(), before + 1);
    for _ in 0..2 {
        let actual = exact(&bytes).result.unwrap();
        assert_eq!(actual.quality, expected.quality);
        assert_eq!(actual.assume_terms, expected.assume_terms);
        assert_eq!(producer_test_counter::count(), before + 1);
    }
    let mut missing: Value = serde_json::from_slice(&bytes).unwrap();
    missing["retained"] = json!([]);
    let missing = serde_json::to_vec(&missing).unwrap();
    assert!(matches!(exact(&missing).result, Err(ReadError::Proof(_))));
    assert_eq!(producer_test_counter::count(), before + 1);
}

#[test]
fn comparator_work_is_added_once_without_new_storage_or_a_renewed_caller_grant() {
    let bytes = boolean_bytes();
    let general = measured_replay(&bytes);
    let baseline = exact(&bytes);
    assert!(baseline.result.is_ok());
    let usage = baseline.usage;
    // [p,!p]: initial + (position,first) + (position,prior,first) + final.
    assert_eq!(usage.charged_work, general.charged_work + 7);
    assert_eq!(usage.charged_bytes, general.charged_bytes);
    assert_eq!(
        usage.decoded_owner_reservation_bytes,
        general.decoded_owner_reservation_bytes
    );
    let mut outer = limits();
    outer.max_work = u64::try_from(usage.charged_work).unwrap();
    outer.max_storage_bytes = usage.charged_bytes;
    let accepted = replay_exact_bundle(&bytes, &outer, &wire(), end(), &mut |_, _| true);
    assert!(accepted.result.is_ok());
    assert_eq!(accepted.usage, usage);
    outer.max_work -= 1;
    assert!(
        replay_bundle(&bytes, &outer, &wire(), end(), &mut |_, _| true)
            .result
            .is_ok()
    );
    let refused = replay_exact_bundle(&bytes, &outer, &wire(), end(), &mut |_, _| true);
    assert!(matches!(
        refused.result,
        Err(ReadError::Transport(TransportError::Limit { .. }))
    ));
    assert_eq!(refused.usage.charged_work, usage.charged_work);
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
        replay_exact_bundle(&bytes, &limits(), &wire(), end(), &mut progress)
            .result
            .unwrap();
        assert!(matches!(
            replay_exact_bundle(&bytes, &limits(), &wire(), end(), &mut progress).result,
            Err(ReadError::Transport(TransportError::Refused))
        ));
    }
}

#[test]
fn all_original_deadlines_apply_before_decode_or_inventory_comparison() {
    let bytes = mismatched_bytes();
    for first in 0..3 {
        let expired = Instant::now() - Duration::from_secs(1);
        let (mut outer, mut inner, mut deadline) = (limits(), wire(), end());
        match first {
            0 => deadline = expired,
            1 => outer.deadline = expired,
            2 => inner.deadline = expired,
            _ => unreachable!(),
        }
        let mut calls = 0;
        let outcome = replay_exact_bundle(&bytes, &outer, &inner, deadline, &mut |_, _| {
            calls += 1;
            true
        });
        assert!(matches!(
            outcome.result,
            Err(ReadError::Transport(TransportError::Deadline))
        ));
        assert_eq!(calls, 0);
        assert_eq!(outcome.usage, OwningUsage::default());
    }
}

#[test]
fn final_cleanup_stop_or_expiry_overrides_mismatch_without_refunding_usage() {
    let bytes = mismatched_bytes();
    let mut total = 0;
    let baseline = replay_exact_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
        total += 1;
        true
    });
    assert!(matches!(
        baseline.result,
        Err(ReadError::Inventory(ExactInventoryError::Mismatch))
    ));
    assert!(total > 2);
    for stop in [total - 1, total] {
        let mut calls = 0;
        let stopped = replay_exact_bundle(&bytes, &limits(), &wire(), end(), &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(
            stopped.result,
            Err(ReadError::Transport(TransportError::Refused))
        ));
        assert_eq!(calls, stop);
        assert_eq!(stopped.usage, baseline.usage);
    }
    let deadline = Instant::now() + Duration::from_secs(1);
    let mut calls = 0;
    let expired = replay_exact_bundle(&bytes, &limits(), &wire(), deadline, &mut |_, _| {
        calls += 1;
        if calls == total {
            std::thread::sleep(
                deadline.saturating_duration_since(Instant::now()) + Duration::from_millis(1),
            );
        }
        true
    });
    assert!(matches!(
        expired.result,
        Err(ReadError::Transport(TransportError::Deadline))
    ));
    assert_eq!(calls, total);
    assert_eq!(expired.usage, baseline.usage);
}
