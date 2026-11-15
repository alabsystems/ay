// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! In-memory v6 boundary only. Test-only snapshot serde below is intentionally
//! uncontrolled and is NOT evidence for a bounded owning wire decoder.

use super::*;
use crate::bundle::retained::{PresenceError, RetainedBundle, RetainedField, RETAINED_SCHEMA};
use crate::bv_blast_solver::retained::RetainedBvRefutation;

fn versioned(
    mut snapshot: SerializableProofBundle,
    payloads: Vec<RetainedStepPayload>,
) -> RetainedBundle {
    snapshot.schema = RETAINED_SCHEMA.to_owned();
    RetainedBundle::from_parts(snapshot, RetainedField::Present(payloads)).unwrap()
}

#[test]
fn constructor_requires_actual_v6_and_present_inventory_without_granting_validity() {
    for schema in [PROOF_BUNDLE_SCHEMA, "ay.proofbundle/v5", ""] {
        for field in [RetainedField::Absent, RetainedField::Present(Vec::new())] {
            let mut snapshot = bundle();
            snapshot.schema = schema.to_owned();
            assert!(RetainedBundle::from_parts(snapshot, field).is_err());
        }
    }
    let mut snapshot = bundle();
    snapshot.schema = RETAINED_SCHEMA.to_owned();
    assert!(matches!(
        RetainedBundle::from_parts(snapshot.clone(), RetainedField::Absent),
        Err(PresenceError::MissingRetainedField)
    ));
    // Presence is not proof authority: this source needs one retained lemma.
    let owned = RetainedBundle::from_parts(snapshot, RetainedField::Present(Vec::new())).unwrap();
    let before = producer_test_counter::count();
    assert!(replay_versioned(&owned, end(), &mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn present_empty_v6_inventory_replays_a_proof_with_no_retained_demand() {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("versioned-boolean", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(Vec::new(), positive, left, right);
    let snapshot = SerializableProofBundle::from_proof(&proof, &terms, vec![positive, negative]);
    let expected = re_check_bundle_strict(&snapshot).unwrap();
    let before = producer_test_counter::count();
    let owned = versioned(snapshot, Vec::new());
    let actual = replay_versioned(&owned, end(), &mut |_, _| true).unwrap();
    assert_eq!(actual.quality, expected.quality);
    assert_eq!(actual.assume_terms, expected.assume_terms);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn independent_owned_v6_reads_survive_producer_drop_without_legacy_normalization() {
    let before = producer_test_counter::count();
    let (source, expected, wire_rows) = {
        let mut snapshot = bundle();
        let (checked, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
        snapshot.schema = RETAINED_SCHEMA.to_owned();
        // Only serialize the test snapshot; the actual v6 inventory is owned
        // separately below. This is not the complete controlled wire format.
        let source = serde_json::to_vec(&snapshot).unwrap();
        let rows: Vec<_> = rows
            .into_iter()
            .map(|row| (row.step, row.payload))
            .collect();
        (source, checked, rows)
    };
    assert_eq!(producer_test_counter::count(), before + 1);
    assert_eq!(wire_rows.len(), 1);
    for _ in 0..2 {
        let snapshot: SerializableProofBundle = serde_json::from_slice(&source).unwrap();
        assert_eq!(snapshot.schema, RETAINED_SCHEMA);
        assert!(matches!(re_check_bundle_strict(&snapshot),
            Err(ProofCheckError::BundleSchemaMismatch { found, .. }) if found == RETAINED_SCHEMA));
        let rows = wire_rows
            .iter()
            .map(|(step, payload)| RetainedStepPayload {
                step: *step,
                payload: payload.clone(),
            })
            .collect();
        let owned = RetainedBundle::from_parts(snapshot, RetainedField::Present(rows)).unwrap();
        assert_eq!(owned.parts().0.schema, RETAINED_SCHEMA);
        assert!(matches!(re_check_bundle_strict(owned.parts().0),
            Err(ProofCheckError::BundleSchemaMismatch { found, .. }) if found == RETAINED_SCHEMA));
        let checked = replay_versioned(&owned, end(), &mut |_, _| true).unwrap();
        assert_eq!(checked.quality, expected.quality);
        assert_eq!(checked.assume_terms, expected.assume_terms);
        assert_eq!(owned.parts().0.schema, RETAINED_SCHEMA);
        assert_eq!(producer_test_counter::count(), before + 1);
        drop(owned);
    }
}

#[test]
fn missing_corrupt_extra_or_rebound_v6_evidence_never_falls_back() {
    let snapshot = bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    re_check_bundle_strict(&snapshot).unwrap();
    let before = producer_test_counter::count();
    let mut corrupt = rows.clone();
    corrupt[0].payload.clear();
    let mut invalid_dag = rows.clone();
    let mut decoded: RetainedBvRefutation =
        serde_json::from_slice(&invalid_dag[0].payload).unwrap();
    decoded.empty_clause_id = u64::MAX;
    invalid_dag[0].payload = serde_json::to_vec(&decoded).unwrap();
    let mut extra = rows.clone();
    extra.push(rows[0].clone());
    let mut rebound = rows.clone();
    rebound[0].step = 0; // The fixture's assumption, not the BV lemma.
    assert_ne!(rows[0].step, rebound[0].step);
    for inventory in [Vec::new(), corrupt, invalid_dag, extra, rebound] {
        let owned = versioned(snapshot.clone(), inventory);
        assert!(replay_versioned(&owned, end(), &mut |_, _| true).is_err());
    }
    let intact = versioned(snapshot, rows);
    replay_versioned(&intact, end(), &mut |_, _| true).unwrap();
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn v6_keeps_snapshot_context_assumption_and_terminal_checks() {
    let snapshot = bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let before = producer_test_counter::count();
    let mut malformed = snapshot.clone();
    malformed.true_term = Some(TermId(u32::MAX));
    let mut unauthorized = snapshot.clone();
    unauthorized.obligation_assertions.clear();
    let mut nonterminal = snapshot.clone();
    nonterminal.steps.pop();
    let mut context = snapshot;
    context
        .constructor_selectors
        .push(("unknown-constructor".to_owned(), vec!["field".to_owned()]));
    for invalid in [malformed, unauthorized, nonterminal, context] {
        let owned = versioned(invalid, rows.clone());
        assert!(replay_versioned(&owned, end(), &mut |_, _| true).is_err());
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn expired_v6_original_deadline_refuses_before_callbacks_or_search() {
    let owned = versioned(bundle(), Vec::new());
    let before = producer_test_counter::count();
    let mut calls = 0;
    assert!(matches!(
        replay_versioned(
            &owned,
            Instant::now() - Duration::from_secs(1),
            &mut |_, _| {
                calls += 1;
                true
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 0);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn v6_entry_inner_and_final_callback_refusals_are_terminal() {
    let snapshot = bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let owned = versioned(snapshot, rows);
    let before = producer_test_counter::count();
    let mut total = 0;
    replay_versioned(&owned, end(), &mut |_, _| {
        total += 1;
        true
    })
    .unwrap();
    assert!(total > 6);
    // Phase-local all-ordinal controls are in the bridge/codec; this boundary
    // pins entry, an interior checkpoint and final post-cleanup publication.
    for stop in [1, 2, 3, total / 2, total - 1, total] {
        let mut calls = 0;
        assert!(matches!(
            replay_versioned(&owned, end(), &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn v6_reads_cannot_renew_cumulative_work_or_byte_grants() {
    let snapshot = bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let owned = versioned(snapshot, rows);
    let original_deadline = end();
    let (mut work, mut bytes) = (0usize, 0usize);
    replay_versioned(&owned, original_deadline, &mut |w, b| {
        work = work.checked_add(w).unwrap();
        bytes = bytes.checked_add(b).unwrap();
        true
    })
    .unwrap();
    assert!(work > 0 && bytes > 0);
    let before = producer_test_counter::count();
    for (work_limit, byte_limit) in [(work, usize::MAX), (usize::MAX, bytes)] {
        let (mut used_work, mut used_bytes) = (0usize, 0usize);
        let mut progress = |w, b| {
            used_work = used_work.checked_add(w).unwrap();
            used_bytes = used_bytes.checked_add(b).unwrap();
            used_work <= work_limit && used_bytes <= byte_limit
        };
        replay_versioned(&owned, original_deadline, &mut progress).unwrap();
        for _ in 0..2 {
            assert!(matches!(
                replay_versioned(&owned, original_deadline, &mut progress),
                Err(ProofCheckError::ResourceLimit)
            ));
        }
    }
    assert_eq!(producer_test_counter::count(), before);
}
