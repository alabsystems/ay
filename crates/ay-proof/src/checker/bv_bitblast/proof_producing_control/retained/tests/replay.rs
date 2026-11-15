// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;

#[test]
fn ordinary_live_clause_replays_after_producer_death_without_legacy_or_search_grants() {
    let producer_calls = producer_test_counter::count();
    let bytes = {
        let (terms, clause) = arithmetic(0);
        assert!(
            crate::checker::bv_bitblast::bv_bitblast_requires_proof_producer(&terms, &[clause])
        );
        let before = terms.entries_snapshot();
        let mut payload = capture(&terms, clause);
        assert!(payload.rows.len() > 1);
        assert_eq!(terms.entries_snapshot(), before);
        separate_derived_ids(&mut payload);
        // This test-only serialization is not a bounded wire API.
        serde_json::to_vec(&payload).unwrap()
    };
    assert_eq!(producer_test_counter::count(), producer_calls + 1);
    let producer_calls = producer_test_counter::count();
    let payload: RetainedBvRefutation = serde_json::from_slice(&bytes).unwrap();
    let (terms, clause) = arithmetic(0);
    let before = terms.entries_snapshot();
    let attempts = super::super::super::ATTEMPTS.with(Cell::get);
    replay(&terms, clause, Some(&payload)).unwrap();
    let end = deadline();
    let (mut proof, gates) = limits(end);
    // Replay does not consult producer search grants, even when absent.
    proof.resolution.max_conflicts = None;
    proof.resolution.max_decisions = None;
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    replay_clause(
        &terms,
        &[clause],
        Some(&payload),
        end,
        &proof,
        &gates,
        &mut || true,
    )
    .unwrap();
    assert_eq!(terms.entries_snapshot(), before);
    // The legacy-entry and common-producer counters cover distinct seams;
    // zero search grants alone cannot prove that the producer was not called.
    assert_eq!(super::super::super::ATTEMPTS.with(Cell::get), attempts);

    let (changed, neighbor) = arithmetic(1);
    assert!(matches!(
        replay(&changed, neighbor, Some(&payload)),
        Err(BridgeError::Refutation(BvExprExportError::RefutationNotSurfaceable(message)))
            if message.starts_with("bounded resolution proof failed:")
    ));
    assert_eq!(producer_test_counter::count(), producer_calls);
}

#[test]
fn live_reused_term_ids_do_not_authorize_the_old_source() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("retained_a", Sort::bitvec(8));
    let b = terms.mk_var("retained_b", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let checkpoint = terms.rollback_checkpoint();
    let (mut payload, old_index, old_stamp) = {
        let clause = equality(&mut terms, a, b, zero);
        (
            capture(&terms, clause),
            clause.index(),
            terms.entry_stamp(clause).unwrap(),
        )
    };
    separate_derived_ids(&mut payload);
    // No suffix TermId survives; only numeric metadata and untrusted RUP rows.
    terms.rollback_to(checkpoint);
    let clause = equality(&mut terms, a, b, one);
    assert_eq!(clause.index(), old_index);
    assert_ne!(terms.entry_stamp(clause).unwrap(), old_stamp);
    assert!(replay(&terms, clause, Some(&payload)).is_err());
}

#[test]
fn missing_wrong_corrupt_and_malformed_sources_never_fall_back() {
    let (terms, clause) = identity();
    let payload = capture(&terms, clause);
    let producer_calls = producer_test_counter::count();
    let attempts = super::super::super::ATTEMPTS.with(Cell::get);
    assert!(replay(&terms, clause, None).is_err());
    for mutation in 0..4 {
        let mut bad = payload.clone();
        match mutation {
            0 => bad.version += 1,
            1 => bad.rows.clear(),
            2 => bad.rows.last_mut().unwrap().hints = vec![u64::MAX],
            3 => bad.empty_clause_id = u64::MAX,
            _ => unreachable!(),
        }
        assert!(replay(&terms, clause, Some(&bad)).is_err());
    }
    let (other, arithmetic_clause) = arithmetic(1);
    let mut shifted = payload.clone();
    separate_derived_ids(&mut shifted);
    assert!(replay(&other, arithmetic_clause, Some(&shifted)).is_err());

    let mut malformed = TermStore::new();
    let x = malformed.mk_var("retained_identity", Sort::bitvec(9));
    let wrong = malformed.mk_bitvec(0.into(), 8);
    let sum = app(&mut malformed, "bvadd", &[x, wrong], Sort::bitvec(9));
    let bad = app(&mut malformed, "=", &[x, sum], Sort::Bool);
    assert!(matches!(
        replay(&malformed, bad, Some(&payload)),
        Err(BridgeError::Source(_))
    ));
    assert_eq!(super::super::super::ATTEMPTS.with(Cell::get), attempts);
    replay(&terms, clause, Some(&payload)).unwrap();
    assert_eq!(producer_test_counter::count(), producer_calls);
}
