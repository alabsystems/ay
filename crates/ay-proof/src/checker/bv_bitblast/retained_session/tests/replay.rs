// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::RetainedBvRefutation;

fn shifted_payload(terms: &TermStore, proof: &Proof) -> Vec<RetainedStepPayload> {
    let mut payloads = capture(terms, proof);
    // Test-only mutation keeps derived IDs disjoint from every small neighbor's
    // original CNF namespace, so source rejection cannot merely be an ID clash.
    let mut payload: RetainedBvRefutation = serde_json::from_slice(&payloads[0].payload).unwrap();
    let first = payload.rows[0].id;
    for row in &mut payload.rows {
        row.id = row.id.checked_add(1_000_000).unwrap();
        for hint in &mut row.hints {
            if *hint >= first {
                *hint = hint.checked_add(1_000_000).unwrap();
            }
        }
    }
    payload.empty_clause_id = payload.empty_clause_id.checked_add(1_000_000).unwrap();
    payloads[0].payload = serde_json::to_vec(&payload).unwrap();
    payloads
}

#[test]
fn fresh_store_replays_after_producer_destruction_without_producer_or_memo() {
    let calls = producer_test_counter::count();
    let payloads = {
        let (terms, clause) = identity(0);
        shifted_payload(&terms, &proof(clause, 1))
    };
    assert_eq!(producer_test_counter::count(), calls + 1);
    let calls = producer_test_counter::count();
    let attempts = proof_producing_control::ATTEMPTS.with(Cell::get);
    let (terms, clause) = identity(0);
    let source = terms.entries_snapshot();
    replay(&terms, &proof(clause, 1), &payloads).unwrap();
    assert_eq!(terms.entries_snapshot(), source);
    assert!(!terms.strict_bv_semantics_validated(&[clause]));
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(proof_producing_control::ATTEMPTS.with(Cell::get), attempts);

    let (neighbor, false_clause) = identity(1);
    assert_eq!(clause.index(), false_clause.index());
    assert!(replay(&neighbor, &proof(false_clause, 1), &payloads).is_err());
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(proof_producing_control::ATTEMPTS.with(Cell::get), attempts);
}

#[test]
fn forged_gate_annotation_is_rechecked_even_with_a_primed_semantic_memo() {
    let (terms, clause) = identity(0);
    let payloads = capture(&terms, &proof(clause, 1));
    terms.record_strict_bv_semantics_validated(&[clause]);
    assert!(terms.strict_bv_semantics_validated(&[clause]));
    let calls = producer_test_counter::count();
    for (gate_type, width) in [(BvGateType::And, 9), (BvGateType::Add, 10)] {
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind(
            "bv",
            vec![clause],
            TheoryLemmaKind::BvBitBlastGate { gate_type, width },
        );
        assert!(matches!(
            replay(&terms, &proof, &payloads),
            Err(ProofCheckError::InvalidTheoryLemma { reason, .. })
                if reason.contains("annotated gate")
        ));
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn corrupt_wire_does_not_use_a_valid_source_memo_or_fall_back() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 1);
    let payloads = capture(&terms, &proof);
    terms.record_strict_bv_semantics_validated(&[clause]);
    let calls = producer_test_counter::count();
    let attempts = proof_producing_control::ATTEMPTS.with(Cell::get);
    for bytes in [Vec::new(), b"null".to_vec(), b"{}".to_vec(), b"[".to_vec()] {
        let invalid = [RetainedStepPayload {
            step: 0,
            payload: bytes,
        }];
        assert!(replay(&terms, &proof, &invalid).is_err());
    }
    let mut corrupt = payloads.clone();
    let mut payload: RetainedBvRefutation = serde_json::from_slice(&corrupt[0].payload).unwrap();
    payload.empty_clause_id = u64::MAX;
    corrupt[0].payload = serde_json::to_vec(&payload).unwrap();
    assert!(replay(&terms, &proof, &corrupt).is_err());
    replay(&terms, &proof, &payloads).unwrap();
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(proof_producing_control::ATTEMPTS.with(Cell::get), attempts);
}

#[test]
fn non_boolean_live_source_and_sat_capture_refuse_without_retained_output() {
    let (terms, clause) = identity(1);
    let proof = proof(clause, 1);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert_eq!(session.output, []);
    assert!(session.finish(&mut |_, _| true).is_err());

    let mut terms = TermStore::new();
    let non_bool = terms.mk_var("non_bool", Sort::bitvec(9));
    let proof = super::proof(non_bool, 1);
    let calls = producer_test_counter::count();
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    assert!(
        matches!(session.validate_step(ProofId(0), &mut |_, _| true),
        Err(ProofCheckError::InvalidTheoryLemma { reason, .. }) if reason.contains("non-Bool"))
    );
    assert!(session.finish(&mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), calls);
}
