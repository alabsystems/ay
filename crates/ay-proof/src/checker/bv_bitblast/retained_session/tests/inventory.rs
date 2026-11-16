// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn rows(ids: &[u32]) -> Vec<RetainedStepPayload> {
    ids.iter()
        .map(|&step| RetainedStepPayload {
            step,
            payload: vec![0],
        })
        .collect()
}

#[test]
fn complete_ordered_inventory_is_required_before_any_step_or_producer() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 2);
    let calls = producer_test_counter::count();
    let attempts = proof_producing_control::ATTEMPTS.with(Cell::get);
    for ids in [
        vec![],
        vec![0],
        vec![0, 1, 2],
        vec![0, 0],
        vec![1, 0],
        vec![0, 2],
        vec![0, u32::MAX],
    ] {
        let payloads = rows(&ids);
        let result = RetainedSession::new(
            credits(&proof, &terms, deadline()),
            RetainedOperation::Replay(&payloads),
            &mut |_, _| true,
        );
        assert!(
            matches!(result, Err(ProofCheckError::InvalidTheoryLemma { .. })),
            "{ids:?}"
        );
    }
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(proof_producing_control::ATTEMPTS.with(Cell::get), attempts);
    let payloads = rows(&[0, 1]);
    let session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Replay(&payloads),
        &mut |_, _| true,
    )
    .unwrap();
    // Inventory admission neither decodes the bogus bytes nor authenticates
    // the source: a session that did not check its steps cannot finish.
    assert!(session.finish(&mut |_, _| true).is_err());
}

#[test]
fn full_inventory_is_checked_even_when_the_first_source_step_is_cheap() {
    let (terms, clause) = identity(0);
    let mut proof = Proof::new();
    proof.add_assume(terms.true_term(), None);
    proof.add_theory_lemma_with_kind("bv", vec![clause], TheoryLemmaKind::BvBitBlast);
    let calls = producer_test_counter::count();
    for payloads in [rows(&[]), rows(&[0])] {
        assert!(RetainedSession::new(
            credits(&proof, &terms, deadline()),
            RetainedOperation::Replay(&payloads),
            &mut |_, _| true,
        )
        .is_err());
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn out_of_order_or_repeated_step_poisons_the_session_and_discards_output() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 2);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    let calls = producer_test_counter::count();
    assert!(session.validate_step(ProofId(1), &mut |_, _| true).is_err());
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert!(session.finish(&mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), calls);

    let proof = super::proof(clause, 1);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    session.validate_step(ProofId(0), &mut |_, _| true).unwrap();
    assert_eq!(session.output.len(), 1);
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert_eq!(session.output, []);
    assert!(session.finish(&mut |_, _| true).is_err());
}

#[test]
fn all_eight_inventory_slots_are_admitted_without_authenticating_the_payloads() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF);
    let payloads = rows(&(0..8).collect::<Vec<_>>());
    let session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Replay(&payloads),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(
        session.credits.ordinary_count(),
        MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF
    );
    assert!(session.finish(&mut |_, _| true).is_err());
    let ninth = super::proof(clause, MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF + 1);
    assert!(plan_expensive_bv_credits_with_progress(&ninth, &terms, &mut |_, _| true).is_err());
}
