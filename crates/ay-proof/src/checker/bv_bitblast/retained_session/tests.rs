// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::classification::plan_expensive_bv_credits_with_progress;
use super::super::producer_limits::counted_limits_until;
use super::super::{bv_bitblast_requires_proof_producer, proof_producing_control};
use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use ay_core::{BvGateType, Proof, Sort, Symbol, TermStore};
use std::{cell::Cell, time::Duration};

mod controls;
mod hang_guard;
mod inventory;
mod replay;
mod specialized;
mod wire_limits;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn identity(constant: u32) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("session_identity", Sort::bitvec(9));
    let value = terms.mk_bitvec(constant.into(), 9);
    let sum = app(&mut terms, "bvadd", &[a, value], Sort::bitvec(9));
    let root = app(&mut terms, "=", &[a, sum], Sort::Bool);
    (terms, root)
}

fn proof(clause: TermId, count: usize) -> Proof {
    let mut proof = Proof::new();
    for _ in 0..count {
        proof.add_theory_lemma_with_kind("bv", vec![clause], TheoryLemmaKind::BvBitBlast);
    }
    proof
}

fn credits<'a>(proof: &'a Proof, terms: &'a TermStore, end: Instant) -> PrepaidBvCredits<'a> {
    plan_expensive_bv_credits_with_progress(proof, terms, &mut |_, _| true)
        .unwrap()
        .prepay(end, &mut |_, _| true)
        .unwrap()
}

fn capture(terms: &TermStore, proof: &Proof) -> Vec<RetainedStepPayload> {
    let mut session = RetainedSession::new(
        credits(proof, terms, deadline()),
        RetainedOperation::Capture,
        &mut |_, _| true,
    )
    .unwrap();
    for index in 0..proof.steps.len() {
        session
            .validate_step(ProofId(index as u32), &mut |_, _| true)
            .unwrap();
    }
    session.finish(&mut |_, _| true).unwrap()
}

fn replay(
    terms: &TermStore,
    proof: &Proof,
    payloads: &[RetainedStepPayload],
) -> Result<(), ProofCheckError> {
    let mut session = RetainedSession::new(
        credits(proof, terms, deadline()),
        RetainedOperation::Replay(payloads),
        &mut |_, _| true,
    )?;
    for index in 0..proof.steps.len() {
        session.validate_step(ProofId(index as u32), &mut |_, _| true)?;
    }
    assert!(session.finish(&mut |_, _| true)?.is_empty());
    Ok(())
}

#[test]
fn two_ordinary_steps_share_one_whole_proof_precharge_and_keep_source_unchanged() {
    let (terms, clause) = identity(0);
    assert!(bv_bitblast_requires_proof_producer(&terms, &[clause]));
    let source = terms.entries_snapshot();
    let proof = proof(clause, 2);
    let plan = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    let aggregate = plan.aggregate_charge();
    assert_eq!(
        aggregate.work,
        2 * super::super::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize
    );
    assert_eq!(
        aggregate.bytes,
        2 * super::super::MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
    );
    let prepaid_calls = Cell::new(0);
    let mut progress = |work, bytes| {
        if (work, bytes) == (aggregate.work, aggregate.bytes) {
            prepaid_calls.set(prepaid_calls.get() + 1);
        } else {
            // The bridge spends its allowance internally, not by repaying a
            // per-lemma reservation or a second full transport reservation.
            assert!(work <= MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF);
            assert!(bytes <= 1024);
        }
        true
    };
    let prepaid = plan.prepay(deadline(), &mut progress).unwrap();
    let mut session =
        RetainedSession::new(prepaid, RetainedOperation::Capture, &mut progress).unwrap();
    assert_eq!(
        session.validate_step(ProofId(0), &mut progress).unwrap(),
        Some(&[clause][..])
    );
    assert_eq!(
        session.validate_step(ProofId(1), &mut progress).unwrap(),
        Some(&[clause][..])
    );
    let payloads = session.finish(&mut progress).unwrap();
    assert_eq!(
        payloads.iter().map(|row| row.step).collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert_eq!(prepaid_calls.get(), 1);
    assert_eq!(terms.entries_snapshot(), source);
    assert!(!terms.strict_bv_semantics_validated(&[clause]));
    replay(&terms, &proof, &payloads).unwrap();
}

#[test]
fn one_lemma_budget_cannot_admit_two_lemmas_before_any_producer_entry() {
    let (terms, clause) = identity(0);
    let proof = proof(clause, 2);
    let plan = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    let calls = producer_test_counter::count();
    let limit = super::super::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize;
    assert!(plan
        .prepay(deadline(), &mut |work, _| work <= limit)
        .is_err());
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn cheap_and_non_bv_steps_are_not_retained_acceptances() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("cheap", Sort::bitvec(1));
    let clause = app(&mut terms, "=", &[a, a], Sort::Bool);
    assert!(!bv_bitblast_requires_proof_producer(&terms, &[clause]));
    let mut proof = proof(clause, 1);
    proof.add_assume(terms.true_term(), None);
    let mut session = RetainedSession::new(
        credits(&proof, &terms, deadline()),
        RetainedOperation::Replay(&[]),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(
        session.validate_step(ProofId(0), &mut |_, _| true),
        Ok(None)
    );
    assert_eq!(
        session.validate_step(ProofId(1), &mut |_, _| true),
        Ok(None)
    );
    assert!(session.finish(&mut |_, _| true).unwrap().is_empty());
    // The enclosing strict checker, not this empty session, must check these
    // source steps and reject the absent terminal contradiction.
}
