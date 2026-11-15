// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use crate::checker::bv_bitblast::classification::plan_expensive_bv_credits_with_progress;
use crate::checker::bv_bitblast::retained_session::{RetainedOperation, RetainedSession};
use ay_core::{Proof, Sort, Symbol};
use std::time::Duration;

fn fixture() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("priced", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [a, zero], Sort::bitvec(9));
    let root = terms.mk_app(Symbol::named("="), [a, sum], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![root], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn plan<'a>(terms: &'a TermStore, proof: &'a Proof) -> ExpensiveBvCreditPlan<'a> {
    plan_expensive_bv_credits_with_progress(proof, terms, &mut |_, _| true).unwrap()
}

fn capture(terms: &TermStore, proof: &Proof) -> Vec<RetainedStepPayload> {
    let credit = plan(terms, proof).prepay(end(), &mut |_, _| true).unwrap();
    let mut session =
        RetainedSession::new(credit, RetainedOperation::Capture, &mut |_, _| true).unwrap();
    session.validate_step(ProofId(0), &mut |_, _| true).unwrap();
    session.finish(&mut |_, _| true).unwrap()
}

#[test]
fn ordinary_refinement_is_downward_and_credit_keeps_its_exact_borrowed_source() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let source = terms.entries_snapshot();
    let old = plan(&terms, &proof).aggregate_charge();
    let before = producer_test_counter::count();
    let end = end();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end, None, &mut |_, _| true)
        .unwrap();
    assert!(refined.aggregate_charge().work < old.work);
    assert!(refined.aggregate_charge().bytes < old.bytes);
    let paid = refined.aggregate_charge();
    let mut charges = Vec::new();
    let mut credit = refined
        .prepay(end, &mut |work, bytes| {
            charges.push((work, bytes));
            true
        })
        .unwrap();
    assert_eq!(
        charges
            .iter()
            .filter(|&&(work, bytes)| (work, bytes) == (paid.work, paid.bytes))
            .count(),
        1
    );
    let borrowed = credit.take(ProofId(0), &mut |_, _| true).unwrap();
    assert!(std::ptr::eq(borrowed.terms(), &terms));
    assert!(std::ptr::eq(borrowed.step(), &proof.steps[0]));
    assert!(borrowed.replay_price().is_some());
    drop(borrowed);
    credit.finish().unwrap();
    assert_eq!(terms.entries_snapshot(), source);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn mixed_nonordinary_fee_and_shared_structural_cap_are_never_discounted() {
    let (terms, mut proof) = fixture();
    let payloads = capture(&terms, &proof);
    proof.add_theory_lemma_with_kind(
        "BV",
        vec![terms.true_term()],
        TheoryLemmaKind::BvLiaTautology,
    );
    let before = plan(&terms, &proof);
    let old_nonordinary = before
        .entries
        .iter()
        .flatten()
        .find(|entry| entry.ordinary_clause().is_none())
        .unwrap()
        .charge;
    let refined = before
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let kept = refined
        .entries
        .iter()
        .flatten()
        .find(|entry| entry.ordinary_clause().is_none())
        .unwrap();
    assert_eq!(kept.charge.work, old_nonordinary.work);
    assert_eq!(kept.charge.bytes, old_nonordinary.bytes);
    assert!(kept.replay_price.is_none());
    for _ in 0..8 {
        proof.add_theory_lemma_with_kind(
            "BV",
            vec![terms.true_term()],
            TheoryLemmaKind::BvLiaTautology,
        );
    }
    assert!(plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).is_err());
}

#[test]
fn incomplete_duplicate_reordered_and_capacity_overflow_inventory_never_get_a_price() {
    let (terms, mut proof) = fixture();
    let mut payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    assert!(plan(&terms, &proof)
        .refine_replay(&[], end(), None, &mut |_, _| true)
        .is_err());
    let mut duplicate = payloads.clone();
    duplicate.push(payloads[0].clone());
    assert!(plan(&terms, &proof)
        .refine_replay(&duplicate, end(), None, &mut |_, _| true)
        .is_err());
    payloads[0].step = 1;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .is_err());
    payloads[0].step = 0;
    let mut wire = transport_wire_limits(end());
    wire.max_storage_bytes = payloads[0].payload.capacity() - 1;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, wire.deadline, Some(wire), &mut |_, _| true)
        .is_err());
    proof.steps.push(proof.steps[0].clone());
    duplicate[1].step = 1;
    duplicate.swap(0, 1);
    assert!(plan(&terms, &proof)
        .refine_replay(&duplicate, end(), None, &mut |_, _| true)
        .is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn every_planning_stop_and_zero_byte_or_work_owner_refuses_before_prepaid_credit() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let deadline = end();
    let mut total = 0;
    plan(&terms, &proof)
        .refine_replay(&payloads, deadline, None, &mut |_, _| {
            total += 1;
            true
        })
        .unwrap();
    let before = producer_test_counter::count();
    for stop_at in 1..=total {
        let mut calls = 0;
        assert!(plan(&terms, &proof)
            .refine_replay(&payloads, deadline, None, &mut |_, _| {
                calls += 1;
                calls != stop_at
            })
            .is_err());
        assert_eq!(calls, stop_at);
    }
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, deadline, None, &mut |work, _| work == 0)
        .is_err());
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, deadline, None, &mut |_, bytes| bytes == 0)
        .is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn original_absolute_deadline_refuses_before_any_planner_callback() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let mut callbacks = 0;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, Instant::now(), None, &mut |_, _| {
            callbacks += 1;
            true
        })
        .is_err());
    assert_eq!(callbacks, 0);
}

// This shape's retained lane requires an independently checked offset theorem.
// Empty wire here remains untrusted: price inspection cannot authenticate it.
fn conditional_fixture() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let stack = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let start = terms.mk_app(Symbol::named("bvsub"), [stack, size], word.clone());
    let guard = terms.mk_app(Symbol::named("bvuge"), [stack, size], Sort::Bool);
    let below = terms.mk_app(Symbol::named("bvult"), [observe, start], Sort::Bool);
    let above = terms.mk_app(Symbol::named("bvuge"), [observe, stack], Sort::Bool);
    let outside = terms.mk_app(Symbol::named("or"), [below, above], Sort::Bool);
    let inside = terms.mk_not_raw(outside);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", byte.clone());
    let after = terms.mk_app(Symbol::named("store"), [base, start, value], array);
    let after = terms.mk_app(Symbol::named("select"), [after, observe], byte.clone());
    let before = terms.mk_app(Symbol::named("select"), [base, observe], byte);
    let equal = terms.mk_app(Symbol::named("="), [after, before], Sort::Bool);
    let property = terms.mk_app(Symbol::named("or"), [inside, equal], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = terms.mk_app(Symbol::named("and"), [guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    assert!(
        crate::checker::bv_bitblast::proof_producing_control::OutsideFrameShape::recognize(
            &terms,
            &[clause]
        )
        .is_some()
    );
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![clause], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

#[test]
fn conditional_prerequisite_route_keeps_exact_legacy_fee_without_assuming_success() {
    let (terms, proof) = conditional_fixture();
    let before = plan(&terms, &proof).aggregate_charge();
    let payloads = [RetainedStepPayload {
        step: 0,
        payload: vec![],
    }];
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(refined.aggregate_charge().work, before.work);
    assert_eq!(refined.aggregate_charge().bytes, before.bytes);
    assert!(refined
        .entries
        .iter()
        .flatten()
        .all(|entry| entry.replay_price.is_none()));
    let calls = producer_test_counter::count();
    let prepaid = refined.prepay(end(), &mut |_, _| true).unwrap();
    let mut session = RetainedSession::new(
        prepaid,
        RetainedOperation::Replay(&payloads),
        &mut |_, _| true,
    )
    .unwrap();
    assert!(session.validate_step(ProofId(0), &mut |_, _| true).is_err());
    assert!(session.finish(&mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn final_refined_aggregate_refusal_is_not_retried_refunded_or_replaced_by_search() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let paid = refined.aggregate_charge();
    let mut refused = 0;
    assert!(refined
        .prepay(end(), &mut |work, bytes| {
            if (work, bytes) == (paid.work, paid.bytes) {
                refused += 1;
                false
            } else {
                true
            }
        })
        .is_err());
    assert_eq!(refused, 1);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn earlier_requested_wire_deadline_refuses_before_any_direct_planner_callback() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let original = end();
    let mut wire = transport_wire_limits(original);
    wire.deadline = Instant::now();
    let mut callbacks = 0;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, original, Some(wire), &mut |_, _| {
            callbacks += 1;
            true
        })
        .is_err());
    assert_eq!(callbacks, 0);
}

#[test]
fn malformed_gate_annotation_keeps_exact_invalid_theory_error_before_pricing() {
    let (terms, mut proof) = fixture();
    let payloads = capture(&terms, &proof);
    let ProofStep::TheoryLemma { kind, .. } = &mut proof.steps[0] else {
        panic!("fixture must be an ordinary theory lemma");
    };
    *kind = TheoryLemmaKind::BvBitBlastGate {
        gate_type: ay_core::BvGateType::And,
        width: 9,
    };
    let before = producer_test_counter::count();
    let result = plan(&terms, &proof).refine_replay(&payloads, end(), None, &mut |_, _| true);
    assert!(matches!(
        result,
        Err(ProofCheckError::InvalidTheoryLemma {
            step: ProofId(0),
            ..
        })
    ));
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn incomplete_array_free_source_scan_keeps_old_fee_and_never_trusts_wire() {
    let (mut terms, mut proof) = fixture();
    let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[0] else {
        panic!("fixture must be an ordinary theory lemma");
    };
    let mut root = clause[0];
    for _ in 0..crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_TERM_NODES {
        root = terms.mk_not_raw(root);
    }
    clause[0] = root;
    let old = plan(&terms, &proof).aggregate_charge();
    let payloads = [RetainedStepPayload {
        step: 0,
        payload: b"not a proof".to_vec(),
    }];
    let before = producer_test_counter::count();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(refined.aggregate_charge().work, old.work);
    assert_eq!(refined.aggregate_charge().bytes, old.bytes);
    assert!(refined
        .entries
        .iter()
        .flatten()
        .all(|entry| entry.replay_price.is_none()));
    assert_eq!(producer_test_counter::count(), before);
}

fn legacy_replay_error(
    terms: &TermStore,
    proof: &Proof,
    payloads: &[RetainedStepPayload],
) -> ProofCheckError {
    let prepaid = plan(terms, proof).prepay(end(), &mut |_, _| true).unwrap();
    let mut session =
        RetainedSession::new(prepaid, RetainedOperation::Replay(payloads), &mut |_, _| {
            true
        })
        .unwrap();
    session
        .validate_step(ProofId(0), &mut |_, _| true)
        .unwrap_err()
}

fn invalid_step_and_reason(error: ProofCheckError) -> (ProofId, String) {
    match error {
        ProofCheckError::InvalidTheoryLemma { step, reason } => (step, reason),
        other => panic!("expected exact legacy invalid-theory error, got {other:?}"),
    }
}

#[test]
fn malformed_wire_keeps_exact_legacy_strict_replay_error_without_search() {
    let (terms, proof) = fixture();
    let mut payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    for bytes in [b"null".as_slice(), b"{}", b"[]", b"not JSON"] {
        payloads[0].payload = bytes.to_vec();
        let old = legacy_replay_error(&terms, &proof, &payloads);
        let new = plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| true)
            .err()
            .unwrap();
        assert_eq!(invalid_step_and_reason(new), invalid_step_and_reason(old));
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn unsupported_array_free_source_keeps_exact_legacy_strict_replay_error() {
    let (mut terms, mut proof) = fixture();
    let payloads = capture(&terms, &proof);
    let a = terms.mk_var("unsupported", Sort::bitvec(9));
    let invalid = terms.mk_app(
        Symbol::indexed("extract", vec![99, 0]),
        [a],
        Sort::bitvec(9),
    );
    let equal = terms.mk_app(Symbol::named("="), [a, invalid], Sort::Bool);
    let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[0] else {
        panic!("fixture must be an ordinary theory lemma");
    };
    clause[0] = equal;
    let before = producer_test_counter::count();
    let old = legacy_replay_error(&terms, &proof, &payloads);
    let new = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .err()
        .unwrap();
    assert_eq!(invalid_step_and_reason(new), invalid_step_and_reason(old));
    assert_eq!(producer_test_counter::count(), before);
}

mod sparse_cost;
