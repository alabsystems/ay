// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::checker::validate_expensive_bv_budget_with_progress;
use crate::{
    re_check_bundle_strict, re_check_bundle_strict_with_cancellation, SerializableProofBundle,
};

fn wide_tagged_proof(count: usize) -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let value = terms.mk_var("classification-wide", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..count {
        proof.add_theory_lemma_with_kind("BV", vec![equality], TheoryLemmaKind::BvBitBlast);
    }
    (terms, proof)
}

fn sample_payload() -> PayloadStats {
    PayloadStats {
        work: 17,
        bytes: 31,
        unfolded_work: 13,
        fp_assignments: 0,
        order_assignments: 0,
    }
}

#[test]
fn tag_census_preserves_exact_two_pass_charge_and_only_polls_zero() {
    let (terms, mut proof) = wide_tagged_proof(1);
    proof.add_theory_lemma_with_kind(
        "BV",
        vec![],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: ay_core::BvGateType::Eq,
            width: 16,
        },
    );
    // Other expensive kinds are counted by the aggregate census, not this
    // reservation for BV-presence and bounded-variable classifier traversals.
    proof.add_theory_lemma_with_kind("BV/LIA", vec![], TheoryLemmaKind::BvLiaTautology);
    proof.add_assume(terms.true_term(), None);
    let mut polls = 0;
    let charge =
        proof_producing_bv_classifier_charge(&proof, sample_payload(), &mut |work, bytes| {
            assert_eq!((work, bytes), (0, 0));
            polls += 1;
            true
        })
        .unwrap();
    assert_eq!(charge, (4 * 17, 4 * 31));
    assert_eq!(polls, proof.steps.len() + 2);
}

#[test]
fn tag_census_refuses_every_checkpoint_even_empty_untagged_and_final() {
    let (terms, tagged) = wide_tagged_proof(9);
    let untagged = Proof::from_steps(vec![ProofStep::Assume(terms.true_term()); 8]);
    for proof in [&Proof::new(), &untagged, &tagged] {
        for stop in 1..=proof.steps.len() + 2 {
            let mut calls = 0;
            let result =
                proof_producing_bv_classifier_charge(proof, sample_payload(), &mut |_, _| {
                    calls += 1;
                    calls != stop
                });
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
            assert_eq!(calls, stop);
        }
        assert!(
            proof_producing_bv_classifier_charge(proof, sample_payload(), &mut |_, _| true).is_ok()
        );
    }
}

fn actual_classifier_reservation(terms: &TermStore, proof: &Proof) -> (usize, usize) {
    let payload =
        meter_authentication_payload(proof, terms, None, None, None, Some(&[]), &mut |_, _| true)
            .unwrap()
            .aggregate;
    proof_producing_bv_classifier_charge(proof, payload, &mut |_, _| true).unwrap()
}

#[test]
fn strict_checker_carries_actual_inner_classification_polls_before_cap_rejection() {
    // The ninth wide lemma must be rejected by the aggregate census, before
    // ANY producer or semantic checker runs. This test launches no solver.
    let (terms, proof) = wide_tagged_proof(9);
    let reserve = actual_classifier_reservation(&terms, &proof);
    let mut inner = Vec::new();
    let expected =
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |work, bytes| {
            inner.push((work, bytes));
            true
        })
        .unwrap_err();
    assert!(
        matches!(&expected, ProofCheckError::InvalidTheoryLemma { step: ProofId(8), reason }
        if reason.contains("whole-proof cap"))
    );
    assert!(inner.len() > 3);
    assert!(inner.iter().all(|charge| *charge == (0, 0)));

    let mut trace = Vec::new();
    let actual = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            trace.push((work, bytes));
            true
        },
    )
    .unwrap_err();
    assert_eq!(actual, expected);
    let positions: Vec<_> = trace
        .iter()
        .enumerate()
        .filter_map(|(index, charge)| (*charge == reserve).then_some(index))
        .collect();
    assert_eq!(
        positions.len(),
        1,
        "fixture reservation must uniquely locate classification"
    );
    let census = positions[0] + 1;
    assert_eq!(trace[census], (proof.steps.len(), 0));
    // Exact suffix locks the real wiring: the old uncontrolled collector
    // would return the cap error here without any of these inner callbacks.
    assert_eq!(&trace[census + 1..], inner);
    let stop = census + 1 + 3;
    let mut calls = 0;
    let refused = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |_, _| {
            calls += 1;
            calls != stop
        },
    )
    .unwrap_err();
    assert_eq!(refused, ProofCheckError::ResourceLimit);
    assert_eq!(calls, stop);
}

fn closed_refutation() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let five = terms.mk_bitvec(5.into(), 64);
    let ten = terms.mk_bitvec(10.into(), 64);
    let equality = terms.mk_app(Symbol::named("="), [five, ten], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let assume = proof.add_assume(equality, None);
    let theorem =
        proof.add_theory_lemma_with_kind("BV", vec![disequality], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], equality, assume, theorem);
    SerializableProofBundle::from_proof(&proof, &terms, vec![equality])
}

#[test]
fn offline_closed_bv_refutation_has_exact_live_parity_and_terminal_cancellation() {
    // Ground 64-bit constants need zero assignment bits, so live proof
    // validation uses the bounded evaluator, not a producer solver.
    let bundle = closed_refutation();
    let source = serde_json::to_vec(&bundle).unwrap();
    let expected = re_check_bundle_strict(&bundle).unwrap();
    assert!(expected.quality.is_complete());
    assert_eq!(expected.assume_terms, bundle.obligation_assertions);
    let mut total = 0;
    let actual = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
        total += 1;
        true
    })
    .unwrap();
    assert_eq!(actual.quality, expected.quality);
    assert_eq!(actual.assume_terms, expected.assume_terms);
    for stop in 1..=total {
        let mut calls = 0;
        let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            calls += 1;
            calls != stop
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), source);
    let retried = re_check_bundle_strict_with_cancellation(&bundle, &mut || true).unwrap();
    assert_eq!(retried.quality, expected.quality);
}

#[test]
fn cheap_classification_does_not_authorize_a_forged_no_bv_lemma() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("classification-no-bv", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![p, not_p], TheoryLemmaKind::BvBitBlast);
    let charge =
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    assert_eq!((charge.work, charge.bytes), (0, 0));
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |_, _| true,
    )
    .unwrap_err();
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { reason, .. }
        if reason.contains("does not mention any bitvector"))
    );
}

fn closed_bool_lia_refutation() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let truth = terms.true_term();
    let source = terms.mk_not_raw(truth);
    let literal = terms.mk_not_raw(source);
    let mut proof = Proof::new();
    let assume = proof.add_assume(source, None);
    let theorem =
        proof.add_theory_lemma_with_kind("BV_LIA", vec![literal], TheoryLemmaKind::BvLiaTautology);
    proof.add_resolution(vec![], source, theorem, assume);
    (terms, proof)
}

#[test]
fn closed_bool_lia_planner_is_prepaid_before_source_census_and_native_fee() {
    let (terms, proof) = closed_bool_lia_refutation();
    let reserve = crate::checker::bv_bitblast::CLOSED_BV_LIA_CLASSIFIER_WORK;
    assert_eq!(
        proof_producing_bv_classifier_charge(&proof, sample_payload(), &mut |_, _| true,).unwrap(),
        (reserve, 0)
    );
    let source = terms.entries_snapshot();
    let ProofStep::Assume(root) = &proof.steps[0] else {
        panic!("fixture");
    };
    let mut planner_paid = 0;
    let mut native_paid = 0;
    let actual = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[*root],
        &mut |work, bytes| {
            if (work, bytes) == (reserve, 0) {
                planner_paid += 1;
            }
            if (work, bytes) == (32 * 1024, 1024 * 1024) {
                assert_eq!(planner_paid, 1);
                native_paid += 1;
            }
            true
        },
    )
    .unwrap();
    assert_eq!(actual.step_count(), 3);
    assert_eq!(actual.clause(ProofId(2)), Some([].as_slice()));
    assert_eq!(planner_paid, 1);
    assert_eq!(native_paid, 1);
    assert_eq!(terms.entries_snapshot(), source);
}

#[test]
fn closed_bool_lia_native_fee_refusal_is_terminal_before_rule_validation() {
    let (terms, proof) = closed_bool_lia_refutation();
    let source = terms.entries_snapshot();
    let ProofStep::Assume(root) = &proof.steps[0] else {
        panic!("fixture");
    };
    let mut refused = false;
    let mut after_refusal = 0;
    let result = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[*root],
        &mut |work, bytes| {
            if refused {
                after_refusal += 1;
            }
            if (work, bytes) == (32 * 1024, 1024 * 1024) {
                refused = true;
                return false;
            }
            true
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert!(refused);
    assert_eq!(after_refusal, 0);
    assert_eq!(terms.entries_snapshot(), source);
}
