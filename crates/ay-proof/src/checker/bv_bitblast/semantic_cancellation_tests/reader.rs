// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{
    authenticate_premise_clauses_strict_with_context_and_progress, re_check_bundle_strict,
    re_check_bundle_strict_with_cancellation, SerializableProofBundle,
};

#[test]
fn strict_step_validation_contains_the_actual_boolean_semantic_poll_trace() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("falsifiable-semantic-leaf", Sort::Bool);
    let clause = [p];
    let mut inner = Vec::new();
    let expected =
        validate_bool_tautology_with_progress(&terms, ProofId(0), &clause, &mut |w, b| {
            inner.push((w, b));
            true
        })
        .unwrap_err();
    assert!(matches!(
        expected,
        ProofCheckError::InvalidTheoryLemma { .. }
    ));
    assert!(inner.len() > 5);
    assert!(inner.iter().all(|charge| *charge == (0, 0)));
    let mut tagged = Proof::new();
    tagged.add_theory_lemma_with_kind("Bool", clause.to_vec(), TheoryLemmaKind::BoolTautology);
    let mut true_rule = Proof::new();
    true_rule.add_rule_step(ay_core::AletheRule::True, clause.to_vec(), vec![], vec![]);
    let mut false_rule = Proof::new();
    false_rule.add_rule_step(ay_core::AletheRule::False, clause.to_vec(), vec![], vec![]);
    for proof in [tagged, true_rule, false_rule] {
        assert_semantic_trace(&proof, &terms, &inner, &expected);
    }
}

fn assert_semantic_trace(
    proof: &Proof,
    terms: &TermStore,
    inner: &[(usize, usize)],
    expected: &ProofCheckError,
) {
    let mut outer = Vec::new();
    let actual = authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        &[],
        &mut |w, b| {
            outer.push((w, b));
            true
        },
    )
    .unwrap_err();
    assert_eq!(&actual, expected);
    let step_start = outer.iter().rposition(|charge| *charge != (0, 0)).unwrap() + 1;
    // No progress-capable dispatch layer may replace or skip the inner walk.
    assert_eq!(&outer[step_start..], inner);
    for position in 1..=inner.len() {
        let stop = step_start + position;
        let mut calls = 0_usize;
        let result = authenticate_premise_clauses_strict_with_context_and_progress(
            proof,
            terms,
            None,
            None,
            &[],
            &mut |_, _| {
                calls = calls.saturating_add(1);
                calls != stop
            },
        );
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
}

fn refutation(lane: Lane) -> SerializableProofBundle {
    let (mut terms, clause) = valid(lane);
    let theorem = clause[0];
    let assumption = terms.mk_not_raw(theorem);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(assumption, None);
    let lemma = proof.add_theory_lemma_with_kind("semantic-cancellation", clause, lane.kind());
    proof.add_resolution(vec![], theorem, lemma, assumed);
    SerializableProofBundle::from_proof(&proof, &terms, vec![assumption])
}

#[test]
fn offline_bv_gate_and_boolean_refutations_refuse_every_poll_and_retry_unchanged() {
    for lane in [Lane::Boolean, Lane::BitBlast, Lane::Gate] {
        let bundle = refutation(lane);
        let source = serde_json::to_vec(&bundle).unwrap();
        let expected = re_check_bundle_strict(&bundle).unwrap();
        assert!(expected.quality.is_complete());
        assert_eq!(expected.assume_terms, bundle.obligation_assertions);
        let mut total = 0;
        let checked = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            total += 1;
            true
        })
        .unwrap();
        assert_eq!(checked.quality, expected.quality);
        assert_eq!(checked.assume_terms, expected.assume_terms);
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
}
