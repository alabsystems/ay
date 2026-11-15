// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use std::time::Duration;

mod conditional;
mod versioned;
mod wire;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn bundle() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let x = terms.mk_var("snapshot-retained", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(9));
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let negated = terms.mk_not(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], identity, lemma, assumption);
    SerializableProofBundle::from_proof(&proof, &terms, vec![negated])
}

#[test]
fn independent_snapshot_readers_replay_without_producer_owners_or_search() {
    let before = producer_test_counter::count();
    let (source, checked, payloads) = {
        let bundle = bundle();
        let (checked, payloads) = capture(&bundle, end(), &mut |_, _| true).unwrap();
        // Test-only legacy serialization, NOT a new controlled v6 reader.
        (serde_json::to_vec(&bundle).unwrap(), checked, payloads)
    };
    assert_eq!(producer_test_counter::count(), before + 1);
    assert_eq!(payloads.len(), 1);
    for _ in 0..2 {
        let reconstructed: SerializableProofBundle = serde_json::from_slice(&source).unwrap();
        let replayed = replay(&reconstructed, &payloads, end(), &mut |_, _| true).unwrap();
        assert_eq!(replayed.quality, checked.quality);
        assert_eq!(replayed.assume_terms, checked.assume_terms);
        assert_eq!(producer_test_counter::count(), before + 1);
    }
}

#[test]
fn malformed_snapshot_and_unauthorized_assumptions_never_gain_payload_authority() {
    let bundle = bundle();
    let (_, payloads) = capture(&bundle, end(), &mut |_, _| true).unwrap();
    let before = producer_test_counter::count();
    let mut malformed = bundle.clone();
    malformed.true_term = Some(TermId(u32::MAX));
    assert!(replay(&malformed, &payloads, end(), &mut |_, _| true).is_err());
    let mut unauthorized = bundle.clone();
    unauthorized.obligation_assertions.clear();
    assert!(replay(&unauthorized, &payloads, end(), &mut |_, _| true).is_err());
    let mut nonterminal = bundle.clone();
    nonterminal.steps.pop();
    assert!(replay(&nonterminal, &payloads, end(), &mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn prior_legacy_snapshot_check_cannot_authorize_missing_or_corrupt_payloads() {
    let bundle = bundle();
    let (_, payloads) = capture(&bundle, end(), &mut |_, _| true).unwrap();
    // Legacy checking owns and drops a different reconstructed TermStore.
    // Its success cannot authorize omitted or corrupt retained evidence in a
    // subsequent snapshot. Same-store memo controls live in session tests.
    re_check_bundle_strict(&bundle).unwrap();
    let before = producer_test_counter::count();
    assert!(replay(&bundle, &[], end(), &mut |_, _| true).is_err());
    let mut corrupt = payloads.clone();
    corrupt[0].payload.clear();
    assert!(replay(&bundle, &corrupt, end(), &mut |_, _| true).is_err());
    let mut extra = payloads.clone();
    extra.push(payloads[0].clone());
    assert!(replay(&bundle, &extra, end(), &mut |_, _| true).is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn original_deadline_covers_snapshot_preflight_and_does_not_call_progress_when_expired() {
    let bundle = bundle();
    let before = producer_test_counter::count();
    let mut callbacks = 0;
    let mut progress = |_, _| {
        callbacks += 1;
        true
    };
    assert!(matches!(
        capture(&bundle, Instant::now(), &mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        replay(&bundle, &[], Instant::now(), &mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(callbacks, 0);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn consecutive_independent_reads_use_the_same_caller_budget_without_renewal() {
    let bundle = bundle();
    let (_, payloads) = capture(&bundle, end(), &mut |_, _| true).unwrap();
    let (mut work, mut bytes) = (0usize, 0usize);
    replay(&bundle, &payloads, end(), &mut |w, b| {
        work = work.checked_add(w).unwrap();
        bytes = bytes.checked_add(b).unwrap();
        true
    })
    .unwrap();
    assert!(work > 0 && bytes > 0);
    let before = producer_test_counter::count();
    let (mut used_work, mut used_bytes) = (0usize, 0usize);
    let mut progress = |w, b| {
        used_work = used_work.checked_add(w).unwrap();
        used_bytes = used_bytes.checked_add(b).unwrap();
        used_work <= work && used_bytes <= bytes
    };
    replay(&bundle, &payloads, end(), &mut progress).unwrap();
    assert!(matches!(
        replay(&bundle, &payloads, end(), &mut progress),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(producer_test_counter::count(), before);
}
