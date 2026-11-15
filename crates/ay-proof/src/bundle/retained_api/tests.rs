// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use crate::{Proof, TheoryLemmaKind};
use ay_core::{Sort, Symbol, TermStore};
use std::time::Duration;

mod control;
mod diagnostics;
mod transport;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn transport_limits() -> RetainedProofTransportLimits {
    RetainedProofTransportLimits {
        max_json_bytes: 64 * 1024 * 1024,
        max_storage_bytes: 64 * 1024 * 1024,
        max_work: 1_000_000_000,
    }
}

// The source Proof and TermStore die BEFORE capture; the public owner receives
// only the caller-admitted snapshot. No solver/producer state survives here.
fn bv_snapshot() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let x = terms.mk_var("public-retained", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(9));
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let negative = terms.mk_not(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negative, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], identity, lemma, assumption);
    SerializableProofBundle::from_proof(&proof, &terms, vec![negative])
}

fn repeated_bool_snapshot() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("public-retained-bool", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let pos = proof.add_assume(positive, None);
    let neg = proof.add_assume(negative, None);
    proof.add_assume(positive, None);
    proof.add_resolution(vec![], positive, pos, neg);
    // A caller-authorized superset is narrowed, preserving FIRST use order.
    SerializableProofBundle::from_proof(&proof, &terms, vec![negative, positive, negative])
}

fn finished() -> RetainedProofBundle {
    capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut |_, _| true)
        .unwrap()
        .finish_exact_with_resource_control(&mut |_, _| true)
        .unwrap()
        .0
}

#[test]
fn public_capture_survives_producer_destruction_and_finish_replay_produces_zero() {
    let before = producer_test_counter::count();
    let pending =
        capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut |_, _| {
            true
        })
        .unwrap();
    assert_eq!(producer_test_counter::count(), before + 1);
    assert!(pending.first_check().quality.is_complete());
    let assumptions = pending.first_check().assume_terms.clone();
    let (owner, second) = pending
        .finish_exact_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert_eq!(producer_test_counter::count(), before + 1);
    assert_eq!(second.assume_terms, assumptions);
    assert_eq!(owner.schema(), RETAINED_PROOF_BUNDLE_SCHEMA);
    assert_eq!(owner.obligation_assertions(), assumptions);
    for _ in 0..2 {
        let checked = owner
            .replay_exact_with_resource_control(end(), &mut |_, _| true)
            .unwrap();
        assert_eq!(checked.assume_terms, assumptions);
        assert!(checked.quality.is_complete());
        assert_eq!(producer_test_counter::count(), before + 1);
    }
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    drop(owner);
    let (decoded, third) = read_retained_proof_bundle_with_resource_control(
        &bytes,
        transport_limits(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(decoded.obligation_assertions(), assumptions);
    assert_eq!(third.assume_terms, assumptions);
    assert_eq!(producer_test_counter::count(), before + 1);
}

#[test]
fn consuming_finish_requires_independent_second_check_despite_authentic_first_report() {
    for corrupt in 0..3 {
        let mut pending = capture_strict_retained_bundle_with_resource_control(
            bv_snapshot(),
            end(),
            &mut |_, _| true,
        )
        .unwrap();
        assert!(pending.first_check().quality.is_complete());
        match corrupt {
            0 => pending.payloads.clear(),
            1 => pending.payloads[0].payload.clear(),
            _ => pending.snapshot.steps.pop().map(|_| ()).unwrap(),
        }
        let before = producer_test_counter::count();
        assert!(pending
            .finish_exact_with_resource_control(&mut |_, _| true)
            .is_err());
        assert_eq!(producer_test_counter::count(), before);
    }
}

#[test]
fn exact_narrowing_preserves_first_use_deduplicates_and_present_empty_bool_inventory() {
    let before = producer_test_counter::count();
    let pending = capture_strict_retained_bundle_with_resource_control(
        repeated_bool_snapshot(),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    let assumes = pending.first_check().assume_terms.clone();
    assert_eq!(assumes.len(), 3);
    assert_eq!(assumes[0], assumes[2]);
    let (owner, checked) = pending
        .finish_exact_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert_eq!(owner.obligation_assertions(), &assumes[..2]);
    assert_eq!(checked.assume_terms, assumes);
    let bytes = owner
        .encode_with_resource_control(transport_limits(), end(), &mut |_, _| true)
        .unwrap();
    let doc: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(doc["retained"], serde_json::json!([]));
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn detached_first_report_and_opaque_debug_cannot_change_or_expose_payload_owners() {
    let pending =
        capture_strict_retained_bundle_with_resource_control(bv_snapshot(), end(), &mut |_, _| {
            true
        })
        .unwrap();
    let authentic = pending.first_check().assume_terms.clone();
    let mut detached = pending.first_check().clone();
    detached.assume_terms.clear();
    assert_eq!(pending.first_check().assume_terms, authentic);
    assert_eq!(format!("{pending:?}"), "RetainedProofCapture { .. }");
    let (owner, checked) = pending
        .finish_exact_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert_eq!(checked.assume_terms, authentic);
    assert_eq!(format!("{owner:?}"), "RetainedProofBundle { .. }");
}
