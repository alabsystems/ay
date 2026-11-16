// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete private wire-reader controls, not external-query authentication.
//! Fixtures and adversarial serde mutations are test-owned inputs. Their
//! allocations are outside the controlled reader's newly owned reservations.

use super::*;
use crate::bundle::retained::{
    decode_bundle, encode_bundle, replay_bundle, BundleLimits, OwningOutcome, OwningUsage,
    ReadError, RetainedBundle, RetainedField, TransportError, RETAINED_SCHEMA,
};
use crate::bv_blast_solver::retained::{wire::WireLimits, RetainedBvRefutation};
use ay_core::{Constant, TermData};
use serde_json::{json, Value};

mod controls;
mod exact;

fn limits() -> BundleLimits {
    BundleLimits {
        max_json_bytes: 8 * 1024 * 1024,
        max_storage_bytes: 2 * 1024 * 1024 * 1024,
        max_work: 500_000_000,
        deadline: end(),
    }
}

fn wire() -> WireLimits {
    WireLimits {
        max_json_bytes: 8 * 1024 * 1024,
        max_rows: 10_000,
        max_literals: 1_000_000,
        max_hints: 1_000_000,
        max_work: 50_000_000,
        max_storage_bytes: 192 * 1024 * 1024,
        deadline: end(),
    }
}

fn encoded(snapshot: &SerializableProofBundle, rows: Vec<RetainedStepPayload>) -> Vec<u8> {
    encode_bundle(
        snapshot,
        &RetainedField::Present(rows),
        &limits(),
        &wire(),
        end(),
        &mut |_, _| true,
    )
    .result
    .unwrap()
}

fn decoded(bytes: &[u8]) -> OwningOutcome<RetainedBundle, TransportError> {
    decode_bundle(bytes, &limits(), &wire(), end(), &mut |_, _| true)
}

fn checked(bytes: &[u8]) -> OwningOutcome<BundleReCheck, ReadError> {
    replay_bundle(bytes, &limits(), &wire(), end(), &mut |_, _| true)
}

fn boolean_bundle() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("wire-boolean", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(Vec::new(), positive, left, right);
    SerializableProofBundle::from_proof(&proof, &terms, vec![positive, negative])
}

fn boolean_bytes() -> Vec<u8> {
    encoded(&boolean_bundle(), Vec::new())
}

fn arithmetic_bundle() -> SerializableProofBundle {
    // The existing multibit retained fixture, now through live lowering and
    // the whole owning reader: (a + b == 0) iff (a == -b). A sum of two
    // words, so the offset-equality lowering does not collapse its sides
    // into one `Eq`, as it does for (a - b == 0) against (a == b).
    let mut terms = TermStore::new();
    let a = terms.mk_var("wire-arithmetic-a", Sort::bitvec(8));
    let b = terms.mk_var("wire-arithmetic-b", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let sum = terms.mk_app(Symbol::named("bvadd"), [a, b], Sort::bitvec(8));
    let zero_test = terms.mk_app(Symbol::named("="), [sum, zero], Sort::Bool);
    let negated_b = terms.mk_app(Symbol::named("bvneg"), [b], Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("="), [a, negated_b], Sort::Bool);
    let identity = terms.mk_app(Symbol::named("="), [zero_test, equal], Sort::Bool);
    let negated = terms.mk_not(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), identity, lemma, assumption);
    SerializableProofBundle::from_proof(&proof, &terms, vec![negated])
}

fn measured_decode(bytes: &[u8]) -> OwningUsage {
    let (mut work, mut storage) = (0usize, 0usize);
    let outcome = decode_bundle(bytes, &limits(), &wire(), end(), &mut |w, b| {
        work = work.checked_add(w).unwrap();
        storage = storage.checked_add(b).unwrap();
        true
    });
    assert!(outcome.result.is_ok());
    assert_eq!(outcome.usage.charged_work, work);
    assert_eq!(outcome.usage.charged_bytes, storage);
    assert_eq!(outcome.usage.decoded_owner_reservation_bytes, Some(storage));
    outcome.usage
}

fn measured_replay(bytes: &[u8]) -> OwningUsage {
    let (mut work, mut storage) = (0usize, 0usize);
    let outcome = replay_bundle(bytes, &limits(), &wire(), end(), &mut |w, b| {
        work = work.checked_add(w).unwrap();
        storage = storage.checked_add(b).unwrap();
        true
    });
    assert!(outcome.result.is_ok());
    assert_eq!(outcome.usage.charged_work, work);
    assert_eq!(outcome.usage.charged_bytes, storage);
    outcome.usage
}

#[test]
fn complete_wire_reads_outlive_producer_and_input_without_search_or_normalization() {
    let before = producer_test_counter::count();
    let (bytes, expected) = {
        let snapshot = bundle();
        let (expected, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
        (encoded(&snapshot, rows), expected)
    };
    assert_eq!(producer_test_counter::count(), before + 1);
    assert!(serde_json::from_slice::<SerializableProofBundle>(&bytes).is_err());
    let owned = {
        let independent_input = bytes.clone();
        decoded(&independent_input).result.unwrap()
    }; // Decoder output cannot borrow this destroyed input or producer state.
    assert_eq!(owned.parts().0.schema, RETAINED_SCHEMA);
    assert_eq!(owned.parts().1.len(), 1);
    assert!(matches!(
        re_check_bundle_strict(owned.parts().0),
        Err(ProofCheckError::BundleSchemaMismatch { .. })
    ));
    let replayed = replay_versioned(&owned, end(), &mut |_, _| true).unwrap();
    assert_eq!(replayed.quality, expected.quality);
    drop(owned);
    for _ in 0..2 {
        let replayed = checked(&bytes).result.unwrap();
        assert_eq!(replayed.quality, expected.quality);
        assert_eq!(replayed.assume_terms, expected.assume_terms);
        assert_eq!(producer_test_counter::count(), before + 1);
    }
}

#[test]
fn present_empty_wire_inventory_checks_boolean_proof_without_a_producer() {
    let snapshot = boolean_bundle();
    let expected = re_check_bundle_strict(&snapshot).unwrap();
    let before = producer_test_counter::count();
    let bytes = encoded(&snapshot, Vec::new());
    drop(snapshot);
    let owned = decoded(&bytes).result.unwrap();
    assert_eq!(owned.parts().0.schema, RETAINED_SCHEMA);
    assert_eq!(owned.parts().1, []);
    let actual = checked(&bytes).result.unwrap();
    assert_eq!(actual.quality, expected.quality);
    assert_eq!(actual.assume_terms, expected.assume_terms);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn absent_null_or_legacy_schema_cannot_select_an_unretained_reader() {
    let intact: Value = serde_json::from_slice(&boolean_bytes()).unwrap();
    let before = producer_test_counter::count();
    let mut absent = intact.clone();
    absent.as_object_mut().unwrap().remove("retained");
    let mut null = intact.clone();
    null["retained"] = Value::Null;
    let mut legacy_with_inventory = intact.clone();
    legacy_with_inventory["schema"] = json!(PROOF_BUNDLE_SCHEMA);
    let mut future = intact.clone();
    future["schema"] = json!("ay.proofbundle/v5");
    let legacy_absent = serde_json::to_value(boolean_bundle()).unwrap();
    for invalid in [absent, null, legacy_with_inventory, future, legacy_absent] {
        let bytes = serde_json::to_vec(&invalid).unwrap();
        let outcome = checked(&bytes);
        assert!(matches!(outcome.result, Err(ReadError::Transport(_))));
        assert_eq!(outcome.usage.decoded_owner_reservation_bytes, None);
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn empty_corrupt_rebound_and_extra_wire_payloads_never_fall_back() {
    let snapshot = bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let bytes = encoded(&snapshot, rows);
    drop(snapshot);
    let intact: Value = serde_json::from_slice(&bytes).unwrap();
    let before = producer_test_counter::count();
    let mut empty = intact.clone();
    empty["retained"] = json!([]);
    let mut corrupt = intact.clone();
    corrupt["retained"][0]["payload"]["empty_clause_id"] = json!(u64::MAX);
    let mut rebound = intact.clone();
    assert_ne!(rebound["retained"][0]["step"], json!(0));
    rebound["retained"][0]["step"] = json!(0);
    let mut extra = intact.clone();
    let duplicate = extra["retained"][0].clone();
    extra["retained"].as_array_mut().unwrap().push(duplicate);
    let mut malformed_inner = intact.clone();
    malformed_inner["retained"][0]["payload"] = json!({});
    for invalid in [empty, corrupt, rebound, extra, malformed_inner] {
        let bytes = serde_json::to_vec(&invalid).unwrap();
        assert!(decoded(&bytes).result.is_ok()); // Transport is not authority.
        let refused = checked(&bytes);
        assert!(matches!(refused.result, Err(ReadError::Proof(_))));
        assert!(refused.usage.decoded_owner_reservation_bytes.is_some());
    }
    checked(&bytes).result.unwrap();
    assert_eq!(producer_test_counter::count(), before);
}

fn shifted(rows: &mut [RetainedStepPayload]) {
    // Keep the old refutation's derived IDs out of a neighbor's original CNF
    // namespace; rejection must not rely merely on a tiny original-ID alias.
    let mut proof: RetainedBvRefutation = serde_json::from_slice(&rows[0].payload).unwrap();
    let first = proof.rows[0].id;
    for row in &mut proof.rows {
        row.id = row.id.checked_add(1_000_000).unwrap();
        for hint in &mut row.hints {
            if *hint >= first {
                *hint = hint.checked_add(1_000_000).unwrap();
            }
        }
    }
    proof.empty_clause_id = proof.empty_clause_id.checked_add(1_000_000).unwrap();
    rows[0].payload = serde_json::to_vec(&proof).unwrap();
}

#[test]
fn retained_wire_cannot_prove_a_same_id_sat_neighbor() {
    let mut snapshot = bundle();
    let (_, mut rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    shifted(&mut rows);
    let original = encoded(&snapshot, rows.clone());
    let before = producer_test_counter::count();
    checked(&original).result.unwrap();
    let mut changed = 0;
    for (term, _) in &mut snapshot.term_entries {
        if let TermData::Const(Constant::BitVec { value, width }) = term {
            assert_eq!(*width, 9);
            assert_eq!(*value, num_bigint::BigInt::from(0));
            *value = 1.into();
            changed += 1;
        }
    }
    assert_eq!(changed, 1); // x + 1 = x is false, with unchanged term IDs.
    let neighbor = encoded(&snapshot, rows);
    assert!(decoded(&neighbor).result.is_ok());
    assert!(matches!(
        checked(&neighbor).result,
        Err(ReadError::Proof(_))
    ));
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn owning_wire_decode_does_not_replace_context_assumption_or_terminal_checks() {
    let snapshot = boolean_bundle();
    let mut bad_term = snapshot.clone();
    bad_term.true_term = Some(TermId(u32::MAX));
    let mut unauthorized = snapshot.clone();
    unauthorized.obligation_assertions.clear();
    let mut nonterminal = snapshot.clone();
    nonterminal.steps.pop();
    let mut context = snapshot;
    context
        .constructor_selectors
        .push(("unknown-constructor".to_owned(), vec!["field".to_owned()]));
    let before = producer_test_counter::count();
    for invalid in [bad_term, unauthorized, nonterminal, context] {
        let bytes = encoded(&invalid, Vec::new());
        let ownership = decoded(&bytes);
        assert!(ownership.result.is_ok());
        let replayed = checked(&bytes);
        assert!(matches!(replayed.result, Err(ReadError::Proof(_))));
        assert_eq!(
            replayed.usage.decoded_owner_reservation_bytes,
            ownership.usage.decoded_owner_reservation_bytes
        );
    }
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn wrong_typed_wire_and_wrong_proof_have_distinct_errors() {
    let mut wrong_type: Value = serde_json::from_slice(&boolean_bytes()).unwrap();
    wrong_type["steps"][0] = json!({"Assume": "not an unsigned term ID"});
    let bytes = serde_json::to_vec(&wrong_type).unwrap();
    let malformed = checked(&bytes);
    assert!(matches!(malformed.result, Err(ReadError::Transport(_))));
    assert_eq!(malformed.usage.decoded_owner_reservation_bytes, None);
    let mut unauthorized = boolean_bundle();
    unauthorized.obligation_assertions.clear();
    let semantic = checked(&encoded(&unauthorized, Vec::new()));
    assert!(matches!(semantic.result, Err(ReadError::Proof(_))));
    assert!(semantic.usage.decoded_owner_reservation_bytes.is_some());
}

#[test]
fn supplied_row_literal_and_hint_caps_reach_the_actual_retained_reader() {
    let snapshot = arithmetic_bundle();
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    assert_eq!(rows.len(), 1);
    // Test-only decoding measures this actual producer's wire shape. A zero
    // literal/hint assumption would not establish that those caps propagate.
    let payload: RetainedBvRefutation = serde_json::from_slice(&rows[0].payload).unwrap();
    let mut exact = wire();
    exact.max_rows = payload.rows.len();
    exact.max_literals = payload.rows.iter().fold(0usize, |sum, row| {
        sum.checked_add(row.literals.len()).unwrap()
    });
    exact.max_hints = payload
        .rows
        .iter()
        .fold(0usize, |sum, row| sum.checked_add(row.hints.len()).unwrap());
    assert!(exact.max_rows > 1 && exact.max_literals > 0 && exact.max_hints > 0);
    let bytes = encoded(&snapshot, rows);
    drop(snapshot);
    drop(payload);
    let before = producer_test_counter::count();
    let original_deadline = end();
    let accepted = replay_bundle(&bytes, &limits(), &exact, original_deadline, &mut |_, _| {
        true
    });
    assert!(accepted.result.is_ok());
    let mut row_short = exact;
    row_short.max_rows -= 1;
    let mut literal_short = exact;
    literal_short.max_literals -= 1;
    let mut hint_short = exact;
    hint_short.max_hints -= 1;
    for short in [row_short, literal_short, hint_short] {
        // Outer ownership preserves raw payloads; the mandatory inner reader
        // enforces these proof-shape caps without replacing the evidence.
        assert!(
            decode_bundle(&bytes, &limits(), &short, original_deadline, &mut |_, _| {
                true
            })
            .result
            .is_ok()
        );
        let refused = replay_bundle(&bytes, &limits(), &short, original_deadline, &mut |_, _| {
            true
        });
        assert!(matches!(refused.result, Err(ReadError::Proof(_))));
        assert_eq!(
            refused.usage.decoded_owner_reservation_bytes,
            accepted.usage.decoded_owner_reservation_bytes
        );
        assert_eq!(producer_test_counter::count(), before);
    }
}
