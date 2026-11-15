// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete private v6 outside-frame reads. Test-owned JSON mutations are not
//! controlled admission or external-query authority; no public exporter is used.

use super::*;
use crate::bundle::retained::{
    decode_bundle, encode_bundle, replay_bundle, BundleLimits, RetainedField, RETAINED_SCHEMA,
};
use crate::bv_blast_solver::retained::wire::WireLimits;
use serde_json::{json, Value};

#[derive(Clone, Copy)]
enum Conclusion {
    Valid,
    False,
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

fn outside_bundle(conclusion: Conclusion) -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let stack = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let start = app(&mut terms, "bvsub", &[stack, size], word.clone());
    let guard = app(&mut terms, "bvuge", &[stack, size], Sort::Bool);
    let below = app(&mut terms, "bvult", &[observe, start], Sort::Bool);
    let above = app(&mut terms, "bvuge", &[observe, stack], Sort::Bool);
    let outside = app(&mut terms, "or", &[below, above], Sort::Bool);
    let not_outside = terms.mk_not_raw(outside);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", byte.clone());
    let mut memory = base;
    for offset in 0u32..2 {
        let offset = terms.mk_bitvec(offset.into(), 9);
        let index = app(&mut terms, "bvadd", &[start, offset], word.clone());
        memory = app(&mut terms, "store", &[memory, index, value], array.clone());
    }
    let after = app(&mut terms, "select", &[memory, observe], byte.clone());
    let before = app(&mut terms, "select", &[base, observe], byte);
    let equality = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_outside, equality], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let tail = match conclusion {
        Conclusion::Valid => negative,
        Conclusion::False => property,
    };
    let root = app(&mut terms, "and", &[guard, tail], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![clause], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), root, assumption, lemma);
    SerializableProofBundle::from_proof(&proof, &terms, vec![root])
}

fn limits(deadline: Instant) -> (BundleLimits, WireLimits) {
    (
        BundleLimits {
            max_json_bytes: 8 * 1024 * 1024,
            max_storage_bytes: 2 * 1024 * 1024 * 1024,
            max_work: 500_000_000,
            deadline,
        },
        WireLimits {
            max_json_bytes: 8 * 1024 * 1024,
            max_rows: 10_000,
            max_literals: 1_000_000,
            max_hints: 1_000_000,
            max_work: 50_000_000,
            max_storage_bytes: 192 * 1024 * 1024,
            deadline,
        },
    )
}

fn encoded(snapshot: &SerializableProofBundle, rows: Vec<RetainedStepPayload>) -> Vec<u8> {
    let deadline = end();
    let (limits, wire) = limits(deadline);
    encode_bundle(
        snapshot,
        &RetainedField::Present(rows),
        &limits,
        &wire,
        deadline,
        &mut |_, _| true,
    )
    .result
    .unwrap()
}

fn checked(bytes: &[u8]) -> Result<BundleReCheck, retained::ReadError> {
    let deadline = end();
    let (limits, wire) = limits(deadline);
    replay_bundle(bytes, &limits, &wire, deadline, &mut |_, _| true).result
}

#[test]
fn outside_pair_survives_whole_proof_capture_and_two_fresh_mandatory_v6_reads() {
    let before = producer_test_counter::count();
    let (bytes, expected) = {
        let snapshot = outside_bundle(Conclusion::Valid);
        let (checked, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
        assert_eq!(rows.len(), 1, "one inventory entry for the one BV lemma");
        let pair: Value = serde_json::from_slice(&rows[0].payload).unwrap();
        assert_eq!(pair.as_array().unwrap().len(), 2);
        assert!(pair[0]["outside_free_offset"].is_object());
        assert!(pair[1]["final_clause"].is_object());
        (encoded(&snapshot, rows), checked)
    }; // The source TermStore, Proof, snapshot and captured inventory are gone.
    assert_eq!(producer_test_counter::count(), before + 2);
    let deadline = end();
    let (limits, wire) = limits(deadline);
    let owned = {
        let independent_input = bytes.clone();
        decode_bundle(&independent_input, &limits, &wire, deadline, &mut |_, _| {
            true
        })
        .result
        .unwrap()
    };
    assert_eq!(owned.parts().0.schema, RETAINED_SCHEMA);
    assert_eq!(owned.parts().1.len(), 1);
    assert!(matches!(
        re_check_bundle_strict(owned.parts().0),
        Err(ProofCheckError::BundleSchemaMismatch { .. })
    ));
    let replayed = replay_versioned(&owned, deadline, &mut |_, _| true).unwrap();
    assert_eq!(replayed.quality, expected.quality);
    assert_eq!(replayed.assume_terms, expected.assume_terms);
    drop(owned);
    for _ in 0..2 {
        let replayed = replay_bundle(&bytes, &limits, &wire, deadline, &mut |_, _| true)
            .result
            .unwrap();
        assert_eq!(replayed.quality, expected.quality);
        assert_eq!(replayed.assume_terms, expected.assume_terms);
        assert_eq!(producer_test_counter::count(), before + 2);
    }
}

#[test]
fn valid_outside_evidence_cannot_replace_context_assumptions_or_terminal_proof() {
    let snapshot = outside_bundle(Conclusion::Valid);
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let before = producer_test_counter::count();
    let mut missing = snapshot.clone();
    missing.obligation_assertions.clear();
    let mut foreign = snapshot.clone();
    foreign.obligation_assertions = vec![snapshot.true_term.unwrap()];
    assert_ne!(
        foreign.obligation_assertions,
        snapshot.obligation_assertions
    );
    let mut nonterminal = snapshot.clone();
    nonterminal.steps.pop();
    let mut malformed = snapshot.clone();
    malformed.true_term = Some(TermId(u32::MAX));
    let mut bad_context = snapshot.clone();
    bad_context.constructor_selectors.push((
        "undeclared-constructor".to_owned(),
        vec!["field".to_owned()],
    ));
    for changed in [missing, foreign, nonterminal, malformed, bad_context] {
        assert!(checked(&encoded(&changed, rows.clone())).is_err());
    }
    checked(&encoded(&snapshot, rows)).unwrap();
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn complete_v6_outside_reads_require_both_uncorrupted_ordered_frames() {
    let snapshot = outside_bundle(Conclusion::Valid);
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let bytes = encoded(&snapshot, rows);
    let intact: Value = serde_json::from_slice(&bytes).unwrap();
    let before = producer_test_counter::count();
    for mutation in 0..7 {
        let mut bad = intact.clone();
        match mutation {
            0 => {
                bad.as_object_mut().unwrap().remove("retained");
            }
            1 => bad["retained"] = json!([]),
            2 => {
                bad["retained"][0]["payload"]
                    .as_array_mut()
                    .unwrap()
                    .remove(0);
            }
            3 => {
                bad["retained"][0]["payload"].as_array_mut().unwrap().pop();
            }
            4 => {
                bad["retained"][0]["payload"]
                    .as_array_mut()
                    .unwrap()
                    .swap(0, 1);
            }
            5 | 6 => {
                let index = mutation - 5;
                let role = ["outside_free_offset", "final_clause"][index];
                bad["retained"][0]["payload"][index][role]["empty_clause_id"] = json!(u64::MAX);
            }
            _ => unreachable!(),
        }
        assert!(checked(&serde_json::to_vec(&bad).unwrap()).is_err());
    }
    checked(&bytes).unwrap();
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn retained_outside_pair_does_not_prove_a_same_id_satisfiable_whole_snapshot() {
    let snapshot = outside_bundle(Conclusion::Valid);
    let (_, rows) = capture(&snapshot, end(), &mut |_, _| true).unwrap();
    let before = producer_test_counter::count();
    let neighbor = outside_bundle(Conclusion::False);
    assert_eq!(
        neighbor.obligation_assertions,
        snapshot.obligation_assertions
    );
    assert_eq!(neighbor.steps, snapshot.steps);
    assert_eq!(neighbor.term_entries.len(), snapshot.term_entries.len());
    assert_ne!(neighbor.term_entries, snapshot.term_entries);
    // stack=2, observe=2, constant-zero memory/value satisfies the neighbor's
    // asserted root. Its valid free-offset theorem cannot justify the false
    // final clause or the apparently empty resolution above it.
    assert!(checked(&encoded(&neighbor, rows.clone())).is_err());
    checked(&encoded(&snapshot, rows)).unwrap();
    assert_eq!(producer_test_counter::count(), before);
}
