// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let a = terms.mk_var("start_a", word.clone());
    let b = terms.mk_var("start_b", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let end_a = app(&mut terms, "bvadd", &[a, size], word.clone());
    let end_b = app(&mut terms, "bvadd", &[b, size], word);
    let after_b = app(&mut terms, "bvuge", &[a, end_b], Sort::Bool);
    let after_a = app(&mut terms, "bvuge", &[b, end_a], Sort::Bool);
    let separate = app(&mut terms, "or", &[after_b, after_a], Sort::Bool);
    let bound = terms.mk_bitvec(509.into(), 9);
    let nowrap_a = app(&mut terms, "bvule", &[a, bound], Sort::Bool);
    let nowrap_b = app(&mut terms, "bvule", &[b, bound], Sort::Bool);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", byte.clone());
    let stored = app(&mut terms, "store", &[base, a, value], array);
    let after = app(&mut terms, "select", &[stored, b], byte.clone());
    let before = app(&mut terms, "select", &[base, b], byte);
    let property = app(&mut terms, "=", &[after, before], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = app(
        &mut terms,
        "and",
        &[separate, nowrap_a, nowrap_b, negative],
        Sort::Bool,
    );
    let clause = terms.mk_not_raw(root);
    (terms, clause)
}

#[test]
fn disjoint_session_replays_required_prerequisites_without_search_or_memo() {
    let (terms, clause) = source();
    assert!(super::super::super::disjoint::Shape::recognize(&terms, &[clause]).is_some());
    assert!(bv_bitblast_requires_proof_producer(&terms, &[clause]));
    let proof = proof(clause, 1);
    let calls = producer_test_counter::count();
    let attempts = proof_producing_control::ATTEMPTS.with(Cell::get);
    let source = terms.entries_snapshot();
    let payloads = capture(&terms, &proof);
    assert_eq!(payloads.len(), 1);
    assert_eq!(producer_test_counter::count(), calls + 2);
    let calls = producer_test_counter::count();
    replay(&terms, &proof, &payloads).unwrap();
    terms.record_strict_bv_semantics_validated(&[clause]);
    let bad = [RetainedStepPayload {
        step: 0,
        payload: b"not JSON".to_vec(),
    }];
    assert!(replay(&terms, &proof, &bad).is_err());
    assert!(replay(&terms, &proof, &[]).is_err());
    replay(&terms, &proof, &payloads).unwrap();
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(proof_producing_control::ATTEMPTS.with(Cell::get), attempts);
    assert_eq!(terms.entries_snapshot(), source);
    assert!(terms.strict_bv_semantics_validated(&[clause]));
}
