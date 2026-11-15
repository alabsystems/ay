// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn outside_frame() -> (TermStore, TermId) {
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
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    (terms, clause)
}

pub(super) fn disjoint() -> (TermStore, TermId) {
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

fn assert_specialized(terms: &TermStore, clause: TermId, route: SpecializedRoute) {
    let deadline = deadline();
    let (mut proof, mut gates) = limits(deadline);
    // Recognition must refuse before construction/search, even when those
    // grants are zero and replay has no declared payload to read.
    proof.max_estimated_gate_work = 0;
    proof.max_construction_bytes = 0;
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    gates.max_work = 0;
    let before = terms.entries_snapshot();
    assert_eq!(
        capture_clause(terms, &[clause], deadline, &proof, &gates, &mut || true),
        Err(BridgeError::Specialized(route))
    );
    assert_eq!(
        replay_clause(
            terms,
            &[clause],
            None,
            deadline,
            &proof,
            &gates,
            &mut || true
        ),
        Err(BridgeError::Specialized(route))
    );
    assert_eq!(terms.entries_snapshot(), before);
    assert!(!terms.strict_bv_semantics_validated(&[clause]));
}

#[test]
fn outside_frame_prerequisite_route_is_explicitly_unsupported() {
    let (terms, clause) = outside_frame();
    assert!(super::super::outside_frame::Shape::recognize(&terms, &[clause]).is_some());
    assert!(crate::checker::bv_bitblast::disjoint::Shape::recognize(&terms, &[clause]).is_none());
    assert_specialized(&terms, clause, SpecializedRoute::OutsideFrame);
}

#[test]
fn disjoint_prerequisite_route_is_explicitly_unsupported() {
    let (terms, clause) = disjoint();
    assert!(crate::checker::bv_bitblast::disjoint::Shape::recognize(&terms, &[clause]).is_some());
    assert!(super::super::outside_frame::Shape::recognize(&terms, &[clause]).is_none());
    assert_specialized(&terms, clause, SpecializedRoute::Disjoint);
}

#[test]
fn empty_and_oversized_clauses_refuse_but_exact_cap_reaches_source_validation() {
    let mut terms = TermStore::new();
    let unsupported = app(&mut terms, "retained_unsupported_bool", &[], Sort::Bool);
    let cap = crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_CLAUSE_LITERALS;
    let deadline = deadline();
    let (proof, gates) = limits(deadline);
    for count in [0, cap, cap + 1] {
        let clause = vec![unsupported; count];
        let capture = capture_clause(&terms, &clause, deadline, &proof, &gates, &mut || true);
        let replay = replay_clause(&terms, &clause, None, deadline, &proof, &gates, &mut || {
            true
        });
        if count == cap {
            assert!(matches!(capture, Err(BridgeError::Source(_))));
            assert!(matches!(replay, Err(BridgeError::Source(_))));
        } else {
            assert_eq!(capture, Err(BridgeError::ClauseBound));
            assert_eq!(replay, Err(BridgeError::ClauseBound));
        }
    }
    assert!(!terms.strict_bv_semantics_validated(&[unsupported]));
}
