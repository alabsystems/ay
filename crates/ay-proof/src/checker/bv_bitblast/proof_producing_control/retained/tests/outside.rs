// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private metered adapter tests, not public retained-bundle adoption.

use super::super::metered::{self as bridge, MeteredBridgeError};
use super::*;
use crate::bv_blast_solver::retained::{
    producer_test_counter,
    wire::{self, WireLimits},
    work::{Metered, WorkAllowance, WorkUsage},
};

mod controls;

const GRANT: u64 = 50_000_000;
const ROLES: [&str; 2] = ["outside_free_offset", "final_clause"];

#[derive(Clone, Copy, Debug)]
enum Operation {
    Capture,
    Replay,
}

#[derive(Clone, Copy, Debug)]
enum Source {
    Valid,
    FalseConclusion,
    WrongValueWidth,
    MalformedOverwrittenValue,
}

fn wire_limits(end: Instant) -> WireLimits {
    WireLimits {
        max_json_bytes: 8 * 1024 * 1024,
        max_rows: 4096,
        max_literals: 64_000,
        max_hints: 64_000,
        max_work: GRANT,
        max_storage_bytes: 128 * 1024 * 1024,
        deadline: end,
    }
}

fn fixture(source: Source) -> (TermStore, TermId) {
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
    let value_sort = match source {
        Source::WrongValueWidth => word.clone(),
        _ => byte.clone(),
    };
    let value = terms.mk_var("value", value_sort);
    let mut memory = base;
    for offset in 0u32..2 {
        let offset = terms.mk_bitvec(offset.into(), 9);
        let index = app(&mut terms, "bvadd", &[start, offset], word.clone());
        if matches!(source, Source::MalformedOverwrittenValue) {
            let bad = app(&mut terms, "bvadd", &[value], byte.clone());
            memory = app(&mut terms, "store", &[memory, index, bad], array.clone());
        }
        memory = app(&mut terms, "store", &[memory, index, value], array.clone());
    }
    let after = app(&mut terms, "select", &[memory, observe], byte.clone());
    let before = app(&mut terms, "select", &[base, observe], byte);
    let equality = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_outside, equality], Sort::Bool);
    // Allocate the same nodes/IDs even in the false neighbor: the final root,
    // not a transport-supplied role or matching ID, decides what is proved.
    let negative = terms.mk_not_raw(property);
    let tail = match source {
        Source::FalseConclusion => property,
        _ => negative,
    };
    let root = app(&mut terms, "and", &[guard, tail], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    assert!(outside_frame::Shape::recognize(&terms, &[clause]).is_some());
    assert!(crate::checker::bv_bitblast::disjoint::Shape::recognize(&terms, &[clause]).is_none());
    (terms, clause)
}

fn capture_bytes(terms: &TermStore, clause: TermId) -> Metered<Vec<u8>> {
    let end = deadline();
    let (proof, gates) = limits(end);
    bridge::capture_clause(
        terms,
        &[clause],
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true,
    )
    .unwrap()
}

fn invoke(
    operation: Operation,
    terms: &TermStore,
    clause: TermId,
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<WorkUsage, MeteredBridgeError> {
    match operation {
        Operation::Capture => {
            bridge::capture_clause(terms, &[clause], proof, gates, wire, allowance, poll)
                .map(|result| result.work)
        }
        Operation::Replay => {
            bridge::replay_clause(terms, &[clause], bytes, proof, gates, wire, allowance, poll)
                .map(|result| result.work)
        }
    }
}

fn replay_bytes(
    terms: &TermStore,
    clause: TermId,
    bytes: &[u8],
) -> Result<WorkUsage, MeteredBridgeError> {
    let end = deadline();
    let (mut proof, gates) = limits(end);
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    invoke(
        Operation::Replay,
        terms,
        clause,
        bytes,
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true,
    )
}

fn total(usage: WorkUsage) -> u64 {
    usage.producer_validation + usage.retained_prefix + usage.gates + usage.dag + usage.wire
}

#[test]
fn two_ordered_frames_survive_producer_drop_and_replay_against_fresh_source() {
    let calls = producer_test_counter::count();
    let bytes = {
        let (terms, clause) = fixture(Source::Valid);
        let before = terms.entries_snapshot();
        let result = capture_bytes(&terms, clause);
        assert!(result.work.producer_validation > 0);
        assert_eq!(terms.entries_snapshot(), before);
        result.value
    };
    assert_eq!(producer_test_counter::count(), calls + 2);
    let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(json.as_array().unwrap().len(), 2);
    for (frame, role) in json.as_array().unwrap().iter().zip(ROLES) {
        assert_eq!(frame.as_object().unwrap().len(), 1);
        assert!(frame[role].is_object());
    }
    let end = deadline();
    let (mut proof, gates) = limits(end);
    let frames = wire::pair::decode(&bytes, &wire_limits(end), &proof, &gates, &mut || true)
        .result
        .unwrap();
    for frame in frames {
        assert!(
            !wire::decode(frame, &wire_limits(end), &proof, &gates, &mut || true)
                .result
                .unwrap()
                .rows
                .is_empty()
        );
    }
    let (terms, clause) = fixture(Source::Valid);
    let before = terms.entries_snapshot();
    let calls = producer_test_counter::count();
    let attempts = crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    for bound in [Some(0), None] {
        proof.resolution.max_conflicts = bound;
        proof.resolution.max_decisions = bound;
        let usage = invoke(
            Operation::Replay,
            &terms,
            clause,
            &bytes,
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .unwrap();
        assert_eq!(usage.producer_validation, 0);
        assert!(usage.retained_prefix > 0 && usage.gates > 0 && usage.dag > 0);
    }
    assert_eq!(producer_test_counter::count(), calls);
    assert_eq!(
        crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get),
        attempts
    );
    assert_eq!(terms.entries_snapshot(), before);
}

#[test]
fn both_frames_are_mandatory_and_corruption_cannot_use_semantic_memo() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    let calls = producer_test_counter::count();
    replay_bytes(&terms, clause, &bytes).unwrap();
    terms.record_strict_bv_semantics_validated(&[clause]);
    let frames: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    for input in [b"".as_slice(), b"null", b"{}", b"[]", b"[", b"[{},{}]"] {
        assert!(replay_bytes(&terms, clause, input).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.extend_from_slice(b" false");
    assert!(replay_bytes(&terms, clause, &trailing).is_err());
    let deep = format!(
        "[{{\"outside_free_offset\":{{\"nested\":{}0{}}}}},{{\"final_clause\":{{}}}}]",
        "[".repeat(1024),
        "]".repeat(1024),
    );
    assert!(replay_bytes(&terms, clause, deep.as_bytes()).is_err());
    for mutation in 0..7 {
        let mut bad = frames.clone();
        let array = bad.as_array_mut().unwrap();
        match mutation {
            0 => {
                array.remove(0);
            }
            1 => {
                array.pop();
            }
            2 => array.push(array[1].clone()),
            3 => array.swap(0, 1),
            4 | 5 => {
                let index = mutation - 4;
                array[index][ROLES[index]]["empty_clause_id"] = serde_json::json!(u64::MAX);
            }
            6 => array[0][ROLES[0]]["rows"] = serde_json::json!([]),
            _ => unreachable!(),
        }
        assert!(replay_bytes(&terms, clause, &serde_json::to_vec(&bad).unwrap()).is_err());
    }
    replay_bytes(&terms, clause, &bytes).unwrap();
    assert!(terms.strict_bv_semantics_validated(&[clause]));
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn a_valid_offset_theorem_does_not_authorize_a_changed_false_final_clause() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    let calls = producer_test_counter::count();
    let (neighbor, changed) = fixture(Source::FalseConclusion);
    assert_eq!(
        clause, changed,
        "same IDs do not bind a different source graph"
    );
    // stack=2, observe=2, constant-zero memory/value satisfies this root.
    // Recognition and its offset theorem still hold; the final clause does not.
    assert!(replay_bytes(&neighbor, changed, &bytes).is_err());
    assert_eq!(producer_test_counter::count(), calls);
    assert!(!neighbor.strict_bv_semantics_validated(&[changed]));
    let end = deadline();
    let (proof, gates) = limits(end);
    assert!(invoke(
        Operation::Capture,
        &neighbor,
        changed,
        b"",
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true,
    )
    .is_err());
}

#[test]
fn concrete_store_operands_cannot_be_discarded_by_the_offset_route() {
    let (terms, clause) = fixture(Source::Valid);
    let bytes = capture_bytes(&terms, clause).value;
    for source in [Source::WrongValueWidth, Source::MalformedOverwrittenValue] {
        let (malformed, clause) = fixture(source);
        let before = malformed.entries_snapshot();
        let calls = producer_test_counter::count();
        assert!(
            replay_bytes(&malformed, clause, &bytes).is_err(),
            "{source:?}"
        );
        assert_eq!(producer_test_counter::count(), calls);
        let end = deadline();
        let (proof, gates) = limits(end);
        let result = invoke(
            Operation::Capture,
            &malformed,
            clause,
            b"",
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        );
        assert!(
            matches!(
                result.as_ref(),
                Err(MeteredBridgeError::Bridge(BridgeError::Source(_)))
            ),
            "{source:?}: {result:?}"
        );
        // The adapter's whole-source admission rejects these malformed
        // operands before even the free-offset producer can be entered.
        assert_eq!(producer_test_counter::count(), calls);
        assert_eq!(malformed.entries_snapshot(), before);
        assert!(!malformed.strict_bv_semantics_validated(&[clause]));
    }
}
