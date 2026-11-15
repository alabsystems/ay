// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_child_field_intersects_and_optional_none_cannot_relax_root() {
    let (root, root_gates, _) = limits();
    macro_rules! field {
        (($($field:ident).+); $name:ident) => { {
            let mut root = root.clone();
            let mut child = root.clone();
            root.$($field).+.$name = 3;
            child.$($field).+.$name = 7;
            let (got, _) = super::super::limits::child(&root, &root_gates, &child, &root_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$($field).+.$name, 3, stringify!($name));
            child.$($field).+.$name = 1;
            let (got, _) = super::super::limits::child(&root, &root_gates, &child, &root_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$($field).+.$name, 1, stringify!($name));
        } };
    }
    macro_rules! fields {
        ($path:tt; $($name:ident),+ $(,)?) => { $( field!($path; $name); )+ };
    }
    // Separate macros avoid pretending these differently typed fields share
    // an owning reflection/serialization path.
    macro_rules! top {
        ($($name:ident),+ $(,)?) => { $( {
            let mut root = root.clone();
            let mut child = root.clone();
            root.$name = 3;
            child.$name = 7;
            let (got, _) = super::super::limits::child(&root, &root_gates, &child, &root_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$name, 3, stringify!($name));
            child.$name = 1;
            let (got, _) = super::super::limits::child(&root, &root_gates, &child, &root_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$name, 1, stringify!($name));
        } )+ };
    }
    top!(
        max_expr_nodes,
        max_expr_occurrences,
        max_expr_depth,
        max_leaf_name_bytes,
        max_internal_width,
        max_estimated_gate_work,
        max_construction_bytes,
        max_resolution_steps,
        max_expanded_literals,
        max_expansion_work,
        max_expansion_bytes
    );
    fields!((resolution); max_num_vars, max_input_clauses, max_input_literals,
        max_input_clause_literals, max_input_bytes, solver_clause_db_reduction_threshold_bytes,
        max_proof_output_bytes, max_derived_steps, max_derived_literals, max_hints,
        max_pending_deletions, max_codec_bytes, max_backward_reconstruction_bytes);
    fields!((resolution.validation); max_original_clauses, max_original_literals,
        max_derived_steps, max_derived_literals, max_hints, max_work, max_bytes);
    macro_rules! gates {
        ($($name:ident),+ $(,)?) => { $( {
            let mut root_gates = root_gates;
            let mut child_gates = root_gates;
            root_gates.$name = 3;
            child_gates.$name = 7;
            let (_, got) = super::super::limits::child(&root, &root_gates, &root, &child_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$name, 3, stringify!($name));
            child_gates.$name = 1;
            let (_, got) = super::super::limits::child(&root, &root_gates, &root, &child_gates, root_gates.deadline.unwrap());
            assert_eq!(got.$name, 1, stringify!($name));
        } )+ };
    }
    gates!(
        max_vars,
        max_bit_lemmas,
        max_clauses,
        max_clause_literals,
        max_original_literals,
        max_resolution_steps,
        max_derived_literals,
        max_work
    );
    let mut child = root.clone();
    child.resolution.max_conflicts = None;
    child.resolution.max_decisions = None;
    child.resolution.deadline = None;
    child.resolution.validation.deadline = None;
    let mut child_gates = root_gates;
    child_gates.deadline = None;
    let (got, gates) = limits::child(
        &root,
        &root_gates,
        &child,
        &child_gates,
        root_gates.deadline.unwrap(),
    );
    assert_eq!(got.resolution.max_conflicts, root.resolution.max_conflicts);
    assert_eq!(got.resolution.max_decisions, root.resolution.max_decisions);
    assert_eq!(got.resolution.deadline, root.resolution.deadline);
    assert_eq!(
        got.resolution.validation.deadline,
        root.resolution.validation.deadline
    );
    assert_eq!(gates.deadline, root_gates.deadline);
}

#[test]
fn a_child_may_drop_the_swept_retry_but_never_add_it() {
    let (root, root_gates, _) = limits();
    for (root_sweep, child_sweep) in [(false, true), (true, false), (true, true)] {
        let mut root = root.clone();
        let mut child = root.clone();
        root.sweep = root_sweep;
        child.sweep = child_sweep;
        let (got, _) = limits::child(
            &root,
            &root_gates,
            &child,
            &root_gates,
            root_gates.deadline.unwrap(),
        );
        assert_eq!(got.sweep, root_sweep && child_sweep);
    }
}

fn manual_frame() -> Vec<u8> {
    // Independent canonical a=a CNF [e,a], [e,!a], [!e]. Positive
    // literal/hint/row counts do not depend on a producer's lucky search.
    let payload = RetainedBvRefutation {
        version: VERSION,
        rows: vec![
            RetainedRupRow {
                id: 4,
                literals: vec![2],
                hints: vec![1, 2],
            },
            RetainedRupRow {
                id: 5,
                literals: vec![],
                hints: vec![3, 4],
            },
        ],
        empty_clause_id: 5,
    };
    serde_json::to_vec(&payload).unwrap()
}

fn replay_twice(bytes: &[u8], wire: &wire::WireLimits) -> Result<Metered<()>, MeteredError> {
    let (mut proof, gates, _) = limits();
    no_search(&mut proof);
    let (lhs, rhs) = source(0);
    run(
        &proof,
        &gates,
        wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            chain.replay_one(&lhs, &rhs, bytes, &proof, &gates)?;
            chain.replay_one(&lhs, &rhs, bytes, &proof, &gates)
        },
    )
}

#[test]
fn aggregate_json_rows_literals_hints_and_wire_work_are_not_renewed() {
    let bytes = manual_frame();
    let (proof, gates, mut wire) = limits();
    let decoded = wire::decode(&bytes, &wire, &proof, &gates, &mut || true);
    assert!(decoded.result.is_ok());
    wire.max_json_bytes = bytes.len() * 2;
    wire.max_rows = 4;
    wire.max_literals = 2;
    wire.max_hints = 8;
    wire.max_work = u64::try_from(decoded.usage.charged_work).unwrap() * 2;
    replay_twice(&bytes, &wire).unwrap();
    for field in 0..5 {
        let mut short = wire;
        match field {
            0 => short.max_json_bytes -= 1,
            1 => short.max_rows -= 1,
            2 => short.max_literals -= 1,
            3 => short.max_hints -= 1,
            4 => short.max_work -= 1,
            _ => unreachable!(),
        }
        assert!(replay_twice(&bytes, &short).is_err(), "field {field}");
    }
}

#[test]
fn earlier_capture_capacity_and_replay_input_reduce_later_wire_scratch() {
    let (proof, gates, mut wire) = limits();
    let (lhs, rhs) = source(0);
    let payload = capture_bv_expr_refutation(&lhs, &rhs, &proof, &gates, &mut || true).unwrap();
    let encoded = wire::encode(&payload, &wire, &proof, &gates, &mut || true);
    let bytes = encoded.result.unwrap();
    assert_eq!(
        encoded.usage.returned_owned_bytes,
        size_of::<Vec<u8>>() + bytes.capacity()
    );
    wire.max_storage_bytes = encoded.usage.peak_storage_bytes + encoded.usage.returned_owned_bytes;
    let invoke = |wire: &wire::WireLimits| {
        let (lhs, rhs) = source(0);
        run(
            &proof,
            &gates,
            wire,
            allowance(1_000_000),
            &mut || true,
            |chain| {
                let a = chain.capture_one(&lhs, &rhs, &proof, &gates)?;
                let b = chain.capture_one(&lhs, &rhs, &proof, &gates)?;
                Ok((a, b))
            },
        )
    };
    invoke(&wire).unwrap();
    wire.max_storage_bytes -= 1;
    assert!(invoke(&wire).is_err());
    let (_, _, mut wire) = limits();
    let decoded = wire::decode(&bytes, &wire, &proof, &gates, &mut || true);
    assert!(decoded.result.is_ok());
    wire.max_storage_bytes = decoded.usage.peak_storage_bytes + bytes.len();
    replay_twice(&bytes, &wire).unwrap();
    wire.max_storage_bytes -= 1;
    assert!(replay_twice(&bytes, &wire).is_err());
}

#[test]
fn prior_frame_reservations_also_reduce_codec_and_dag_bytes_without_refund() {
    let (mut proof, gates, wire) = limits();
    let mut budget = budget::Budget::new(wire, &proof);
    budget.commit(Shape::default(), 1, 17, 0).unwrap();
    let codec = proof.resolution.max_codec_bytes;
    let dag = proof.resolution.validation.max_bytes;
    budget.child(&mut proof, wire.deadline).unwrap();
    assert_eq!(proof.resolution.max_codec_bytes, codec - 17);
    assert_eq!(proof.resolution.validation.max_bytes, dag - 17);
    proof.resolution.max_codec_bytes = 16;
    assert!(budget.child(&mut proof, wire.deadline).is_err());
    let (lhs, rhs) = source(0);
    let (proof, _, mut wire) = limits();
    let single = capture(
        &lhs,
        &rhs,
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
    )
    .unwrap();
    wire.max_json_bytes = single.value.len();
    assert!(run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            drop(chain.capture_one(&lhs, &rhs, &proof, &gates)?);
            chain.capture_one(&lhs, &rhs, &proof, &gates)
        }
    )
    .is_err());
}
