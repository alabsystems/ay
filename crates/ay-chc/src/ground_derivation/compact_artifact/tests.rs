// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcParser;
use compact::{Arena, CompactStep, ValueNode};
use num_bigint::BigUint;

#[path = "tests/mutations.rs"]
mod mutations;
#[path = "tests/original_shape.rs"]
mod original_shape;
#[path = "tests/public_progress.rs"]
mod public_progress;
#[path = "tests/resources.rs"]
mod resources;

fn source(k: usize, safe: bool) -> String {
    let mut input = "(set-logic HORN)\n".to_owned();
    for level in 1..=k {
        let inner = if level == 1 {
            "(_ BitVec 8)".to_owned()
        } else {
            format!("D{}", level - 1)
        };
        input.push_str(&format!(
            "(declare-datatype D{level} ((mk{level} (a{level} {inner}) (b{level} {inner}))))\n"
        ));
    }
    input.push_str(&format!(
        "(declare-fun P (D{k}) Bool)\n(assert (forall ((x D{k})) (P x)))\n"
    ));
    let mut selected = "x".to_owned();
    for level in (1..=k).rev() {
        selected = format!("(a{level} {selected})");
    }
    let guard = if safe { "false" } else { "true" };
    input.push_str(&format!("(assert (forall ((x D{k})) (=> (and {guard} (P x) (= {selected} #x05)) false)))\n(check-sat)\n"));
    input
}

fn fixture(k: usize) -> (ChcProblem, CompactDerivation, Owner<'static>) {
    let problem = ChcParser::parse(&source(k, false)).expect("compact original source");
    let mut owner = Owner::capture().expect("original owner");
    let mut arena = Arena::new();
    let mut root = arena
        .intern(
            &ValueNode::BitVec {
                value: BigUint::from(5u8),
                width: 8,
            },
            &mut owner,
        )
        .expect("leaf");
    for level in 1..=k {
        root = arena
            .intern(
                &ValueNode::Datatype {
                    sort: format!("D{level}"),
                    constructor: format!("mk{level}"),
                    fields: vec![root, root],
                },
                &mut owner,
            )
            .expect("shared complete constructor");
    }
    let steps = vec![
        CompactStep {
            clause_index: 0,
            env: [("x".into(), root)].into_iter().collect(),
            premises: vec![],
        },
        CompactStep {
            clause_index: 1,
            env: [("x".into(), root)].into_iter().collect(),
            premises: vec![0],
        },
    ];
    (
        problem,
        CompactDerivation {
            arena,
            steps,
            query_step: 1,
        },
        owner,
    )
}

fn artifact(k: usize) -> (ChcProblem, ChcProofRunArtifact) {
    let (problem, derivation, mut owner) = fixture(k);
    let artifact = encode_with_owner(&problem, &derivation, &mut owner)
        .expect("source-bound compact artifact");
    (problem, artifact)
}

#[test]
fn k10_roundtrip_replays_original_source_and_borrows_shared_all_field_values() {
    let (_, artifact) = artifact(10);
    let original = ChcParser::parse(&source(10, false)).expect("independent source parse");
    let bytes = artifact.into_bytes();
    let checked = validate_chc_compact_ground_derivation_artifact(&original, &bytes)
        .expect("fresh original replay");
    assert_eq!(
        checked.artifact_schema(),
        CHC_COMPACT_GROUND_DERIVATION_SCHEMA
    );
    assert_eq!(checked.artifact_role(), CHC_COMPACT_GROUND_DERIVATION_ROLE);
    assert_eq!(checked.artifact_bytes(), bytes.len());
    assert_eq!(checked.node_count(), 11);
    assert_eq!(checked.step_count(), 2);
    assert_eq!(checked.query_step(), 1);
    assert_eq!(checked.steps().len(), 2);
    assert_eq!(checked.nodes().len(), 11);
    let step = checked.step(1).expect("query");
    assert_eq!(step.clause_index(), 1);
    assert_eq!(step.premises(), &[0]);
    assert_eq!(step.bindings().count(), 1);
    let mut id = step.binding("x").expect("original variable");
    for level in (1..=10).rev() {
        let node = checked.node(id).expect("bound shared node");
        let expected = (format!("D{level}"), format!("mk{level}"));
        assert_eq!(
            node.datatype(),
            Some((expected.0.as_str(), expected.1.as_str()))
        );
        let fields: Vec<_> = node.fields().collect();
        assert_eq!(fields.len(), 2, "unread b-field is concrete, never omitted");
        assert_eq!(fields[0], fields[1], "sharing remains explicit");
        assert!(fields[0].index() < id.index());
        id = fields[0];
    }
    assert_eq!(
        checked.node(id).expect("leaf").bitvector(),
        Some((&BigUint::from(5u8), 8))
    );
}

#[test]
fn artifact_storage_follows_unique_nodes_not_expanded_leaf_count() {
    let (_, small) = artifact(4);
    let (_, large) = artifact(16);
    let small = small.into_bytes();
    let large = large.into_bytes();
    assert!(large.len() < small.len() * 4);
    assert!(large.len() < 16 * 1024);
    let checked = validate_chc_compact_ground_derivation_artifact(
        &ChcParser::parse(&source(16, false)).expect("source"),
        &large,
    )
    .expect("larger full DAG replay");
    assert_eq!(checked.node_count(), 17);
}

#[test]
fn changed_original_source_never_inherits_an_old_compact_capability() {
    let (_, artifact) = artifact(4);
    let safe = ChcParser::parse(&source(4, true)).expect("safe neighbor");
    let failure = validate_chc_compact_ground_derivation_artifact(&safe, &artifact.into_bytes())
        .expect_err("source mismatch");
    assert_eq!(failure.reason, Reason::ProblemHashMismatch);
}

#[test]
fn producer_rejects_false_guard_without_serializing_a_candidate() {
    let (_, derivation, mut owner) = fixture(4);
    let safe = ChcParser::parse(&source(4, true)).expect("safe neighbor");
    assert!(encode_with_owner(&safe, &derivation, &mut owner).is_err());
}
