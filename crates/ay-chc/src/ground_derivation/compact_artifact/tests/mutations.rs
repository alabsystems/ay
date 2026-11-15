// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn mutate(change: impl FnOnce(&mut wire::Envelope)) -> ChcGroundDerivationArtifactError {
    let (problem, artifact) = artifact(3);
    let mut envelope: wire::Envelope =
        serde_json::from_slice(&artifact.into_bytes()).expect("producer JSON");
    change(&mut envelope);
    let bytes = serde_json::to_vec(&envelope).expect("same canonical field order");
    validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
        .expect_err("mutated evidence must fail")
}

#[test]
fn cycles_forward_children_and_forward_premises_are_rejected() {
    assert_eq!(
        mutate(|e| {
            let wire::Node::Datatype { fields, .. } = &mut e.nodes[1] else {
                panic!("datatype")
            };
            fields[0] = 1;
        })
        .reason,
        Reason::IndexOutOfRange
    );
    assert_eq!(
        mutate(|e| {
            let wire::Node::Datatype { fields, .. } = &mut e.nodes[1] else {
                panic!("datatype")
            };
            fields[0] = 3;
        })
        .reason,
        Reason::IndexOutOfRange
    );
    assert_eq!(
        mutate(|e| e.steps[1].premises[0] = 1).reason,
        Reason::IndexOutOfRange
    );
}

#[test]
fn nominal_sort_constructor_and_every_field_are_checked() {
    mutate(|e| {
        let wire::Node::Datatype { sort, .. } = &mut e.nodes[1] else {
            panic!("datatype")
        };
        *sort = "D2".into();
    });
    mutate(|e| {
        let wire::Node::Datatype { constructor, .. } = &mut e.nodes[1] else {
            panic!("datatype")
        };
        *constructor = "mk2".into();
    });
    mutate(|e| {
        let wire::Node::Datatype { fields, .. } = &mut e.nodes[1] else {
            panic!("datatype")
        };
        fields.pop();
    });
    mutate(|e| {
        let wire::Node::Bitvector { value_hex, .. } = &mut e.nodes[0] else {
            panic!("leaf")
        };
        *value_hex = "6".into();
    });
}

#[test]
fn original_bindings_query_root_clause_order_and_counts_are_authenticated() {
    mutate(|e| e.steps[1].bindings[0].name = "different".into());
    mutate(|e| e.steps[1].bindings[0].value = 0);
    mutate(|e| e.query_step = 0);
    mutate(|e| e.steps[1].clause_index = 0);
    assert_eq!(
        mutate(|e| e.binding_count += 1).reason,
        Reason::CountMismatch
    );
    assert_eq!(
        mutate(|e| e.source_clause_sequence_sha256 = "0".repeat(64)).reason,
        Reason::ClauseSequenceHashMismatch
    );
    assert_eq!(
        mutate(|e| e.normalized_input_schema = "ay.chc.normalized-input/v1".into()).reason,
        Reason::SchemaMismatch
    );
}

#[test]
fn duplicate_nodes_bindings_and_noncanonical_numbers_cannot_hide_in_dag() {
    assert_eq!(
        mutate(|e| {
            e.nodes.push(wire::Node::Bitvector {
                width: 8,
                value_hex: "5".into(),
            });
            e.value_node_count += 1;
        })
        .reason,
        Reason::NonCanonicalEnvelope
    );
    assert_eq!(
        mutate(|e| {
            e.steps[0].bindings.push(wire::Binding {
                name: "x".into(),
                value: 3,
            });
            e.binding_count += 1;
        })
        .reason,
        Reason::BindingSetMismatch
    );
    for value in ["05", "-5", "FF", "100"] {
        assert_eq!(
            mutate(|e| {
                let wire::Node::Bitvector { value_hex, .. } = &mut e.nodes[0] else {
                    panic!("leaf")
                };
                *value_hex = value.into();
            })
            .reason,
            Reason::InvalidValue
        );
    }
}

#[test]
fn duplicate_json_keys_unknown_fields_and_trailing_bytes_are_refused() {
    let (problem, artifact) = artifact(2);
    let canonical = String::from_utf8(artifact.into_bytes()).expect("UTF8");
    let duplicate = canonical.replacen(
        "{\"schema\":",
        &format!("{{\"schema\":\"{CHC_COMPACT_GROUND_DERIVATION_SCHEMA}\",\"schema\":"),
        1,
    );
    let unknown = canonical.replacen("{\"schema\":", "{\"trusted\":true,\"schema\":", 1);
    let trailing = format!("{canonical} ");
    for altered in [duplicate, unknown, trailing] {
        assert!(
            validate_chc_compact_ground_derivation_artifact(&problem, altered.as_bytes()).is_err()
        );
    }
}

#[test]
fn oversized_bytes_refuse_before_any_recursive_decoding() {
    let (problem, _, _) = fixture(1);
    let bytes = vec![b' '; CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES + 1];
    assert_eq!(
        validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
            .expect_err("byte cap")
            .reason,
        Reason::ArtifactTooLarge
    );
}
