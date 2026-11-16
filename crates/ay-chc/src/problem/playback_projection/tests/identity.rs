// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission};
use sha2::{Digest, Sha256};
use std::sync::Arc;

fn original() -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 8 * 1024 * 1024),
        Instant::now() + Duration::from_secs(60),
        Arc::new(|| false),
    )
}

fn datatype() -> ChcSort {
    ChcSort::Datatype {
        name: "Record".into(),
        constructors: crate::ChcDtConstructors::new(vec![crate::ChcDtConstructor {
            name: "record".into(),
            selectors: vec![crate::ChcDtSelector {
                name: "value".into(),
                sort: ChcSort::Int,
            }],
        }]),
    }
}

fn empty_query() -> ChcProblem {
    let mut source = ChcProblem::new();
    source.add_clause(HornClause::query(ClauseBody::empty()));
    source
}

fn assert_identity(row: &ChcQueryPlayback<'_>, expected_schema: &'static str) {
    let text = row.problem().normalized_input();
    let digest = format!("{:x}", Sha256::digest(text.as_bytes()));
    assert_eq!(
        crate::normalized_chc_input_schema_of(&text),
        Some(expected_schema)
    );
    assert_eq!(
        row.obligation_id().normalized_input_schema(),
        expected_schema
    );
    assert_eq!(row.obligation_id().content_sha256(), digest);
    assert_eq!(
        crate::proof_metadata::normalized_chc_input_identity_with_progress(
            row.problem(),
            &mut || true,
        ),
        Ok((expected_schema, digest)),
    );
}

#[test]
fn datatype_free_playback_identity_matches_prepared_bytes_and_ordinary_slice() {
    let source = chain();
    let ordinary = source.query_obligations().unwrap();
    let mut callback = || true;
    let mut control = control(&mut callback);
    let rows = source
        .query_obligations_with_playback(&mut control)
        .unwrap();
    assert_eq!(rows.len(), ordinary.len());
    for (row, ordinary) in rows.iter().zip(&ordinary) {
        assert_eq!(row.obligation_id(), ordinary.id());
        assert_identity(row, crate::NORMALIZED_CHC_INPUT_SCHEMA);
        original()
            .with_work(|work| {
                crate::prepare_normalized_chc_input_with_work(row.problem(), work)?.with_sha256(
                    |source, bytes, digest, _| {
                        assert!(std::ptr::eq(source, row.problem()));
                        assert_eq!(bytes, source.normalized_input());
                        assert_eq!(
                            crate::normalized_chc_input_schema_of(bytes),
                            Some(row.obligation_id().normalized_input_schema()),
                        );
                        assert_eq!(digest, row.obligation_id().content_sha256());
                        Ok(())
                    },
                )
            })
            .unwrap();
    }
}

#[test]
fn playback_identity_retains_hidden_datatypes_and_unused_registry_schema() {
    let mut hidden = empty_query();
    hidden.declare_predicate(
        "Unused",
        vec![ChcSort::Array(Box::new(ChcSort::Int), Box::new(datatype()))],
    );
    let mut scalar_registry = empty_query();
    scalar_registry.add_datatype_def(
        "Unused".into(),
        vec![("unused".into(), vec![("value".into(), ChcSort::Int)])],
    );
    let mut nested_registry = empty_query();
    nested_registry.add_datatype_def(
        "Unused".into(),
        vec![("unused".into(), vec![("value".into(), datatype())])],
    );
    for (source, schema) in [
        (
            hidden,
            crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
        ),
        (scalar_registry, crate::NORMALIZED_CHC_INPUT_SCHEMA),
        (
            nested_registry,
            crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
        ),
    ] {
        let ordinary = source.query_obligations().unwrap();
        let mut callback = || true;
        let mut control = control(&mut callback);
        let rows = source
            .query_obligations_with_playback(&mut control)
            .unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].obligation_id(), ordinary[0].id());
        assert_identity(&rows[0], schema);
        // All three are outside prepared canonical input's datatype-free
        // cohort, even when the ordinary serializer correctly emits v1.
        assert!(original()
            .with_work(|work| {
                crate::prepare_normalized_chc_input_with_work(rows[0].problem(), work)?
                    .with_input(|_, _, _| panic!("datatype-bearing preparation must refuse"))
            })
            .is_err());
    }
}

#[test]
fn playback_replay_checks_schema_and_digest_together() {
    for schema in [
        crate::NORMALIZED_CHC_INPUT_SCHEMA,
        crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
    ] {
        let mut source = empty_query();
        if schema == crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA {
            source.declare_predicate("Unused", vec![datatype()]);
        }
        let mut callback = || true;
        let mut control = control(&mut callback);
        let row = source
            .query_obligations_with_playback(&mut control)
            .unwrap()
            .remove(0);
        assert_identity(&row, schema);
        let bytes = wire(
            row.problem(),
            vec![GroundDerivationStep {
                clause_index: 0,
                env: Default::default(),
                premises: Vec::new(),
            }],
            0,
        );
        let envelope: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(envelope["normalized_input_schema"], schema);
        assert_eq!(
            envelope["normalized_input_sha256"],
            row.obligation_id().content_sha256()
        );
        let other = if schema == crate::NORMALIZED_CHC_INPUT_SCHEMA {
            crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA
        } else {
            crate::NORMALIZED_CHC_INPUT_SCHEMA
        };
        let text = std::str::from_utf8(&bytes).unwrap();
        let label = format!("\"normalized_input_schema\":\"{schema}\"");
        assert_eq!(text.matches(&label).count(), 1);
        let spliced = text.replace(&label, &format!("\"normalized_input_schema\":\"{other}\""));
        let error = row
            .lift_ground_derivation_v2(spliced.as_bytes(), &mut control)
            .unwrap_err();
        let ChcQueryPlaybackError::Artifact(error) = error else {
            panic!("a relabeled hash must be rejected by source authentication");
        };
        assert_eq!(
            error.reason,
            crate::ChcGroundDerivationArtifactErrorReason::SchemaMismatch
        );
        let (artifact, _) = row.lift_ground_derivation_v2(&bytes, &mut control).unwrap();
        let lifted: serde_json::Value = serde_json::from_slice(artifact.bytes()).unwrap();
        assert_eq!(lifted["normalized_input_schema"], schema);
        assert_eq!(
            lifted["normalized_input_sha256"],
            source.normalized_input_sha256()
        );
        let validated =
            crate::validate_chc_ground_derivation_artifact_v2(&source, artifact.bytes()).unwrap();
        assert_eq!(validated.artifact_sha256(), artifact.sha256());
    }
}
