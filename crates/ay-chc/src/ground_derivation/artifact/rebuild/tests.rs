// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn authenticated_rebuild_keeps_both_legacy_envelopes_exact() {
    let (problem, derivation) = super::super::tests::fixture();
    let legacy = envelope_for_derivation(&problem, &derivation).unwrap();
    let mut progress = || true;
    let mut control = GroundValidationControl::new(&mut progress);
    let identity = AuthenticatedSource::check(
        &problem,
        &legacy.normalized_input_schema,
        &legacy.normalized_input_sha256,
        &legacy.source_clause_sequence_sha256,
        "artifact",
        &mut control,
    )
    .unwrap();
    assert_eq!(
        identity.rebuild_v1(&derivation, &mut control).unwrap(),
        legacy
    );

    let (problem, derivation) = super::super::tests::uf_fixture();
    let legacy = envelope_v2_for_derivation(&problem, &derivation).unwrap();
    let identity = AuthenticatedSource::check(
        &problem,
        &legacy.normalized_input_schema,
        &legacy.normalized_input_sha256,
        &legacy.source_clause_sequence_sha256,
        "v2 artifact",
        &mut control,
    )
    .unwrap();
    assert_eq!(
        identity.rebuild_v2(&derivation, &mut control).unwrap(),
        legacy
    );
}

#[test]
fn problem_mismatch_does_not_start_positional_hashing() {
    let (problem, _) = super::super::tests::fixture();
    let mut normalization_polls = 0;
    normalized_chc_input_sha256_with_progress(&problem, &mut || {
        normalization_polls += 1;
        true
    })
    .unwrap();
    for label in ["artifact", "v2 artifact"] {
        let mut polls = 0;
        let rejected = AuthenticatedSource::check(
            &problem,
            crate::NORMALIZED_CHC_INPUT_SCHEMA,
            "wrong-normalized-hash",
            "wrong-positional-hash",
            label,
            &mut GroundValidationControl::new(&mut || {
                polls += 1;
                polls <= normalization_polls
            }),
        )
        .err()
        .expect("bad identity must not authenticate");
        assert_eq!(
            rejected.reason,
            ChcGroundDerivationArtifactErrorReason::ProblemHashMismatch
        );
        assert_eq!(polls, normalization_polls);
        assert_eq!(
            rejected.detail,
            format!("{label} normalized-input hash does not match the supplied problem")
        );
    }
}

#[test]
fn matching_normalized_hash_does_not_authorize_wrong_clause_order() {
    let (problem, _) = super::super::tests::fixture();
    let rejected = AuthenticatedSource::check(
        &problem,
        crate::NORMALIZED_CHC_INPUT_SCHEMA,
        &normalized_chc_input_sha256(&problem),
        "wrong-positional-hash",
        "artifact",
        &mut GroundValidationControl::new(&mut || true),
    )
    .err()
    .expect("positional mismatch must not authenticate");
    assert_eq!(
        rejected.reason,
        ChcGroundDerivationArtifactErrorReason::ClauseSequenceHashMismatch
    );
}

#[test]
fn authenticated_source_cannot_restart_a_refused_budget_during_rebuild() {
    let (problem, derivation) = super::super::tests::fixture();
    let envelope = envelope_for_derivation(&problem, &derivation).unwrap();
    let identity = AuthenticatedSource::check(
        &problem,
        &envelope.normalized_input_schema,
        &envelope.normalized_input_sha256,
        &envelope.source_clause_sequence_sha256,
        "artifact",
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap();
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        calls != 1
    };
    let mut control = GroundValidationControl::new(&mut progress);
    assert!(control.poll().is_err());
    for _ in 0..2 {
        assert_eq!(
            identity
                .rebuild_v1(&derivation, &mut control)
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert_eq!(
            identity
                .rebuild_v2(&derivation, &mut control)
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
    }
    assert_eq!(calls, 1);
}

#[test]
fn a_relabelled_normalized_input_schema_does_not_authenticate() {
    // The authenticated hash covers the schema line, so a label naming the
    // other schema can only have been rewritten after hashing.
    let (problem, _) = super::super::tests::fixture();
    let rejected = AuthenticatedSource::check(
        &problem,
        crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
        &normalized_chc_input_sha256(&problem),
        &crate::proof_metadata::ordered_chc_clause_sequence_sha256(&problem),
        "artifact",
        &mut GroundValidationControl::new(&mut || true),
    )
    .err()
    .expect("a relabelled schema must not authenticate");
    assert_eq!(
        rejected.reason,
        ChcGroundDerivationArtifactErrorReason::SchemaMismatch
    );
}
