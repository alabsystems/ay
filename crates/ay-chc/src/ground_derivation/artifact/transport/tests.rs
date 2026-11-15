// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::{
    encode_ground_derivation_artifact, encode_ground_derivation_artifact_v2,
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_v2,
    validate_chc_ground_derivation_artifact_v2_with_progress,
    validate_chc_ground_derivation_artifact_with_progress, ChcValidatedGroundDerivation,
    GroundDerivationEnvelope, GroundDerivationEnvelopeV2,
};
use super::*;

#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TextFixture {
    text: String,
    count: u64,
}

fn text_fixture() -> TextFixture {
    TextFixture {
        text: format!("{}\"\\\n\u{0000}é🦀", "x".repeat(2 * POLL_BYTES + 7)),
        count: u64::MAX,
    }
}

fn rejects_every_refusal<T: std::fmt::Debug>(
    mut run: impl FnMut(&mut dyn FnMut() -> bool) -> ArtifactResult<T>,
) {
    let mut calls = 0;
    run(&mut || {
        calls += 1;
        true
    })
    .expect("always-continue fixture must pass");
    assert!(calls > 2, "fixture must cross interior and final polls");
    for refused in 1..=calls {
        let mut observed = 0;
        let error = run(&mut || {
            observed += 1;
            observed != refused
        })
        .expect_err("every refusal must prevent success");
        assert_eq!(error.reason, Reason::Interrupted, "poll {refused}: {error}");
        assert_eq!(error.reason_code, "interrupted");
        assert_eq!(observed, refused, "a refusal must remain sticky");
    }
    run(&mut || true).expect("a fresh attempt must remain valid");
}

#[test]
fn transport_operations_refuse_at_every_callback_and_allow_retry() {
    let value = text_fixture();
    let bytes = serde_json::to_vec(&value).expect("fixture serializes");
    rejects_every_refusal(|progress| {
        validate_json_surface(&bytes, &mut GroundValidationControl::new(progress))
    });
    rejects_every_refusal(|progress| {
        parse_envelope::<TextFixture>(&bytes, &mut GroundValidationControl::new(progress))
    });
    rejects_every_refusal(|progress| {
        check_canonical_json(
            &value,
            &bytes,
            "test mismatch",
            &mut GroundValidationControl::new(progress),
        )
    });
    rejects_every_refusal(|progress| {
        sha256_hex(&bytes, &mut GroundValidationControl::new(progress))
    });
}

#[test]
fn canonical_json_and_digest_match_existing_serde_and_sha256() {
    let value = text_fixture();
    let bytes = serde_json::to_vec(&value).expect("fixture serializes");
    let decoded: TextFixture =
        parse_envelope(&bytes, &mut GroundValidationControl::new(&mut || true))
            .expect("controlled reader accepts canonical bytes");
    assert_eq!(decoded, value);
    check_canonical_json(
        &value,
        &bytes,
        "test mismatch",
        &mut GroundValidationControl::new(&mut || true),
    )
    .expect("controlled writer preserves serde's exact bytes");
    assert_eq!(
        sha256_hex(&bytes, &mut GroundValidationControl::new(&mut || true))
            .expect("digest succeeds"),
        super::super::sha256_hex(&bytes)
    );
}

#[test]
fn surface_scanner_preserves_legacy_limits_and_error_reasons() {
    let mut long_string = vec![b'"'];
    long_string.extend(vec![
        b'x';
        CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
            + 1
    ]);
    let cases = [
        Vec::new(),
        br#"{"text":"escaped\"quote\\\n","count":1}"#.to_vec(),
        b"malformed-but-surface-bounded".to_vec(),
        vec![b'['; CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH + 1],
        vec![b'9'; CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES + 1],
        long_string,
    ];
    for bytes in cases {
        assert_eq!(
            validate_json_surface(&bytes, &mut GroundValidationControl::new(&mut || true)),
            super::super::validate_json_surface(&bytes),
        );
    }
}

#[test]
fn malformed_unknown_duplicate_and_trailing_json_stay_malformed() {
    for bytes in [
        &b"{"[..],
        &br#"{"text":"x","count":1,"extra":true}"#[..],
        &br#"{"text":"x","text":"y","count":1}"#[..],
        &br#"{"text":"x","count":1} false"#[..],
        &br#"{"text":"x","count":18446744073709551616}"#[..],
    ] {
        assert!(serde_json::from_slice::<TextFixture>(bytes).is_err());
        let error =
            parse_envelope::<TextFixture>(bytes, &mut GroundValidationControl::new(&mut || true))
                .expect_err("malformed envelope must stay rejected");
        assert_eq!(error.reason, Reason::MalformedEnvelope);
    }
}

#[test]
fn changed_order_escaping_bytes_and_lengths_stay_noncanonical() {
    let value = TextFixture {
        text: "x".to_string(),
        count: 1,
    };
    let canonical = serde_json::to_vec(&value).expect("fixture serializes");
    let mut shorter = canonical.clone();
    shorter.pop();
    let mut longer = canonical.clone();
    longer.push(b' ');
    for expected in [
        br#"{"count":1,"text":"x"}"#.to_vec(),
        br#"{"text":"\u0078","count":1}"#.to_vec(),
        br#"{"text":"y","count":1}"#.to_vec(),
        shorter,
        longer,
    ] {
        assert_ne!(canonical, expected);
        let error = check_canonical_json(
            &value,
            &expected,
            "test mismatch",
            &mut GroundValidationControl::new(&mut || true),
        )
        .expect_err("changed canonical bytes must be rejected");
        assert_eq!(error.reason, Reason::NonCanonicalEnvelope);
        assert_eq!(error.detail, "test mismatch");
    }
}

#[test]
fn serialization_failure_remains_distinct_from_mismatch_and_refusal() {
    struct RefusesSerialization;
    impl Serialize for RefusesSerialization {
        fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("intentional serializer failure"))
        }
    }
    assert_eq!(
        check_canonical_json(
            &RefusesSerialization,
            b"{}",
            "test mismatch",
            &mut GroundValidationControl::new(&mut || true),
        )
        .expect_err("serialization failure must not become a short-output mismatch")
        .reason,
        Reason::SerializationFailed
    );
    assert_eq!(
        check_canonical_json(
            &RefusesSerialization,
            b"{}",
            "test mismatch",
            &mut GroundValidationControl::new(&mut || false),
        )
        .expect_err("entry refusal must precede serialization")
        .reason,
        Reason::Interrupted
    );
}

#[test]
fn sticky_io_refusal_is_not_retryable_or_reclassified() {
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        false
    };
    let mut control = GroundValidationControl::new(&mut progress);
    let mut reader = ProgressReader {
        bytes: b"{}",
        position: 0,
        until_poll: 0,
        control: &mut control,
    };
    let mut byte = [0];
    for _ in 0..2 {
        assert_eq!(
            reader
                .read(&mut byte)
                .expect_err("refused I/O must stop")
                .kind(),
            io::ErrorKind::Other
        );
    }
    drop(reader);
    assert!(control.is_stopped());
    assert_eq!(
        parse_envelope::<TextFixture>(b"invalid JSON", &mut control)
            .expect_err("sticky stop precedes malformed input")
            .reason,
        Reason::Interrupted
    );
    drop(control);
    assert_eq!(calls, 1);
}

fn same_validated_identity(lhs: &ChcValidatedGroundDerivation, rhs: &ChcValidatedGroundDerivation) {
    assert_eq!(lhs.artifact_schema(), rhs.artifact_schema());
    assert_eq!(lhs.artifact_role(), rhs.artifact_role());
    assert_eq!(lhs.artifact_sha256(), rhs.artifact_sha256());
    assert_eq!(lhs.artifact_bytes(), rhs.artifact_bytes());
    assert_eq!(lhs.normalized_input_sha256(), rhs.normalized_input_sha256());
    assert_eq!(
        lhs.source_clause_sequence_sha256(),
        rhs.source_clause_sequence_sha256()
    );
    assert_eq!(lhs.step_count(), rhs.step_count());
    assert_eq!(lhs.query_step(), rhs.query_step());
    assert_eq!(lhs.binding_count(), rhs.binding_count());
    assert_eq!(lhs.premise_edge_count(), rhs.premise_edge_count());
    assert_eq!(lhs.uf_observation_count(), rhs.uf_observation_count());
    assert_eq!(lhs.value_node_count(), rhs.value_node_count());
}

#[test]
fn public_v1_validator_refuses_every_callback_without_changing_evidence() {
    let (problem, derivation) = super::super::tests::fixture();
    let artifact =
        encode_ground_derivation_artifact(&problem, &derivation).expect("valid v1 fixture encodes");
    let legacy = validate_chc_ground_derivation_artifact(&problem, artifact.bytes())
        .expect("legacy validator accepts fixture");
    let controlled = validate_chc_ground_derivation_artifact_with_progress(
        &problem,
        artifact.bytes(),
        &mut || true,
    )
    .expect("controlled validator accepts fixture");
    same_validated_identity(&legacy, &controlled);
    rejects_every_refusal(|progress| {
        validate_chc_ground_derivation_artifact_with_progress(&problem, artifact.bytes(), progress)
    });
}

#[test]
fn public_v2_validator_refuses_every_callback_without_changing_uf_evidence() {
    let (problem, derivation) = super::super::tests::uf_fixture();
    let artifact = encode_ground_derivation_artifact_v2(&problem, &derivation)
        .expect("valid v2 UF fixture encodes");
    let legacy = validate_chc_ground_derivation_artifact_v2(&problem, artifact.bytes())
        .expect("legacy v2 validator accepts fixture");
    let controlled = validate_chc_ground_derivation_artifact_v2_with_progress(
        &problem,
        artifact.bytes(),
        &mut || true,
    )
    .expect("controlled v2 validator accepts fixture");
    same_validated_identity(&legacy, &controlled);
    assert_eq!(controlled.uf_observation_count(), 2);
    rejects_every_refusal(|progress| {
        validate_chc_ground_derivation_artifact_v2_with_progress(
            &problem,
            artifact.bytes(),
            progress,
        )
    });
}

#[test]
fn v1_and_v2_keep_transport_errors_before_schema_errors() {
    let (problem, derivation) = super::super::tests::fixture();
    let v1 = encode_ground_derivation_artifact(&problem, &derivation).expect("v1 fixture encodes");
    let mut envelope: GroundDerivationEnvelope =
        serde_json::from_slice(v1.bytes()).expect("fixture envelope parses");
    envelope.schema = "wrong-schema".to_string();
    let canonical = serde_json::to_vec(&envelope).expect("changed envelope serializes");
    assert_eq!(
        validate_chc_ground_derivation_artifact_with_progress(&problem, &canonical, &mut || true)
            .expect_err("canonical wrong schema must be rejected")
            .reason,
        Reason::SchemaMismatch
    );
    let noncanonical = serde_json::to_vec_pretty(&envelope).expect("pretty envelope serializes");
    assert_eq!(
        validate_chc_ground_derivation_artifact_with_progress(&problem, &noncanonical, &mut || {
            true
        })
        .expect_err("transport precedence must stay intact")
        .reason,
        Reason::NonCanonicalEnvelope
    );
    let v2 =
        encode_ground_derivation_artifact_v2(&problem, &derivation).expect("v2 fixture encodes");
    let mut envelope: GroundDerivationEnvelopeV2 =
        serde_json::from_slice(v2.bytes()).expect("v2 fixture envelope parses");
    envelope.schema = "wrong-schema".to_string();
    let canonical = serde_json::to_vec(&envelope).expect("changed v2 envelope serializes");
    assert_eq!(
        validate_chc_ground_derivation_artifact_v2_with_progress(&problem, &canonical, &mut || {
            true
        })
        .expect_err("canonical wrong v2 schema must be rejected")
        .reason,
        Reason::SchemaMismatch
    );
    let noncanonical = serde_json::to_vec_pretty(&envelope).expect("pretty v2 envelope serializes");
    assert_eq!(
        validate_chc_ground_derivation_artifact_v2_with_progress(
            &problem,
            &noncanonical,
            &mut || true
        )
        .expect_err("v2 transport precedence must stay intact")
        .reason,
        Reason::NonCanonicalEnvelope
    );
}
