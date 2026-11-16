// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{
    encode_qf_invariant_model_artifact, parse_qf_invariant_model_artifact,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT, CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA,
};
use super::*;
use crate::{ChcProblem, ChcSort, InvariantModel};
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use ay_core::resource::CheckStop;
use ay_core::time::Instant;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

mod resources;

fn envelope(text: &str) -> Vec<u8> {
    let value = QfInvariantModelEnvelope {
        schema: CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA.into(),
        schema_version: 1,
        role: CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE.into(),
        model_format: CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT.into(),
        normalized_input_sha256: "0".repeat(64),
        predicate_count: 1,
        model_sha256: "1".repeat(64),
        model_smtlib: text.into(),
    };
    serde_json::to_vec(&value).unwrap()
}
fn owner(work: u64, bytes: usize, stop: CheckStop) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        Instant::now() + Duration::from_secs(20),
        stop,
    )
}
fn quiet_owner() -> OriginalAdmission {
    owner(1_000_000, 1_000_000, Arc::new(|| false))
}
fn consume(original: &OriginalAdmission, bytes: &[u8]) -> Result<(), OriginalAdmissionError> {
    original.with_work(|work| {
        prepare_qf_invariant_envelope_with_work(bytes, work)
            .map_err(QfEnvelopePreparationError::query_error)?
            .with_envelope(|_, _| Ok(()))
    })
}
fn totals(bytes: &[u8]) -> (u64, usize) {
    let (mut work_total, mut byte_total) = (0u64, 0usize);
    {
        let mut admission = |work, bytes| {
            work_total += work as u64;
            byte_total += bytes;
            Ok(())
        };
        let mut work = WorkBudget::with_admission(u64::MAX, &mut admission);
        prepare_qf_invariant_envelope_with_work(bytes, &mut work)
            .unwrap()
            .with_envelope(|_, _| Ok(()))
            .unwrap();
    }
    (work_total, byte_total)
}

// The exact pre-change envelope portion, independent of the new shared decoder.
fn reference_refusal(bytes: &[u8]) -> Option<QfEnvelopePreparationError> {
    let envelope: QfInvariantModelEnvelope = match serde_json::from_slice(bytes) {
        Ok(value) => value,
        Err(_) => return Some(QfEnvelopePreparationError::Malformed),
    };
    let canonical = serde_json::to_vec(&envelope).unwrap();
    (canonical != bytes).then_some(QfEnvelopePreparationError::NonCanonical)
}
fn check_legacy_refusal(bytes: &[u8], expected: QfEnvelopePreparationError) {
    use super::super::ChcQfInvariantModelArtifactErrorReason as Reason;
    assert_eq!(reference_refusal(bytes), Some(expected));
    let error = parse_qf_invariant_model_artifact(&ChcProblem::new(), bytes).unwrap_err();
    let reason = match expected {
        QfEnvelopePreparationError::Malformed => Reason::MalformedEnvelope,
        QfEnvelopePreparationError::NonCanonical => Reason::NonCanonicalEnvelope,
        _ => panic!("not a lexical envelope fixture"),
    };
    assert_eq!(error.reason, reason);
}

#[test]
fn real_scalar_artifact_legacy_and_prepared_envelope_share_success() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (>= x 0))", &problem).unwrap();
    let bytes = encode_qf_invariant_model_artifact(&problem, &model).unwrap();
    let parsed = parse_qf_invariant_model_artifact(&problem, bytes.bytes()).unwrap();
    let expected = parsed.to_smtlib(&problem);
    let original = quiet_owner();
    original
        .with_work(|work| {
            prepare_qf_invariant_envelope_with_work(bytes.bytes(), work)
                .map_err(QfEnvelopePreparationError::query_error)?
                .with_envelope(|view, work| {
                    assert_eq!(view.model_smtlib, expected);
                    assert_eq!(view.predicate_count, 1);
                    assert_eq!(view.schema, CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA);
                    work.charge(0)
                })
        })
        .unwrap();
}

#[test]
fn canonical_unicode_controls_and_surrogate_scalar_match_serde() {
    let ascii: String = (0u8..=127).map(char::from).collect();
    let texts = [
        "plain",
        "quote\" slash\\ control\n\t\r",
        "\u{0}\u{8}\u{c}\u{1f}",
        "λ😀",
        "|literal;()|",
        "",
        ascii.as_str(),
    ];
    let original = quiet_owner();
    for text in texts {
        let bytes = envelope(text);
        original
            .with_work(|work| {
                prepare_qf_invariant_envelope_with_work(&bytes, work)
                    .map_err(QfEnvelopePreparationError::query_error)?
                    .with_envelope(|view, _| {
                        assert_eq!(view.model_smtlib, text);
                        Ok(())
                    })
            })
            .unwrap();
    }
}

#[test]
fn duplicates_unknown_missing_and_wrong_field_types_refuse() {
    let valid = String::from_utf8(envelope("true")).unwrap();
    let attacks = [
        valid.replacen("{\"schema\":", "{\"schema\":\"x\",\"schema\":", 1),
        valid.replacen("{\"schema\":", "{\"unknown\":0,\"schema\":", 1),
        valid.replace(",\"predicate_count\":1", ""),
        valid.replace("\"schema_version\":1", "\"schema_version\":true"),
        valid.replace(
            "\"predicate_count\":1",
            "\"predicate_count\":18446744073709551616",
        ),
    ];
    for attack in attacks {
        check_legacy_refusal(attack.as_bytes(), QfEnvelopePreparationError::Malformed);
        let original = quiet_owner();
        let failure = original.with_work(|work| {
            match prepare_qf_invariant_envelope_with_work(attack.as_bytes(), work) {
                Err(error) => {
                    assert_eq!(error, QfEnvelopePreparationError::Malformed);
                    Err(error.query_error())
                }
                Ok(value) => value.with_envelope(|_, _| panic!("malformed envelope admitted")),
            }
        });
        assert!(failure.is_err());
        assert!(original.check().is_err());
    }
}

#[test]
fn valid_json_noncanonical_spacing_order_and_escape_refuse() {
    let valid = String::from_utf8(envelope("a/😀")).unwrap();
    let attacks = [
        format!(" {valid}"),
        format!("{valid}\n"),
        valid.replace("\"schema_version\":1", "\"schema_version\": 1"),
        valid.replace(
            &format!("\"schema_version\":1,\"role\":\"{CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE}\""),
            &format!("\"role\":\"{CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE}\",\"schema_version\":1"),
        ),
        valid.replace("a/😀", "a\\/😀"),
        valid.replace("😀", "\\ud83d\\ude00"),
    ];
    for (index, attack) in attacks.into_iter().enumerate() {
        check_legacy_refusal(attack.as_bytes(), QfEnvelopePreparationError::NonCanonical);
        let error = decode(attack.as_bytes(), &mut Legacy).err().unwrap();
        assert_eq!(
            error,
            QfEnvelopePreparationError::NonCanonical,
            "attack {index}"
        );
    }
}

#[test]
fn malformed_utf8_escape_surrogate_and_trailing_payload_refuse() {
    let valid = String::from_utf8(envelope("text")).unwrap();
    for attack in [
        valid.replace("text", "\\uD800"),
        valid.replace("text", "\\uDC00"),
        valid.replace("text", "\\uD800\\u0000"),
        valid.replace("text", "\\q"),
        format!("{valid}false"),
    ] {
        check_legacy_refusal(attack.as_bytes(), QfEnvelopePreparationError::Malformed);
        assert_eq!(
            decode(attack.as_bytes(), &mut Legacy).err().unwrap(),
            QfEnvelopePreparationError::Malformed
        );
    }
    let mut invalid = envelope("text");
    let at = invalid.iter().position(|byte| *byte == b't').unwrap();
    invalid[at] = 0xff;
    check_legacy_refusal(&invalid, QfEnvelopePreparationError::Malformed);
    assert_eq!(
        decode(&invalid, &mut Legacy).err().unwrap(),
        QfEnvelopePreparationError::Malformed
    );
}

#[test]
fn preparation_does_not_discharge_foreign_problem_missing_predicate_or_model() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("Inv", vec![ChcSort::Int]);
    problem.declare_predicate("Aux", vec![ChcSort::Bool]);
    let model = InvariantModel::parse_smtlib(
        "(define-fun Inv ((x Int)) Bool (>= x 0)) (define-fun Aux ((b Bool)) Bool b)",
        &problem,
    )
    .unwrap();
    let artifact = encode_qf_invariant_model_artifact(&problem, &model).unwrap();
    let mut foreign = ChcProblem::new();
    foreign.declare_predicate("Inv", vec![ChcSort::Bool]);
    foreign.declare_predicate("Aux", vec![ChcSort::Bool]);
    consume(&quiet_owner(), artifact.bytes()).unwrap();
    assert!(parse_qf_invariant_model_artifact(&foreign, artifact.bytes()).is_err());
    // Canonical envelope fields alone do not authenticate the hashes or model grammar.
    consume(&quiet_owner(), &envelope("not a model")).unwrap();
    assert!(parse_qf_invariant_model_artifact(&problem, &envelope("not a model")).is_err());
    let mut missing: QfInvariantModelEnvelope = serde_json::from_slice(artifact.bytes()).unwrap();
    missing.model_smtlib = missing
        .model_smtlib
        .split("(define-fun Aux")
        .next()
        .unwrap()
        .to_owned();
    missing.predicate_count = 1;
    missing.model_sha256 = super::super::sha256_hex(missing.model_smtlib.as_bytes());
    let bytes = serde_json::to_vec(&missing).unwrap();
    consume(&quiet_owner(), &bytes).unwrap();
    let error = parse_qf_invariant_model_artifact(&problem, &bytes).unwrap_err();
    assert_eq!(
        error.reason,
        super::super::ChcQfInvariantModelArtifactErrorReason::MissingPredicate
    );
}

#[test]
fn canonical_comparison_uses_no_second_envelope_buffer() {
    let bytes = envelope("large\n".repeat(100).as_str());
    let (_, charged) = totals(&bytes);
    let value: QfInvariantModelEnvelope = serde_json::from_slice(&bytes).unwrap();
    let fields = [
        &value.schema,
        &value.role,
        &value.model_format,
        &value.normalized_input_sha256,
        &value.model_sha256,
        &value.model_smtlib,
    ];
    let keys = [
        "schema",
        "schema_version",
        "role",
        "model_format",
        "normalized_input_sha256",
        "predicate_count",
        "model_sha256",
        "model_smtlib",
    ];
    let expected = fields.iter().map(|field| field.len()).sum::<usize>()
        + keys.iter().map(|key| key.len()).sum::<usize>();
    assert_eq!(charged, expected);
}

#[test]
fn public_unit_callback_retains_same_ledger_debits() {
    let bytes = envelope("true");
    let (base, storage) = totals(&bytes);
    let original = owner(base + 17, storage, Arc::new(|| false));
    original
        .with_work(|work| {
            prepare_qf_invariant_envelope_with_work(&bytes, work)
                .map_err(QfEnvelopePreparationError::query_error)?
                .with_envelope(|_, work| work.charge(17))
        })
        .unwrap();
    assert!(consume(&original, &bytes).is_err());
    assert!(original.check().is_err());
}
