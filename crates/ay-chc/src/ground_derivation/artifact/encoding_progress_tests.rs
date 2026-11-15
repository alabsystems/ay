// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};

mod oracle;

fn counts(counts: ContentCounts) -> (usize, usize, usize, usize) {
    (
        counts.premise_edges,
        counts.bindings,
        counts.uf_observations,
        counts.value_nodes,
    )
}

fn every_refusal<T>(
    mut run: impl FnMut(&mut dyn FnMut() -> bool) -> Result<T, ChcGroundDerivationArtifactError>,
) -> T {
    let mut total = 0usize;
    let accepted = run(&mut || {
        total += 1;
        true
    })
    .ok()
    .expect("valid encoding");
    assert!(total > 1);
    for ordinal in 1..=total {
        let mut calls = 0usize;
        let failure = run(&mut || {
            calls += 1;
            calls != ordinal
        })
        .err()
        .expect("refusal");
        assert_eq!(
            failure.reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert_eq!(
            calls, ordinal,
            "no retry after refusal, including the final poll"
        );
    }
    assert!(run(&mut || true).is_ok(), "fresh retry remains independent");
    accepted
}

#[test]
fn v1_reencoding_refuses_every_callback_and_preserves_wire_counts() {
    let (problem, derivation) = super::tests::fixture();
    let (expected, expected_counts) =
        oracle::wire_steps_from_derivation(&problem, &derivation).unwrap();
    let (actual, actual_counts) = every_refusal(|progress| {
        wire_steps_from_derivation_with_control(
            &problem,
            &derivation,
            &mut GroundValidationControl::new(progress),
        )
    });
    assert_eq!(actual, expected);
    assert_eq!(counts(actual_counts), counts(expected_counts));
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap()
    );
}

#[test]
fn v2_reencoding_refuses_every_callback_including_observation_evaluation() {
    let (problem, derivation) = super::tests::uf_fixture();
    let (expected, expected_counts) =
        oracle::wire_steps_v2_from_derivation(&problem, &derivation).unwrap();
    let (actual, actual_counts) = every_refusal(|progress| {
        wire_steps_v2_from_derivation_with_control(
            &problem,
            &derivation,
            &mut GroundValidationControl::new(progress),
        )
    });
    assert_eq!(actual, expected);
    assert_eq!(counts(actual_counts), counts(expected_counts));
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap()
    );
}

fn values() -> Vec<(SmtValue, ChcSort)> {
    vec![
        (SmtValue::Bool(true), ChcSort::Bool),
        (SmtValue::Int(i128::MIN), ChcSort::Int),
        (
            SmtValue::int_from_bigint(BigInt::from(1u8) << 160usize),
            ChcSort::Int,
        ),
        (
            SmtValue::Real(BigRational::new(BigInt::from(-3), BigInt::from(7))),
            ChcSort::Real,
        ),
        (
            SmtValue::bitvec_from_biguint(BigUint::from(1u8) << 128usize, 129),
            ChcSort::BitVec(129),
        ),
        (
            SmtValue::ConstArray(Box::new(SmtValue::Bool(false))),
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        ),
        (
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::Int(0)),
                // Duplicate indices remain positional rather than being normalized here.
                entries: vec![
                    (SmtValue::Bool(true), SmtValue::Int(2)),
                    (SmtValue::Bool(true), SmtValue::Int(3)),
                ],
            },
            ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Int)),
        ),
    ]
}

#[test]
fn recursive_value_spelling_and_counts_match_frozen_encoder() {
    for (value, sort) in values() {
        let mut expected_nodes = 0;
        let expected = oracle::encode_value(&value, &sort, 1, &mut expected_nodes).unwrap();
        let (actual, nodes) = every_refusal(|progress| {
            let mut nodes = 0;
            let encoded = encode_value_with_control(
                &value,
                &sort,
                1,
                &mut nodes,
                &mut GroundValidationControl::new(progress),
            )?;
            Ok((encoded, nodes))
        });
        assert_eq!(actual, expected);
        assert_eq!(nodes, expected_nodes);
    }
}

#[test]
fn datatype_constructor_scan_and_fields_are_cancellable() {
    let sort = ChcSort::Datatype {
        name: "Choice".to_string(),
        constructors: crate::ChcDtConstructors::new(
            (0..16)
                .map(|index| ChcDtConstructor {
                    name: format!("c{index}"),
                    selectors: vec![ChcDtSelector {
                        name: "field".to_string(),
                        sort: ChcSort::Int,
                    }],
                })
                .collect(),
        ),
    };
    let value = SmtValue::Datatype("c15".to_string(), vec![SmtValue::Int(9)]);
    let mut expected_nodes = 0;
    let expected = oracle::encode_value(&value, &sort, 1, &mut expected_nodes).unwrap();
    let actual = every_refusal(|progress| {
        encode_value_with_control(
            &value,
            &sort,
            1,
            &mut 0,
            &mut GroundValidationControl::new(progress),
        )
    });
    assert_eq!(actual, expected);
    assert_eq!(expected_nodes, 2);
}

#[test]
fn malformed_values_retain_exact_reason_detail_and_count() {
    for (value, sort, depth) in [
        (SmtValue::Opaque("unknown".to_string()), ChcSort::Int, 1),
        (SmtValue::Bool(true), ChcSort::Int, 1),
        (SmtValue::BitVec(0, 0), ChcSort::BitVec(0), 1),
        (
            SmtValue::Int(1),
            ChcSort::Int,
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH + 1,
        ),
    ] {
        let mut expected_nodes = 0;
        let expected = oracle::encode_value(&value, &sort, depth, &mut expected_nodes);
        let mut actual_nodes = 0;
        let actual = encode_value_with_control(
            &value,
            &sort,
            depth,
            &mut actual_nodes,
            &mut GroundValidationControl::new(&mut || true),
        );
        assert!(expected.is_err());
        assert_eq!(actual, expected);
        assert_eq!(actual_nodes, expected_nodes);
        let mut cancelled_nodes = 0;
        assert_eq!(
            encode_value_with_control(
                &value,
                &sort,
                depth,
                &mut cancelled_nodes,
                &mut GroundValidationControl::new(&mut || false)
            )
            .unwrap_err()
            .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert_eq!(cancelled_nodes, 0);
    }
}

#[test]
fn malformed_rows_preserve_legacy_errors_but_pre_cancel_is_terminal() {
    let (problem, mut derivation) = super::tests::fixture();
    derivation.steps[0].env.clear();
    assert_eq!(
        wire_steps_from_derivation(&problem, &derivation).unwrap_err(),
        oracle::wire_steps_from_derivation(&problem, &derivation).unwrap_err()
    );
    assert_eq!(
        wire_steps_v2_from_derivation(&problem, &derivation).unwrap_err(),
        oracle::wire_steps_v2_from_derivation(&problem, &derivation).unwrap_err()
    );
    assert_eq!(
        wire_steps_from_derivation_with_control(
            &problem,
            &derivation,
            &mut GroundValidationControl::new(&mut || false)
        )
        .unwrap_err()
        .reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
    assert_eq!(
        wire_steps_v2_from_derivation_with_control(
            &problem,
            &derivation,
            &mut GroundValidationControl::new(&mut || false)
        )
        .unwrap_err()
        .reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
}

#[test]
fn encoder_control_refusal_cannot_resume_on_a_second_value() {
    let mut calls = 0usize;
    let mut progress = || {
        calls += 1;
        calls > 1
    };
    let mut control = GroundValidationControl::new(&mut progress);
    for _ in 0..2 {
        assert_eq!(
            encode_value_with_control(&SmtValue::Int(1), &ChcSort::Int, 1, &mut 0, &mut control)
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
    }
    assert_eq!(calls, 1);
}
