#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcVar};
use std::sync::Arc;

fn assert_every_refusal<T>(
    mut run: impl FnMut(&mut dyn FnMut() -> bool) -> Result<T, ChcGroundDerivationArtifactError>,
) -> T {
    let mut successful_polls = 0usize;
    let accepted = run(&mut || {
        successful_polls += 1;
        true
    })
    .unwrap_or_else(|error| panic!("valid decoding failed: {error}"));
    assert!(successful_polls > 1);
    for refusal in 1..=successful_polls {
        let mut polls = 0usize;
        let rejected = run(&mut || {
            polls += 1;
            polls != refusal
        })
        .err()
        .expect("every callback refusal must stop decoding");
        assert_eq!(
            rejected.reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted,
            "refusal {refusal}"
        );
        assert_eq!(polls, refusal, "no callback after the first refusal");
        assert!(run(&mut || true).is_ok(), "fresh retry after {refusal}");
    }
    accepted
}

fn count_tuple(counts: ContentCounts) -> (usize, usize, usize, usize) {
    (
        counts.premise_edges,
        counts.bindings,
        counts.uf_observations,
        counts.value_nodes,
    )
}

#[test]
fn controlled_v1_decoding_refuses_every_poll_and_retains_counts_and_steps() {
    let (problem, derivation) = super::tests::fixture();
    let (wire, encoded_counts) = wire_steps_from_derivation(&problem, &derivation).unwrap();
    let (decoded, counts) = assert_every_refusal(|progress| {
        derivation_from_wire_steps_with_control(
            &problem,
            &wire,
            2,
            &mut GroundValidationControl::new(progress),
        )
    });
    assert_eq!(count_tuple(counts), (2, 4, 0, 4));
    assert_eq!(count_tuple(counts), count_tuple(encoded_counts));
    assert_eq!(
        count_tuple(derivation_from_wire_steps(&problem, &wire, 2).unwrap().1),
        count_tuple(counts)
    );
    assert_eq!(decoded.query_step, 2);
    assert_eq!(
        wire_steps_from_derivation(&problem, &decoded).unwrap().0,
        wire
    );
    validate_ground_derivation(&problem, &decoded).unwrap();
}

#[test]
fn controlled_v2_decoding_refuses_every_poll_including_uf_evaluation() {
    let (problem, derivation) = super::tests::uf_fixture();
    let (wire, encoded_counts) = wire_steps_v2_from_derivation(&problem, &derivation).unwrap();
    let (decoded, counts) = assert_every_refusal(|progress| {
        derivation_from_wire_steps_v2_with_control(
            &problem,
            &wire,
            1,
            &mut GroundValidationControl::new(progress),
        )
    });
    assert_eq!(count_tuple(counts), (1, 2, 2, 4));
    assert_eq!(count_tuple(counts), count_tuple(encoded_counts));
    assert_eq!(
        count_tuple(derivation_from_wire_steps_v2(&problem, &wire, 1).unwrap().1),
        count_tuple(counts)
    );
    assert_eq!(decoded.query_step, 1);
    assert_eq!(
        wire_steps_v2_from_derivation(&problem, &decoded).unwrap().0,
        wire
    );
    validate_ground_derivation(&problem, &decoded).unwrap();
}

#[test]
fn controlled_numeric_text_scans_match_the_precontrol_grammar() {
    let cases = [
        "", "-", "+1", "0", "-0", "00", "01", "-01", "1", "-123", "9", "a", "f", "1af", "FF",
        "0x1", "1g", "1\n", "1\0", "９", "é",
    ];
    for value in cases {
        let decimal =
            canonical_decimal_with_control(value, &mut GroundValidationControl::new(&mut || true))
                .unwrap();
        let hexadecimal =
            canonical_hex_with_control(value, &mut GroundValidationControl::new(&mut || true))
                .unwrap();
        assert_eq!(decimal, canonical_decimal(value), "decimal {value:?}");
        assert_eq!(hexadecimal, canonical_hex(value), "hex {value:?}");
    }
    for value in ["1".repeat(8193), format!("{}x", "1".repeat(8192))] {
        let decimal = assert_every_refusal(|progress| {
            canonical_decimal_with_control(&value, &mut GroundValidationControl::new(progress))
        });
        let hexadecimal = assert_every_refusal(|progress| {
            canonical_hex_with_control(&value, &mut GroundValidationControl::new(progress))
        });
        assert_eq!(decimal, canonical_decimal(&value));
        assert_eq!(hexadecimal, canonical_hex(&value));
    }
}

fn typed_values() -> Vec<(ChcSort, SmtValue, usize)> {
    let pair = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: crate::ChcDtConstructors::new(vec![
            ChcDtConstructor {
                name: "empty".to_string(),
                selectors: Vec::new(),
            },
            ChcDtConstructor {
                name: "pair".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "number".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "flag".to_string(),
                        sort: ChcSort::Bool,
                    },
                ],
            },
        ]),
    };
    vec![
        (ChcSort::Bool, SmtValue::Bool(true), 1),
        (
            ChcSort::Int,
            SmtValue::int_from_bigint(BigInt::from(i128::MAX) + 1),
            1,
        ),
        (
            ChcSort::Real,
            SmtValue::Real(BigRational::new(BigInt::from(-7), BigInt::from(11))),
            1,
        ),
        (
            ChcSort::BitVec(129),
            SmtValue::bitvec_from_biguint((BigUint::from(1u8) << 128) + BigUint::from(3u8), 129),
            1,
        ),
        (
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
            SmtValue::ConstArray(Box::new(SmtValue::Bool(false))),
            2,
        ),
        (
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::Bool(false)),
                // Preserve raw order, duplicate keys and an explicit default-valued entry.
                entries: vec![
                    (SmtValue::Int(9), SmtValue::Bool(true)),
                    (SmtValue::Int(2), SmtValue::Bool(false)),
                    (SmtValue::Int(9), SmtValue::Bool(false)),
                ],
            },
            8,
        ),
        (
            pair,
            SmtValue::Datatype(
                "pair".to_string(),
                vec![SmtValue::Int(5), SmtValue::Bool(true)],
            ),
            3,
        ),
    ]
}

#[test]
fn controlled_recursive_values_preserve_raw_forms_and_work_counts() {
    for (sort, expected, expected_nodes) in typed_values() {
        let wire = encode_value(&expected, &sort, 1, &mut 0).unwrap();
        let occurrences = assert_every_refusal(|progress| {
            wire_value_typecheck_occurrences_with_control(
                &wire,
                &mut GroundValidationControl::new(progress),
            )
        });
        assert_eq!(occurrences, expected_nodes);
        let (decoded, nodes) = assert_every_refusal(|progress| {
            let mut nodes = 0;
            let value = decode_value_with_control(
                &wire,
                &sort,
                1,
                &mut nodes,
                &mut GroundValidationControl::new(progress),
            )?;
            Ok((value, nodes))
        });
        assert_eq!(decoded, expected);
        assert_eq!(nodes, expected_nodes);
        assert_eq!(encode_value(&decoded, &sort, 1, &mut 0).unwrap(), wire);
    }
}

#[test]
fn controlled_value_rejections_preserve_reason_and_precedence() {
    let cases = [
        (
            WireValue::Int {
                decimal: "-0".to_string(),
            },
            ChcSort::Int,
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            "integer value is not canonical decimal",
        ),
        (
            WireValue::Real {
                numerator: "2".to_string(),
                denominator: "4".to_string(),
            },
            ChcSort::Real,
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            "real value is not reduced canonical rational form",
        ),
        (
            WireValue::Real {
                numerator: "1".to_string(),
                denominator: "-2".to_string(),
            },
            ChcSort::Real,
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            "real denominator must be positive",
        ),
        (
            WireValue::Bitvector {
                width: 9,
                value_hex: "FF".to_string(),
            },
            ChcSort::BitVec(8),
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            "bitvector width 9 does not match source width 8",
        ),
        (
            WireValue::Bitvector {
                width: 8,
                value_hex: "100".to_string(),
            },
            ChcSort::BitVec(8),
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            "bitvector value has set bits outside its declared width",
        ),
    ];
    for (wire, sort, reason, detail) in cases {
        let error = decode_value_with_control(
            &wire,
            &sort,
            1,
            &mut 0,
            &mut GroundValidationControl::new(&mut || true),
        )
        .unwrap_err();
        assert_eq!(error.reason, reason);
        assert_eq!(error.detail, detail);
    }
}

#[test]
fn v1_and_v2_retain_different_private_binding_namespace_reasons() {
    let (problem, derivation) = super::tests::fixture();
    let (mut v1, _) = wire_steps_from_derivation(&problem, &derivation).unwrap();
    let (mut v2, _) = wire_steps_v2_from_derivation(&problem, &derivation).unwrap();
    v1[0].bindings[0].name = "\0private".to_string();
    v2[0].bindings[0].name = "\0private".to_string();
    let v1_error = derivation_from_wire_steps_with_control(
        &problem,
        &v1,
        2,
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap_err();
    let v2_error = derivation_from_wire_steps_v2_with_control(
        &problem,
        &v2,
        2,
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap_err();
    assert_eq!(
        v1_error.reason,
        ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
    );
    assert_eq!(
        v2_error.reason,
        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch
    );
    assert_eq!(
        v1_error.detail,
        "step 0 binding uses AY's private UF namespace"
    );
    assert_eq!(v2_error.detail, "step 0 binding uses a private namespace");
}

#[test]
fn controlled_v2_rejects_missing_wrong_ordinal_and_conflicting_uf_results() {
    let (problem, derivation) = super::tests::uf_fixture();
    let (wire, _) = wire_steps_v2_from_derivation(&problem, &derivation).unwrap();
    let mut missing = wire.clone();
    missing[0].uf_observations.clear();
    let mut wrong_ordinal = wire.clone();
    wrong_ordinal[0].uf_observations[0].application_ordinal = 1;
    // A later clause observes the same function at equal concrete arguments.
    let mut conflicting = wire;
    conflicting[1].uf_observations[0].result = WireValue::Int {
        decimal: "8".to_string(),
    };
    for (steps, reason) in [
        (
            missing,
            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch,
        ),
        (
            wrong_ordinal,
            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch,
        ),
        (
            conflicting,
            ChcGroundDerivationArtifactErrorReason::UfCongruenceViolation,
        ),
    ] {
        let error = derivation_from_wire_steps_v2_with_control(
            &problem,
            &steps,
            1,
            &mut GroundValidationControl::new(&mut || true),
        )
        .unwrap_err();
        assert_eq!(error.reason, reason);
    }
}

#[test]
fn uf_argument_interruption_stays_distinct_from_nonground_and_is_sticky() {
    let applications = vec![ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::Int)))],
    )];
    let results = vec![SmtValue::Int(7)];
    let error = install_authenticated_uf_observations_with_control(
        0,
        &applications,
        &results,
        &mut FxHashMap::default(),
        &mut FxHashMap::default(),
        &mut GroundValidationControl::new(&mut || true),
    )
    .unwrap_err();
    assert_eq!(
        error.reason,
        ChcGroundDerivationArtifactErrorReason::UfObservationNotGround
    );

    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        false
    };
    let mut control = GroundValidationControl::new(&mut progress);
    for _ in 0..2 {
        let interrupted = install_authenticated_uf_observations_with_control(
            0,
            &applications,
            &[],
            &mut FxHashMap::default(),
            &mut FxHashMap::default(),
            &mut control,
        )
        .unwrap_err();
        assert_eq!(
            interrupted.reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert!(control.is_stopped());
    }
    assert_eq!(calls, 1);
}
