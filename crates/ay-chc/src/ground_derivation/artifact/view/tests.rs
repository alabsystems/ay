// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;

use super::super::{
    encode_ground_derivation_artifact, encode_ground_derivation_artifact_v2,
    tests::{fixture, uf_fixture},
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_v2,
    ChcValidatedGroundDerivation,
};
use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, SmtValue,
};

fn validated_both(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> [ChcValidatedGroundDerivation; 2] {
    let v1 = encode_ground_derivation_artifact(problem, derivation).expect("valid v1 fixture");
    let v2 = encode_ground_derivation_artifact_v2(problem, derivation).expect("valid v2 fixture");
    [
        validate_chc_ground_derivation_artifact(problem, v1.bytes()).expect("v1 replay"),
        validate_chc_ground_derivation_artifact_v2(problem, v2.bytes()).expect("v2 replay"),
    ]
}

fn value_fixture(sort: ChcSort, value: &SmtValue) -> (ChcProblem, GroundDerivation) {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![sort.clone()]);
    let input = ChcExpr::var(ChcVar::new("input", sort.clone()));
    let output = ChcExpr::var(ChcVar::new("output", sort));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(predicate, vec![input]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        predicate,
        vec![output],
    )])));
    let steps = ["input", "output"]
        .into_iter()
        .enumerate()
        .map(|(clause_index, name)| GroundDerivationStep {
            clause_index,
            env: [(name.to_string(), value.clone())].into_iter().collect(),
            premises: if clause_index == 0 { vec![] } else { vec![0] },
        })
        .collect();
    (
        problem,
        GroundDerivation {
            steps,
            query_step: 1,
        },
    )
}

#[test]
fn multistep_views_borrow_exact_snapshot_storage() {
    let (problem, derivation) = fixture();
    for validated in validated_both(&problem, &derivation) {
        let mut steps = validated.steps();
        assert_eq!(steps.len(), validated.step_count());
        for index in 0..3 {
            let view = steps.next().expect("validated step");
            assert_eq!(steps.len(), 2 - index);
            assert_eq!(view.clause_index(), index);
            let raw = &validated.derivation().steps[index];
            assert_eq!(view.premises(), raw.premises);
            assert!(std::ptr::eq(view.premises(), raw.premises.as_slice()));
            let bindings: Vec<_> = view.source_bindings().collect();
            assert_eq!(bindings.len(), raw.env.len());
            for (name, value) in bindings {
                assert!(std::ptr::eq(
                    value,
                    raw.env.get(name).expect("source binding")
                ));
                assert!(std::ptr::eq(value, view.source_binding(name).unwrap()));
            }
            assert!(view.source_binding("missing").is_none());
            assert!(view.source_binding("\0private").is_none());
        }
        assert!(steps.next().is_none());
        assert_eq!(steps.len(), 0);
        assert!(validated.step(3).is_none());
        assert!(validated.step(usize::MAX).is_none());
        // Accessor lifetimes follow the snapshot, not the temporary view.
        let borrowed = validated.step(0).unwrap().source_binding("x").unwrap();
        let premises = validated.step(2).unwrap().premises();
        let bindings = validated.step(1).unwrap().source_bindings();
        assert_eq!(borrowed, &SmtValue::Int(0));
        assert_eq!(premises, &[1]);
        assert_eq!(bindings.count(), 2);
    }
}

#[test]
fn premise_order_duplicates_and_original_clause_indices_are_preserved() {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![ChcSort::Int]);
    for value in [0, 1] {
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(predicate, vec![ChcExpr::int(value)]),
        ));
    }
    let body = [1, 0, 1].map(|value| (predicate, vec![ChcExpr::int(value)]));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(
        body.to_vec(),
    )));
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 1,
                env: Default::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 0,
                env: Default::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 2,
                env: Default::default(),
                premises: vec![0, 1, 0],
            },
        ],
        query_step: 2,
    };
    for validated in validated_both(&problem, &derivation) {
        assert_eq!(
            validated
                .steps()
                .map(|step| step.clause_index())
                .collect::<Vec<_>>(),
            vec![1, 0, 2]
        );
        assert_eq!(validated.step(2).unwrap().premises(), &[0, 1, 0]);
        assert!(validated
            .steps()
            .all(|step| step.source_bindings().next().is_none()));
        assert_eq!(validated.premise_edge_count(), 3);
    }
}

#[test]
fn exact_scalar_variants_and_high_bits_survive_playback() {
    let cases = [
        (ChcSort::Bool, SmtValue::Bool(true)),
        (ChcSort::Int, SmtValue::Int(-42)),
        (
            ChcSort::Int,
            SmtValue::int_from_bigint(BigInt::from(i128::MAX) + 123),
        ),
        (
            ChcSort::Int,
            SmtValue::int_from_bigint(BigInt::from(i128::MIN) - 123),
        ),
        (
            ChcSort::Real,
            SmtValue::Real(BigRational::new(BigInt::from(-7), BigInt::from(11))),
        ),
        (ChcSort::BitVec(5), SmtValue::BitVec(31, 5)),
        (
            ChcSort::BitVec(129),
            SmtValue::try_bitvec_from_biguint((BigUint::from(1_u8) << 128_u32) + 3_u8, 129)
                .unwrap(),
        ),
        (
            ChcSort::BitVec(255),
            SmtValue::try_bitvec_from_biguint(BigUint::from(0_u8), 255).unwrap(),
        ),
    ];
    for (sort, value) in cases {
        let (problem, derivation) = value_fixture(sort, &value);
        for validated in validated_both(&problem, &derivation) {
            for (index, name) in ["input", "output"].into_iter().enumerate() {
                let view = validated.step(index).unwrap();
                assert_eq!(view.source_binding(name), Some(&value));
                assert_eq!(
                    view.source_bindings().collect::<Vec<_>>(),
                    vec![(name, &value)]
                );
            }
        }
    }
}

fn nested_array_fixture() -> (ChcSort, SmtValue) {
    let samples_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Real));
    let record_sort = ChcSort::Datatype {
        name: "Record".to_string(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "record".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "flag".to_string(),
                    sort: ChcSort::Bool,
                },
                ChcDtSelector {
                    name: "samples".to_string(),
                    sort: samples_sort,
                },
            ],
        }]),
    };
    let rational = |value| SmtValue::Real(BigRational::from_integer(BigInt::from(value)));
    let first = SmtValue::Datatype(
        "record".to_string(),
        vec![
            SmtValue::Bool(false),
            SmtValue::ConstArray(Box::new(rational(0))),
        ],
    );
    let second = SmtValue::Datatype(
        "record".to_string(),
        vec![
            SmtValue::Bool(true),
            SmtValue::ArrayMap {
                default: Box::new(rational(0)),
                entries: vec![
                    (SmtValue::Int(1), rational(3)),
                    (SmtValue::Int(1), rational(7)),
                ],
            },
        ],
    );
    let value = SmtValue::ArrayMap {
        default: Box::new(first.clone()),
        entries: vec![
            (SmtValue::Int(9), first),
            (SmtValue::Int(-2), second.clone()),
            (SmtValue::Int(9), second),
        ],
    };
    (
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(record_sort)),
        value,
    )
}

#[test]
fn nested_datatypes_arrays_and_duplicate_entry_order_are_exact() {
    let (sort, value) = nested_array_fixture();
    let (problem, derivation) = value_fixture(sort, &value);
    for validated in validated_both(&problem, &derivation) {
        let borrowed = validated.step(0).unwrap().source_binding("input").unwrap();
        assert_eq!(borrowed, &value);
        let SmtValue::ArrayMap { entries, .. } = borrowed else {
            panic!("array map preserved");
        };
        assert_eq!(
            entries.iter().map(|(key, _)| key).collect::<Vec<_>>(),
            vec![&SmtValue::Int(9), &SmtValue::Int(-2), &SmtValue::Int(9)]
        );
        let SmtValue::Datatype(_, fields) = &entries[2].1 else {
            panic!("datatype preserved");
        };
        let SmtValue::ArrayMap {
            entries: samples, ..
        } = &fields[1]
        else {
            panic!("nested map preserved");
        };
        assert_eq!(samples.len(), 2);
        assert_eq!(samples[0].0, samples[1].0);
        assert_ne!(samples[0].1, samples[1].1);
        assert!(std::ptr::eq(
            borrowed,
            validated.derivation().steps[0].env.get("input").unwrap()
        ));
    }
}

#[test]
fn constant_arrays_and_empty_maps_are_not_conflated() {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
    for value in [
        SmtValue::ConstArray(Box::new(SmtValue::Bool(false))),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Bool(false)),
            entries: vec![],
        },
    ] {
        let (problem, derivation) = value_fixture(sort.clone(), &value);
        for validated in validated_both(&problem, &derivation) {
            assert_eq!(
                validated.step(1).unwrap().source_binding("output"),
                Some(&value)
            );
        }
    }
}

#[test]
fn v2_private_uf_observations_and_markers_are_not_source_bindings() {
    let (problem, derivation) = uf_fixture();
    assert!(encode_ground_derivation_artifact(&problem, &derivation).is_err());
    let artifact = encode_ground_derivation_artifact_v2(&problem, &derivation).unwrap();
    let validated = validate_chc_ground_derivation_artifact_v2(&problem, artifact.bytes()).unwrap();
    assert_eq!(validated.uf_observation_count(), 2);
    for (index, view) in validated.steps().enumerate() {
        let raw = &validated.derivation().steps[index];
        let private_names: Vec<_> = raw
            .env
            .keys()
            .filter(|name| name.starts_with('\0'))
            .collect();
        assert!(
            !private_names.is_empty(),
            "fixture must exercise private metadata"
        );
        for name in private_names {
            assert!(view.source_binding(name).is_none());
        }
        let expected_name = if index == 0 { "x" } else { "y" };
        assert_eq!(
            view.source_bindings().collect::<Vec<_>>(),
            vec![(expected_name, &SmtValue::Int(0))]
        );
        assert_eq!(view.source_binding(expected_name), Some(&SmtValue::Int(0)));
        assert!(view
            .source_binding("\0ay.unrecognized-private-key")
            .is_none());
    }
}

#[test]
fn invalid_typed_binding_cannot_acquire_a_playback_snapshot() {
    let (problem, derivation) = value_fixture(ChcSort::Int, &SmtValue::Bool(true));
    assert!(encode_ground_derivation_artifact(&problem, &derivation).is_err());
    assert!(encode_ground_derivation_artifact_v2(&problem, &derivation).is_err());
}
