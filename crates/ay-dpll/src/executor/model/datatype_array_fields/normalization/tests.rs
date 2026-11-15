// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::Executor;

mod resources;

fn fixture() -> (Executor, Sort, ArraySort) {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype Row ((row (len (_ BitVec 64))
             (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))
         (declare-datatype Chain ((done) (next (tail Chain))))",
    )
    .expect("bounded nested datatype declarations parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("declarations elaborate");
    (
        executor,
        Sort::Uninterpreted("Outer".to_string()),
        ArraySort::new(Sort::bitvec(64), Sort::Uninterpreted("Row".to_string())),
    )
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), width)
}

fn array(default: ModelValue, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue { default, store }))
}

fn row(length: u64, default: u64, points: &[(u64, u64)]) -> ModelValue {
    ModelValue::Datatype {
        ctor: "row".to_string(),
        args: vec![
            bv(length, 64),
            array(
                bv(default, 8),
                points
                    .iter()
                    .map(|&(key, value)| (bv(key, 64), bv(value, 8)))
                    .collect(),
            ),
        ],
    }
}

fn outer(points: &[(u64, ModelValue)]) -> ModelValue {
    ModelValue::Datatype {
        ctor: "outer".to_string(),
        args: vec![array(
            row(0, 0, &[]),
            points
                .iter()
                .map(|(key, value)| (bv(*key, 64), value.clone()))
                .collect(),
        )],
    }
}

fn outer_array(value: &ModelValue) -> &ArrayValue {
    let ModelValue::Datatype { args, .. } = value else {
        panic!("outer constructor")
    };
    let ModelValue::Array(array) = &args[0] else {
        panic!("outer array field")
    };
    array
}

#[test]
fn nested_registered_fields_and_far_stores_are_typed_exactly() {
    let (executor, sort, array_sort) = fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let value = outer(&[(33, row(65, 7, &[(64, 9)]))]);
    assert!(typed_datatype_array_value(&value, &sort, &guard));
    assert!(typed_array_value(outer_array(&value), &array_sort, &guard));
    let mut budget = SemanticNormalizationBudget::new();
    let normalized = normalize_array_value(outer_array(&value), &mut budget).unwrap();
    assert!(normalized.matches_point(&bv(33, 64), &row(65, 7, &[(64, 9)]), &mut budget));
    assert!(normalized.matches_point(&bv(34, 64), &row(0, 0, &[]), &mut budget));
    assert!(!normalized.matches_point(&bv(33, 64), &row(0, 0, &[]), &mut budget));
}

#[test]
fn nested_shadowed_and_redundant_writes_have_one_extensional_identity() {
    let canonical = outer(&[(33, row(65, 7, &[(64, 9)]))]);
    let redundant = outer(&[
        (33, row(1, 1, &[])),
        (34, row(0, 0, &[(99, 0)])),
        (33, row(65, 7, &[(64, 8), (66, 7), (64, 9)])),
    ]);
    assert_ne!(
        dt_canonical_string(&canonical),
        dt_canonical_string(&redundant)
    );
    assert!(same_value(&canonical, &redundant));
    assert!(same_value(&redundant, &canonical));
    let mut budget = SemanticNormalizationBudget::new();
    let left = normalize_datatype_array_value(&canonical, &mut budget).unwrap();
    let right = normalize_datatype_array_value(&redundant, &mut budget).unwrap();
    let mut identities = HashSet::default();
    assert!(identities.insert(left));
    assert!(
        !identities.insert(right),
        "hashing shares normalized equality"
    );
}

#[test]
fn every_nested_semantic_mutation_remains_distinct() {
    let expected = outer(&[(33, row(65, 7, &[(64, 9)]))]);
    for changed in [
        outer(&[]),
        outer(&[(32, row(65, 7, &[(64, 9)]))]),
        outer(&[(33, row(66, 7, &[(64, 9)]))]),
        outer(&[(33, row(65, 8, &[(64, 9)]))]),
        outer(&[(33, row(65, 7, &[(63, 9)]))]),
        outer(&[(33, row(65, 7, &[(64, 8)]))]),
    ] {
        assert!(!same_value(&expected, &changed));
        assert!(!same_value(&changed, &expected));
    }
    let empty = outer(&[]);
    let newest_default = outer(&[(33, row(65, 7, &[(64, 9)])), (33, row(0, 0, &[]))]);
    assert!(same_value(&empty, &newest_default));
}

#[test]
fn nested_type_errors_and_opaque_fallbacks_fail_closed() {
    let (executor, sort, array_sort) = fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let wrong_row = |ctor: &str, args| ModelValue::Datatype {
        ctor: ctor.to_string(),
        args,
    };
    for cell in [
        wrong_row("foreign", vec![bv(65, 64), array(bv(7, 8), vec![])]),
        wrong_row("row", vec![bv(65, 64)]),
        wrong_row("row", vec![bv(65, 32), array(bv(7, 8), vec![])]),
        wrong_row("row", vec![bv(65, 64), array(bv(7, 16), vec![])]),
        ModelValue::Uninterpreted("@Row!0".to_string()),
    ] {
        let value = outer(&[(33, cell)]);
        assert!(!typed_datatype_array_value(&value, &sort, &guard));
        assert!(!typed_array_value(outer_array(&value), &array_sort, &guard));
    }
    for malformed in [
        ModelValue::BitVec {
            width: 0,
            value: BigInt::from(0),
        },
        ModelValue::BitVec {
            width: 8,
            value: BigInt::from(-1),
        },
        ModelValue::BitVec {
            width: 8,
            value: BigInt::from(256),
        },
        ModelValue::Real(BigRational::new_raw(BigInt::from(1), BigInt::from(0))),
        ModelValue::Uninterpreted("@Row!0".to_string()),
        ModelValue::Seq(vec![]),
    ] {
        // An unsupported/malformed older cell must be rejected even when
        // a later scalar write shadows it completely.
        let value = array(
            bv(0, 8),
            vec![(bv(1, 64), malformed), (bv(1, 64), bv(2, 8))],
        );
        assert!(
            normalize_datatype_array_value(&value, &mut SemanticNormalizationBudget::new())
                .is_none()
        );
    }
    let non_scalar_key = ArrayValue {
        default: row(0, 0, &[]),
        store: vec![(row(1, 0, &[]), row(2, 0, &[]))],
    };
    assert!(!typed_array_value(&non_scalar_key, &array_sort, &guard));
    assert!(
        normalize_array_value(&non_scalar_key, &mut SemanticNormalizationBudget::new()).is_none()
    );
    let empty_non_scalar_keys = ArraySort::new(Sort::Uninterpreted("Row".to_string()), Sort::Bool);
    assert!(!typed_array_value(
        &ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![]
        },
        &empty_non_scalar_keys,
        &guard
    ));
}

#[test]
fn accumulator_reconciles_nested_values_and_preserves_atomic_refusal() {
    let value = row(65, 7, &[(64, 9)]);
    let equivalent = row(65, 7, &[(64, 8), (66, 7), (64, 9)]);
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_interpretation(
        Some(row(0, 0, &[])),
        vec![
            (bv(33, 64), value.clone()),
            (bv(33, 64), row(1, 1, &[])), // newest-first input: this one is shadowed
        ]
    ));
    assert!(accumulator.merge_point(bv(33, 64), equivalent.clone()));
    assert!(accumulator
        .merge_interpretation(Some(row(0, 0, &[(99, 0)])), vec![(bv(33, 64), equivalent)]));
    assert!(!accumulator.merge_interpretation(
        Some(row(0, 0, &[])),
        vec![
            (bv(34, 64), value.clone()),
            (bv(33, 64), row(65, 7, &[(64, 8)])),
        ]
    ));
    let result = accumulator
        .finish(&Sort::Uninterpreted("Row".to_string()))
        .unwrap();
    let expected = array(row(0, 0, &[]), vec![(bv(33, 64), value)]);
    assert!(
        same_value(&result, &expected),
        "failed merge leaked no point 34"
    );
}

#[test]
fn accumulator_scalar_key_identity_is_semantic_without_reordering_output() {
    let half = ModelValue::Real(BigRational::new_raw(BigInt::from(1), BigInt::from(2)));
    let same_half = ModelValue::Real(BigRational::new_raw(BigInt::from(2), BigInt::from(4)));
    let cell = row(65, 7, &[(64, 9)]);
    let mut accumulator = ArrayAccumulator::default();
    assert!(
        accumulator.merge_interpretation(Some(row(0, 0, &[])), vec![(half.clone(), cell.clone())])
    );
    assert!(accumulator.merge_point(same_half.clone(), cell.clone()));
    assert_eq!(accumulator.points.len(), 1);
    assert!(!accumulator.merge_point(same_half, row(65, 7, &[(64, 8)])));
    let ModelValue::Array(value) = accumulator
        .finish(&Sort::Uninterpreted("Row".to_string()))
        .unwrap()
    else {
        panic!("one complete interpretation");
    };
    assert_eq!(value.store.len(), 1);
    assert_eq!(
        dt_canonical_string(&value.store[0].0),
        dt_canonical_string(&half)
    );
    assert!(same_value(&value.store[0].1, &cell));
}

#[test]
fn scalar_array_semantics_are_unchanged() {
    // Exhaust every two-point Boolean function and redundant history.
    for left in [false, true] {
        for right in [false, true] {
            let canonical = array(
                ModelValue::Bool(false),
                vec![
                    (ModelValue::Bool(false), ModelValue::Bool(left)),
                    (ModelValue::Bool(true), ModelValue::Bool(right)),
                ],
            );
            let history = array(
                ModelValue::Bool(false),
                vec![
                    (ModelValue::Bool(true), ModelValue::Bool(!right)),
                    (ModelValue::Bool(false), ModelValue::Bool(!left)),
                    (ModelValue::Bool(true), ModelValue::Bool(right)),
                    (ModelValue::Bool(false), ModelValue::Bool(left)),
                ],
            );
            assert!(same_value(&canonical, &history));
            let changed = array(
                ModelValue::Bool(false),
                vec![
                    (ModelValue::Bool(false), ModelValue::Bool(!left)),
                    (ModelValue::Bool(true), ModelValue::Bool(right)),
                ],
            );
            assert!(!same_value(&canonical, &changed));
        }
    }
}
