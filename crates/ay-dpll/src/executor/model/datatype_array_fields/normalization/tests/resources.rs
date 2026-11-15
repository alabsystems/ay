// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn chain(depth: usize) -> ModelValue {
    let mut value = ModelValue::Datatype {
        ctor: "done".to_string(),
        args: vec![],
    };
    for _ in 0..depth {
        value = ModelValue::Datatype {
            ctor: "next".to_string(),
            args: vec![value],
        };
    }
    value
}

#[test]
fn aggregate_depth_is_shared_across_datatypes_and_arrays() {
    let (executor, _, _) = fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let sort = Sort::Uninterpreted("Chain".to_string());
    let exact = chain(MAX_RENDERED_DT_DEPTH);
    let too_deep = chain(MAX_RENDERED_DT_DEPTH + 1);
    assert!(typed_datatype_array_value(&exact, &sort, &guard));
    assert!(!typed_datatype_array_value(&too_deep, &sort, &guard));
    assert!(
        normalize_datatype_array_value(&exact, &mut SemanticNormalizationBudget::new()).is_some()
    );
    assert!(
        normalize_datatype_array_value(&too_deep, &mut SemanticNormalizationBudget::new())
            .is_none()
    );
    let array_sort = ArraySort::new(Sort::Int, sort);
    for (depth, accepted) in [
        (MAX_RENDERED_DT_DEPTH - 1, true),
        (MAX_RENDERED_DT_DEPTH, false),
    ] {
        let value = ArrayValue {
            default: chain(depth),
            store: vec![],
        };
        assert_eq!(typed_array_value(&value, &array_sort, &guard), accepted);
        assert_eq!(
            normalize_array_value(&value, &mut SemanticNormalizationBudget::new()).is_some(),
            accepted
        );
    }
}

#[test]
fn node_and_payload_limits_count_all_siblings_before_normalization() {
    let (executor, _, _) = fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let sort = ArraySort::new(Sort::Bool, Sort::Bool);
    let mut value = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![
            (ModelValue::Bool(false), ModelValue::Bool(true));
            (MAX_RENDERED_DT_NODES - 2) / 2
        ],
    };
    assert!(typed_array_value(&value, &sort, &guard));
    assert!(normalize_array_value(&value, &mut SemanticNormalizationBudget::new()).is_some());
    value
        .store
        .push((ModelValue::Bool(false), ModelValue::Bool(true)));
    assert!(!typed_array_value(&value, &sort, &guard));
    assert!(normalize_array_value(&value, &mut SemanticNormalizationBudget::new()).is_none());
    // Each child individually fits; the shared array root plus siblings do not.
    let siblings = ArrayValue {
        default: chain(16),
        store: (0..60)
            .map(|key| (ModelValue::Int(BigInt::from(key)), chain(16)))
            .collect(),
    };
    assert!(model_value_work(&siblings.default).is_some());
    assert!(normalize_array_value(&siblings, &mut SemanticNormalizationBudget::new()).is_none());
    for (length, accepted) in [
        (MAX_RENDERED_DT_BYTES - 1, true),
        (MAX_RENDERED_DT_BYTES, false),
    ] {
        let value = ArrayValue {
            default: ModelValue::Str("x".repeat(length)),
            store: vec![],
        };
        assert_eq!(
            normalize_array_value(&value, &mut SemanticNormalizationBudget::new()).is_some(),
            accepted
        );
    }
}

#[test]
fn normalization_and_point_queries_share_the_exact_remaining_work() {
    let value = outer(&[(33, row(65, 7, &[(64, 9)]))]);
    let cost = model_value_work(&value).unwrap();
    assert_eq!(aggregate_work(AggregateRoot::Value(&value)), Some(cost));
    let mut exact = SemanticNormalizationBudget::new();
    assert!(exact.charge(MAX_SEMANTIC_NORMALIZATION_WORK - cost));
    assert!(normalize_datatype_array_value(&value, &mut exact).is_some());
    assert_eq!(exact.work, MAX_SEMANTIC_NORMALIZATION_WORK);
    assert!(normalize_datatype_array_value(&value, &mut exact).is_none());
    let mut short = SemanticNormalizationBudget::new();
    assert!(short.charge(MAX_SEMANTIC_NORMALIZATION_WORK - cost + 1));
    assert!(normalize_datatype_array_value(&value, &mut short).is_none());
    assert!(!short.charge(usize::MAX));
    let mut budget = SemanticNormalizationBudget::new();
    let normalized = normalize_array_value(outer_array(&value), &mut budget).unwrap();
    let key = bv(33, 64);
    let cell = row(65, 7, &[(64, 9)]);
    let point_cost = model_value_work(&key).unwrap() + model_value_work(&cell).unwrap();
    assert!(budget.charge(MAX_SEMANTIC_NORMALIZATION_WORK - budget.work - point_cost));
    assert!(normalized.matches_point(&key, &cell, &mut budget));
    assert_eq!(budget.work, MAX_SEMANTIC_NORMALIZATION_WORK);
    assert!(!normalized.matches_point(&key, &cell, &mut budget));
}

#[test]
fn accumulator_budget_does_not_reset_between_nested_observations() {
    let key = bv(33, 64);
    let cell = row(65, 7, &[(64, 9)]);
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_point(key.clone(), cell.clone()));
    let cost = model_value_work(&key).unwrap() + 2 * model_value_work(&cell).unwrap();
    assert!(accumulator
        .work
        .charge(MAX_SEMANTIC_NORMALIZATION_WORK - accumulator.work.work - cost));
    assert!(accumulator.merge_point(key.clone(), cell.clone()));
    assert_eq!(accumulator.work.work, MAX_SEMANTIC_NORMALIZATION_WORK);
    assert!(!accumulator.merge_point(key.clone(), cell.clone()));
    assert_eq!(accumulator.points.len(), 1);
    assert!(same_value(
        &accumulator.points.values().next().unwrap().1,
        &cell
    ));
    assert!(
        ArrayAccumulator::default().merge_point(key, cell),
        "only a new owner has a fresh budget"
    );
}
