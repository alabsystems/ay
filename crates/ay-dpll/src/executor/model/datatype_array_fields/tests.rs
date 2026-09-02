// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_model_check::ArrayValue;
use num_bigint::BigInt;

fn int(value: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(value))
}

fn array_field_parser_fixture() -> (Executor, Sort) {
    let commands = ay_frontend::parse(
        "(set-logic ALL)\
         (declare-datatype ArrayCell ((mk (field (Array Int Bool)))))",
    )
    .expect("array-field parser fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("array-field parser fixture executes");
    (executor, Sort::Uninterpreted("ArrayCell".to_string()))
}

#[test]
fn guarded_parser_reads_exact_array_valued_field() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    assert!(guard.is_exact_array_cell(&sort));
    assert!(!guard.is_exact(&sort), "authority stays concrete-read-only");

    let parsed = executor.parse_rendered_dt_value_cached(
        "(mk (store ((as const (Array Int Bool)) false) 3 true))",
        &sort,
        &guard,
    );
    assert!(matches!(
        parsed,
        Some(ModelValue::Datatype { ctor, args })
            if ctor == "mk"
                && matches!(
                    args.as_slice(),
                    [ModelValue::Array(array)]
                        if matches!(array.default, ModelValue::Bool(false))
                            && matches!(
                                array.store.as_slice(),
                                [(ModelValue::Int(key), ModelValue::Bool(true))]
                                    if key == &BigInt::from(3)
                            )
                )
    ));
}

#[test]
fn guarded_array_field_parser_rejects_malformed_value() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    assert!(executor
        .parse_rendered_dt_value_cached(
            "(mk (store ((as const (Array Int Bool)) false) 3))",
            &sort,
            &guard,
        )
        .is_none());
}

#[test]
fn guarded_array_field_parser_rejects_foreign_qualifier_sort() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    assert!(executor
        .parse_rendered_dt_value_cached("(mk ((as const (Array Bool Bool)) false))", &sort, &guard,)
        .is_none());
}

#[test]
fn guarded_array_field_parser_rejects_excessive_store_depth() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let mut array = "((as const (Array Int Bool)) false)".to_string();
    for key in 0..=MAX_TYPED_ARRAY_DEPTH {
        array = format!("(store {array} {key} true)");
    }
    assert!(executor
        .parse_rendered_dt_value_cached(&format!("(mk {array})"), &sort, &guard)
        .is_none());
}

#[test]
fn guarded_array_field_parser_rejects_oversized_text() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let payload = "0".repeat(super::super::rendered_dt_limits::MAX_RENDERED_DT_BYTES);
    let rendered = format!("(mk ((as const (Array Int Bool)) {payload}))");
    assert!(executor
        .parse_rendered_dt_value_cached(&rendered, &sort, &guard)
        .is_none());
}

#[test]
fn guarded_array_field_parser_rejects_excessive_nodes() {
    let (executor, sort) = array_field_parser_fixture();
    let guard = RenderedDatatypeGuard::new(&executor);
    let atoms = (0..=super::super::rendered_dt_limits::MAX_RENDERED_DT_NODES)
        .map(|_| "false")
        .collect::<Vec<_>>()
        .join(" ");
    let rendered = format!("(mk ((as const (Array Int Bool)) (and {atoms})))");
    assert!(executor
        .parse_rendered_dt_value_cached(&rendered, &sort, &guard)
        .is_none());
}

#[test]
fn direct_scalar_parser_enforces_cumulative_text_budget() {
    let chunk = format!(
        "|{}|",
        "x".repeat(super::super::rendered_dt_limits::MAX_RENDERED_DT_BYTES / 2)
    );
    let mut budget = TypedArrayParseBudget::new();
    for _ in 0..7 {
        assert!(budget.charge_text(&chunk));
    }
    assert!(!budget.charge_text(&chunk));
}

#[test]
fn direct_scalar_parser_rejects_oversized_text() {
    let (executor, _) = array_field_parser_fixture();
    let oversized = "1".repeat(super::super::rendered_dt_limits::MAX_RENDERED_DT_BYTES + 1);
    assert!(executor
        .typed_scalar_text(&oversized, &Sort::Int, &mut TypedArrayParseBudget::new())
        .is_none());
}

#[test]
fn same_key_evidence_must_agree() {
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_point(int(3), ModelValue::Bool(true)));
    assert!(accumulator.merge_point(int(3), ModelValue::Bool(true)));
    assert!(!accumulator.merge_point(int(3), ModelValue::Bool(false)));
}

#[test]
fn one_interpretation_uses_newest_shadowing_store() {
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_interpretation(
        Some(ModelValue::Bool(false)),
        vec![
            (int(7), ModelValue::Bool(true)),
            (int(7), ModelValue::Bool(false)),
        ],
    ));
    let Some(ModelValue::Array(value)) = accumulator.finish(&Sort::Bool) else {
        panic!("complete interpretation must produce an array");
    };
    assert_eq!(value.store.len(), 1);
    assert!(matches!(value.store[0].1, ModelValue::Bool(true)));
}

#[test]
fn partial_interpretation_is_rejected_atomically() {
    let mut accumulator = ArrayAccumulator::default();
    assert!(!accumulator.merge_interpretation(None, vec![(int(1), ModelValue::Bool(true))],));
    assert!(accumulator.finish(&Sort::Bool).is_none());
}

#[test]
fn conflicting_interpretation_does_not_leak_partial_points() {
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_interpretation(
        Some(ModelValue::Bool(false)),
        vec![(int(1), ModelValue::Bool(true))],
    ));
    assert!(!accumulator.merge_interpretation(
        Some(ModelValue::Bool(false)),
        vec![
            (int(2), ModelValue::Bool(true)),
            (int(1), ModelValue::Bool(false)),
        ],
    ));
    let Some(ModelValue::Array(value)) = accumulator.finish(&Sort::Bool) else {
        panic!("the first complete interpretation must remain intact");
    };
    assert_eq!(value.store.len(), 1);
    assert!(same_value(&value.store[0].0, &int(1)));
}

#[test]
fn congruent_members_merge_disjoint_observations() {
    let mut accumulator = ArrayAccumulator::default();
    assert!(accumulator.merge_interpretation(
        Some(ModelValue::Bool(false)),
        vec![(int(1), ModelValue::Bool(true))],
    ));
    assert!(accumulator.merge_interpretation(
        Some(ModelValue::Bool(false)),
        vec![(int(2), ModelValue::Bool(true))],
    ));
    let Some(ModelValue::Array(value)) = accumulator.finish(&Sort::Bool) else {
        panic!("merged class evidence must produce an array");
    };
    assert_eq!(value.store.len(), 2);
}

mod audit;
mod durable;
mod extensionality;
mod forced_sources;
