// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::model::dt_construct::dt_canonical_string;

const VALUE: &str = "(outer (store ((as const (Array (_ BitVec 64) Row))
    (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
    (_ bv33 64) (row (_ bv65 64)
      (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
        (_ bv64 64) #x09))))";

fn fixture() -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(set-logic ALL)
                 (declare-sort Hidden 0)
                 (declare-datatype Row ((row (len (_ BitVec 64))
                   (data (Array (_ BitVec 64) (_ BitVec 8))))))
                 (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))
                 (declare-datatype Opaque ((opaque (hidden (Array Int Hidden)))))
                 (declare-datatype BadKey ((bad_key (keys (Array Row Bool)))))",
            )
            .unwrap(),
        )
        .unwrap();
    executor
}

fn word(value: i64, width: u32) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), width)
}

fn array(default: ModelValue, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue { default, store }))
}

fn expected() -> ModelValue {
    ModelValue::Datatype {
        ctor: "outer".into(),
        args: vec![array(
            ModelValue::Datatype {
                ctor: "row".into(),
                args: vec![word(0, 64), array(word(0, 8), vec![])],
            },
            vec![(
                word(33, 64),
                ModelValue::Datatype {
                    ctor: "row".into(),
                    args: vec![
                        word(65, 64),
                        array(word(7, 8), vec![(word(64, 64), word(9, 8))]),
                    ],
                },
            )],
        )],
    }
}

#[test]
fn complete_nested_field_text_keeps_defaults_and_both_far_stores() {
    let executor = fixture();
    let sort = Sort::Uninterpreted("Outer".into());
    let guard = RenderedDatatypeGuard::new(&executor);
    assert!(guard.is_exact_array_cell(&sort));
    assert!(
        !guard.is_exact(&sort),
        "concrete parsing is not synthesis authority"
    );
    let value = executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut TypedArrayParseBudget::new())
        .unwrap();
    assert_eq!(
        dt_canonical_string(&value),
        dt_canonical_string(&expected())
    );
    assert!(typed_datatype_array_value(&value, &sort, &guard));
    assert!(same_datatype_array_value(&value, &expected()));
}

#[test]
fn nested_field_text_rejects_wrong_schema_width_arity_and_opaque_values() {
    let executor = fixture();
    let sort = Sort::Uninterpreted("Outer".into());
    let guard = RenderedDatatypeGuard::new(&executor);
    for text in [
        VALUE.replace("(_ bv33 64)", "(_ bv33 32)"),
        VALUE.replace("#x09", "#x0009"),
        VALUE.replace("(row (_ bv65 64)", "(outer (_ bv65 64)"),
        VALUE.replace("(row (_ bv65 64)", "(row (_ bv65 64) true"),
        VALUE.replace("(_ BitVec 8))) #x07", "(_ BitVec 16))) #x07"),
        format!("{VALUE} false"),
        "@Outer!0".into(),
    ] {
        assert!(
            executor
                .typed_field_value_text(&text, &sort, &guard, &mut TypedArrayParseBudget::new())
                .is_none(),
            "accepted malformed nested witness: {text}"
        );
    }
    assert!(!guard.is_exact_array_cell(&Sort::Uninterpreted("Opaque".into())));
    assert!(!guard.is_exact_array_cell(&Sort::Uninterpreted("BadKey".into())));
    assert!(executor
        .typed_field_value_text(
            "(opaque ((as const (Array Int Hidden)) @Hidden!0))",
            &Sort::Uninterpreted("Opaque".into()),
            &guard,
            &mut TypedArrayParseBudget::new(),
        )
        .is_none());
}

#[test]
fn nested_field_text_shares_parse_budget_and_honors_sticky_interrupt() {
    use std::sync::{atomic::AtomicBool, Arc};

    let mut executor = fixture();
    let sort = Sort::Uninterpreted("Outer".into());
    let guard = RenderedDatatypeGuard::new(&executor);
    let mut budget = TypedArrayParseBudget::new();
    let chunk = format!(
        "{}0",
        " ".repeat(super::super::super::rendered_dt_limits::MAX_RENDERED_DT_BYTES - 1)
    );
    for _ in 0..4 {
        assert!(budget.charge_text(&chunk));
    }
    assert!(executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut budget)
        .is_none());
    assert!(executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut TypedArrayParseBudget::new())
        .is_some());
    let interrupt = Arc::new(AtomicBool::new(true));
    executor.solve_interrupt = Some(interrupt.clone());
    assert!(executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut TypedArrayParseBudget::new())
        .is_none());
    interrupt.store(false, std::sync::atomic::Ordering::Relaxed);
    assert!(executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut TypedArrayParseBudget::new())
        .is_none());
    executor.begin_external_decision_query(false);
    let value = executor
        .typed_field_value_text(VALUE, &sort, &guard, &mut TypedArrayParseBudget::new())
        .expect("a fresh decision has a fresh evaluation budget");
    assert_eq!(
        dt_canonical_string(&value),
        dt_canonical_string(&expected())
    );
}
