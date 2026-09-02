// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::model::EvalValue;

fn field_sort(fixture: &Fixture) -> Sort {
    fixture
        .executor
        .ctx
        .constructor_selector_info("mk")
        .and_then(|fields| fields.first())
        .map(|(_, sort)| sort.clone())
        .expect("fixture declares g as its array field")
}

fn field_app(fixture: &mut Fixture, cell: TermId) -> TermId {
    fixture
        .executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), [cell], field_sort(fixture))
}

fn selected(value: &ArrayValue, index: &ModelValue) -> ModelValue {
    value
        .store
        .iter()
        .rev()
        .find(|(key, _)| same_value(key, index))
        .map_or_else(|| value.default.clone(), |(_, value)| value.clone())
}

#[test]
fn strict_output_and_select_use_authenticated_unobserved_projection() {
    let mut fixture = build_fixture();
    let fresh_index = fixture.executor.ctx.terms.mk_int(BigInt::from(97_531));
    let fresh_cell = fixture
        .executor
        .ctx
        .terms
        .mk_select(fixture.outer, fresh_index);
    assert!(fixture
        .model
        .dt_array_field_classes
        .iter()
        .all(|authority| { !authority.members.contains_key(&fresh_cell) }));
    let app = field_app(&mut fixture, fresh_cell);
    let (sort, projected) = fixture
        .executor
        .authenticated_unobserved_array_field(&fixture.model, app)
        .expect("fresh exact outer select resolves to one authenticated class");
    let index_term = fixture.executor.ctx.terms.mk_int(BigInt::from(4_009));
    let index_value = ModelValue::Int(BigInt::from(4_009));
    let expected = selected(&projected, &index_value);

    // A retained/generated row is weaker than the whole-datatype certificate.
    let wrong = !matches!(expected, ModelValue::Bool(true));
    fixture
        .model
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .insert(
            app,
            ay_arrays::ArrayInterpretation {
                default: Some(wrong.to_string()),
                stores: Vec::new(),
                index_sort: Some(sort.index_sort.clone()),
                element_sort: Some(sort.element_sort.clone()),
            },
        );
    assert_eq!(
        fixture
            .executor
            .evaluate_select(&fixture.model, app, index_term),
        super::super::super::super::dt_construct::mv_to_eval(&expected)
    );
    let rendered = fixture
        .executor
        .term_value_string(&fixture.model, app)
        .expect("strict get-value renders the authenticated array");
    assert_eq!(
        rendered,
        fixture
            .executor
            .format_gate_model_value(
                &ModelValue::Array(Box::new(projected.clone())),
                &Sort::Array(Box::new(sort)),
            )
            .expect("projected array is round-trippable")
    );
    let read = fixture.executor.ctx.terms.mk_select(app, index_term);
    assert_eq!(
        fixture
            .executor
            .term_value_string(&fixture.model, read)
            .expect("scalar get-value uses the same projection"),
        fixture
            .executor
            .format_gate_model_value(&expected, &Sort::Bool)
            .expect("projected scalar is round-trippable")
    );
}

#[test]
fn stale_fresh_outer_select_projection_cannot_fall_back_to_raw_row() {
    let mut fixture = build_fixture();
    let fresh_index = fixture.executor.ctx.terms.mk_int(BigInt::from(97_532));
    let fresh_cell = fixture
        .executor
        .ctx
        .terms
        .mk_select(fixture.outer, fresh_index);
    let app = field_app(&mut fixture, fresh_cell);
    let zero = fixture.executor.ctx.terms.mk_int(BigInt::from(0));
    assert!(fixture
        .executor
        .authenticated_unobserved_array_field(&fixture.model, app)
        .is_some());
    fixture
        .model
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .insert(
            app,
            ay_arrays::ArrayInterpretation {
                default: Some("true".to_string()),
                stores: Vec::new(),
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Bool),
            },
        );

    let wrong_member = fixture
        .executor
        .ctx
        .terms
        .mk_var("w6-fresh-projection-wrong-stamp", fixture.cell_sort.clone());
    let wrong_stamp = fixture
        .executor
        .ctx
        .terms
        .entry_stamp(wrong_member)
        .expect("fresh wrong member has a stamp");
    fixture
        .model
        .dt_array_field_classes
        .iter_mut()
        .find(|authority| authority.members.contains_key(&fixture.cell))
        .expect("fixture cell has authority")
        .members
        .insert(fixture.cell, wrong_stamp);

    assert!(fixture
        .executor
        .authenticated_unobserved_array_field(&fixture.model, app)
        .is_none());
    assert!(fixture
        .executor
        .unobserved_array_field_authority_claim(&fixture.model, app));
    assert_eq!(
        fixture.executor.evaluate_select(&fixture.model, app, zero),
        EvalValue::Unknown,
        "a raw row cannot bypass stale authority for a fresh outer select"
    );
    assert!(fixture
        .executor
        .term_value_string(&fixture.model, app)
        .is_err());
}

#[test]
fn projection_is_newest_wins_and_stale_authority_fails_closed() {
    let mut fixture = build_fixture();
    let cell = fixture.cell;
    let app = field_app(&mut fixture, cell);
    let zero_term = fixture.executor.ctx.terms.mk_int(BigInt::from(0));
    let zero = ModelValue::Int(BigInt::from(0));
    let members: Vec<_> = fixture
        .model
        .dt_array_field_classes
        .iter()
        .find(|authority| authority.members.contains_key(&fixture.cell))
        .expect("fixture cell has authority")
        .members
        .keys()
        .copied()
        .collect();
    for member in members {
        let ModelValue::Datatype { args, .. } = fixture
            .model
            .dt_ground
            .get_mut(&member)
            .expect("member has exact ground value")
        else {
            panic!("fixture value is a datatype");
        };
        args[0] = ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![
                (zero.clone(), ModelValue::Bool(false)),
                (zero.clone(), ModelValue::Bool(true)),
            ],
        }));
    }
    assert_eq!(
        fixture
            .executor
            .evaluate_select(&fixture.model, app, zero_term),
        EvalValue::Bool(true),
        "the newest ModelValue store entry must win"
    );

    let mut forged = fixture.model.clone();
    forged.dt_ground.insert(
        fixture.cell,
        ModelValue::Uninterpreted("(mk (#arr false))".to_string()),
    );
    assert!(fixture
        .executor
        .authenticated_unobserved_array_field(&forged, app)
        .is_none());

    let wrong_member = fixture
        .executor
        .ctx
        .terms
        .mk_var("w6-projection-wrong-stamp", fixture.cell_sort.clone());
    let wrong_stamp = fixture
        .executor
        .ctx
        .terms
        .entry_stamp(wrong_member)
        .expect("fresh wrong member has a stamp");
    fixture
        .model
        .dt_array_field_classes
        .iter_mut()
        .find(|authority| authority.members.contains_key(&fixture.cell))
        .expect("fixture cell has authority")
        .members
        .insert(fixture.cell, wrong_stamp);
    fixture
        .model
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .insert(
            app,
            ay_arrays::ArrayInterpretation {
                default: Some("true".to_string()),
                stores: Vec::new(),
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Bool),
            },
        );
    assert!(fixture
        .executor
        .authenticated_unobserved_array_field(&fixture.model, app)
        .is_none());
    assert_eq!(
        fixture
            .executor
            .evaluate_select(&fixture.model, app, zero_term),
        EvalValue::Unknown,
        "a raw array row cannot bypass a stale stamped certificate"
    );
    assert!(fixture
        .executor
        .term_value_string(&fixture.model, app)
        .is_err());
}
