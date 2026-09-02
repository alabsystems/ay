// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certificate durability, resource exhaustion, and tamper controls.

use super::*;

#[test]
fn durable_certificate_rejects_partial_second_pass_model() {
    let mut fixture = build_fixture();
    assert_complete_coverage(&fixture);
    let partial = assert_partial_and_outer_mismatch(&fixture);
    assert_omitted_and_forged_rows(&fixture);
    assert_structural_collision_declines(&fixture);
    assert!(
        fixture
            .executor
            .independent_datatype_element_value_for_test(
                &partial,
                &fixture.carrier,
                &fixture.cell_sort,
            )
            .is_none()
    );
    authored_selector_observation_invalidates_free_field(&mut fixture);

    let old_stamp = fixture
        .executor
        .ctx
        .terms
        .entry_stamp(fixture.cell)
        .expect("inventoried member is live before reset");
    fixture.executor.reset();
    let commands = ay_frontend::parse(FIXTURE).expect("reset fixture parses");
    assert_eq!(
        fixture
            .executor
            .execute_all(&commands)
            .expect("reset fixture executes"),
        ["sat", "sat"]
    );
    assert_ne!(
        fixture.executor.ctx.terms.entry_stamp(fixture.cell),
        Some(old_stamp)
    );
    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&partial, fixture.cell)
        .is_none());
    assert!(!fixture
        .executor
        .observed_datatype_array_fields_complete(&partial, &fixture.outer_sort));
}

#[test]
fn unrelated_global_model_rows_do_not_consume_w6_authority() {
    let mut fixture = build_fixture();
    let unrelated: Vec<_> = (0..(MAX_EXACT_ARRAY_FIELD_TERMS + 128))
        .map(|ordinal| {
            fixture
                .executor
                .ctx
                .terms
                .mk_var(format!("w6-unrelated-{ordinal}"), Sort::Bool)
        })
        .collect();
    assert!(fixture.executor.ctx.terms.len() > MAX_EXACT_ARRAY_FIELD_TERMS);

    let assert_current = |fixture: &Fixture| {
        assert!(fixture
            .executor
            .authenticated_datatype_array_field_classes(&fixture.model)
            .is_some());
        let members = fixture
            .executor
            .authenticated_datatype_array_completion_members(&fixture.model, &fixture.outer_sort)
            .expect("unrelated global rows cannot revoke completion authority");
        assert!(members.contains(fixture.cell));
        assert!(fixture
            .executor
            .independent_datatype_term_value_for_test(&fixture.model, fixture.cell)
            .is_some());
        assert!(fixture
            .executor
            .independent_array_select_value_for_test(&fixture.model, fixture.cell)
            .is_some());
    };
    assert_current(&fixture);

    let euf = fixture
        .model
        .euf_model
        .as_mut()
        .expect("fixture has an EUF model");
    for (ordinal, &term) in unrelated.iter().enumerate() {
        euf.term_values
            .insert(term, format!("@unrelated!{ordinal}"));
    }
    assert!(euf.term_values.len() > MAX_EXACT_ARRAY_FIELD_TERMS);
    assert_current(&fixture);

    for &term in unrelated.iter().take(1_025) {
        fixture
            .model
            .dt_ground
            .insert(term, ModelValue::Bool(false));
    }
    assert!(fixture.model.dt_ground.len() > 1_024);
    assert_current(&fixture);
}

#[test]
fn legacy_import_work_exhaustion_preserves_w6_and_discards_partial_rows() {
    const LEGACY_PAYLOAD_BYTES: usize = 720_000;
    const LEGACY_ROWS: usize = 3;
    const LEGACY_WORK_CAP: usize = 4 * 1_024 * 1_024;

    let mut fixture = build_fixture();
    let declarations =
        ay_frontend::parse("(declare-datatype LegacyW6 ((legacy-w6 (legacy-payload String))))")
            .expect("legacy-work datatype parses");
    assert!(fixture
        .executor
        .execute_all(&declarations)
        .expect("legacy-work datatype declaration executes")
        .is_empty());
    let legacy_sort = Sort::Uninterpreted("LegacyW6".to_string());
    let legacy_constructor = fixture
        .executor
        .ctx
        .datatype_constructors("LegacyW6")
        .and_then(|constructors| constructors.first())
        .cloned()
        .expect("legacy-work datatype has one registered constructor");

    let mut carriers = Vec::new();
    let mut aggregate_legacy_work = 0usize;
    for ordinal in 0..LEGACY_ROWS {
        let term = fixture
            .executor
            .ctx
            .terms
            .mk_var(format!("legacy-work-{ordinal}"), legacy_sort.clone());
        let carrier = format!("@LegacyW6!{ordinal}");
        let value = ModelValue::Datatype {
            ctor: legacy_constructor.clone(),
            args: vec![ModelValue::Str("x".repeat(LEGACY_PAYLOAD_BYTES))],
        };
        let value_work = super::super::super::super::rendered_dt_limits::model_value_work(&value)
            .expect("each legacy row is within the per-value bound");
        let rendered = fixture
            .executor
            .format_gate_model_value(&value, &legacy_sort)
            .expect("each legacy row is individually renderable");
        let row_work = value_work + rendered.len() + carrier.len();
        assert!(row_work < LEGACY_WORK_CAP);
        aggregate_legacy_work += row_work;

        fixture.model.dt_ground.insert(term, value.clone());
        fixture
            .model
            .euf_model
            .as_mut()
            .expect("fixture has an EUF model")
            .term_values
            .insert(term, carrier.clone());
        carriers.push(carrier.clone());

        if ordinal == 0 {
            let imported = fixture
                .executor
                .independent_exact_datatype_cell_value_for_test(
                    &fixture.model,
                    &carrier,
                    &legacy_sort,
                )
                .expect("one bounded legacy row is imported");
            assert!(same_value(&imported, &value));
        }
    }
    assert!(aggregate_legacy_work > LEGACY_WORK_CAP);
    assert!(fixture.model.dt_ground.len() < 1_024);
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&fixture.model)
        .is_some());

    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&fixture.model, fixture.cell)
        .is_some());
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&fixture.model, fixture.cell)
        .is_some());
    for carrier in carriers {
        assert!(fixture
            .executor
            .independent_exact_datatype_cell_value_for_test(&fixture.model, &carrier, &legacy_sort,)
            .is_none());
    }
}

#[test]
fn oversized_authored_scope_fails_closed_and_recovers() {
    let mut fixture = build_fixture();
    let original_roots = fixture.executor.independent_gate_query_roots();
    let oversized_roots: Vec<_> = (0..(MAX_EXACT_ARRAY_FIELD_TERMS + 1))
        .map(|ordinal| {
            fixture
                .executor
                .ctx
                .terms
                .mk_var(format!("w6-authored-{ordinal}"), Sort::Bool)
        })
        .collect();
    fixture.executor.independent_gate_authored_assertions = Some(oversized_roots);
    assert!(fixture
        .executor
        .datatype_array_field_required_terms()
        .is_none());
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&fixture.model)
        .is_none());
    assert!(fixture
        .executor
        .authenticated_datatype_array_completion_members(&fixture.model, &fixture.outer_sort)
        .is_none());

    fixture.executor.independent_gate_authored_assertions = Some(original_roots);
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&fixture.model)
        .is_some());
    assert!(fixture
        .executor
        .authenticated_datatype_array_completion_members(&fixture.model, &fixture.outer_sort)
        .is_some());
}

#[test]
fn carrier_tampering_revokes_w6_authority() {
    let fixture = build_fixture();
    let mut tampered = fixture.model.clone();
    tampered
        .euf_model
        .as_mut()
        .expect("fixture has EUF evidence")
        .term_values
        .insert(fixture.cell, fixture.other_carrier.clone());

    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&tampered)
        .is_none());
    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&tampered, fixture.cell)
        .is_none());
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&tampered, fixture.cell)
        .is_none());
}
