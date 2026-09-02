// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use ay_model_check::ModelValue;

#[test]
fn every_strict_funnel_uses_the_scoped_authority_wrapper() {
    let source = include_str!("../pipeline.rs");
    let scoped_call = ["self.verify_model_strict_", "with_scoped_authority()"].concat();
    assert_eq!(
        source.matches(&scoped_call).count(),
        6,
        "each of the three strict funnels and its retry must share one authority policy"
    );
    let raw_call = ["self.verify_model_", "strict()"].concat();
    assert_eq!(
        source.matches(&raw_call).count(),
        2,
        "raw strict checks belong only inside the scoped wrapper and the exact-certificate read-only gate"
    );
}

#[test]
fn datatype_strict_authority_is_scoped_and_fails_closed() {
    let commands = ay_frontend::parse(
        r#"
            (set-logic ALL)
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (is-mk (f 0)))
            (assert (is-mk (f 1)))
            (assert (distinct (f 0) (f 1)))
            (check-sat)
        "#,
    )
    .expect("W6 strict-authority fixture parses");
    let mut executor = Executor::new();
    assert_eq!(
        executor
            .execute_all(&commands)
            .expect("W6 strict-authority fixture executes"),
        ["sat"]
    );
    let original_roots = executor.independent_gate_query_roots();
    let model = executor.last_model.as_ref().expect("sat retains a model");
    assert!(!executor
        .authenticated_datatype_array_field_classes(model)
        .expect("the installed W6 inventory reauthenticates")
        .is_empty());
    assert!(executor.strict_coverage_gap_has_full_independent_authority("datatype"));
    assert!(
        !executor.strict_coverage_gap_has_full_independent_authority("datatype-field"),
        "an adjacent oracle spelling must remain out of scope"
    );
    assert!(
        !executor.strict_coverage_gap_has_full_independent_authority("arrays"),
        "an unrelated strict oracle must remain out of scope"
    );

    let falsehood = executor.ctx.terms.false_term();
    let mut violating_roots = original_roots.clone();
    violating_roots.push(falsehood);
    executor.independent_gate_authored_assertions = Some(violating_roots);
    assert!(
        !executor.strict_coverage_gap_has_full_independent_authority("datatype"),
        "a model violation must not acquire authority"
    );
    executor.independent_gate_authored_assertions = Some(original_roots.clone());
    let unpinned = executor.ctx.terms.mk_var("unpinned", Sort::Bool);
    let mut incomplete_roots = original_roots.clone();
    incomplete_roots.push(unpinned);
    executor.independent_gate_authored_assertions = Some(incomplete_roots);
    assert!(
        !executor.strict_coverage_gap_has_full_independent_authority("datatype"),
        "an unevaluable authored assertion must not acquire authority"
    );

    let mut scalar_executor = Executor::new();
    let marker = scalar_executor
        .ctx
        .terms
        .mk_var("constructed-datatype", Sort::Uninterpreted("D".to_string()));
    let truth = scalar_executor.ctx.terms.true_term();
    let mut scalar_model = crate::executor::model::Model::empty();
    scalar_model.dt_ground.insert(
        marker,
        ModelValue::Datatype {
            ctor: "D_mk".to_string(),
            args: vec![ModelValue::Int(0.into())],
        },
    );
    scalar_executor.last_model = Some(scalar_model);
    scalar_executor.independent_gate_authored_assertions = Some(vec![truth]);
    assert!(
        !scalar_executor.strict_coverage_gap_has_full_independent_authority("datatype"),
        "scalar-only dt_ground rows are not W6 authority"
    );

    executor.independent_gate_authored_assertions = Some(original_roots);
    executor
        .last_model
        .as_mut()
        .expect("candidate model")
        .dt_array_field_classes
        .first_mut()
        .expect("fixture has W6 authority")
        .carrier
        .push_str("-tampered");
    assert!(
        !executor.strict_coverage_gap_has_full_independent_authority("datatype"),
        "tampered raw W6 inventory must not authorize a strict deferral"
    );
}
