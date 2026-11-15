// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private output-data tests, not native SAT publication or seal construction.

use super::*;
use crate::executor::model::dt_egraph_values::DtEgraphAssignment;
use crate::executor::model::EvalValue;
use crate::executor_types::SolveResult;
use ay_core::term::TermData;
use ay_model_check::ModelValue;
use std::sync::Arc;

mod projection;

fn fixture() -> (Executor, Model, TermId) {
    let mut exec = Executor::new();
    for command in ay_frontend::parse(
        "(set-option :produce-models true) (set-logic ALL)
         (declare-datatype Box ((box (payload Bool))))
         (declare-const v Box)",
    )
    .unwrap()
    {
        exec.ctx.process_command(&command).unwrap();
    }
    let term = exec.ctx.source_constant_for_value("v").unwrap().0;
    let TermData::App(_, children) = exec.ctx.terms.get(term) else {
        panic!("declared single-constructor value has an eager source carrier");
    };
    assert_eq!(children.len(), 1);
    let mut model = Model::empty();
    model
        .completed_values
        .insert(children[0], EvalValue::Bool(true));
    model.dt_ground.insert(
        term,
        ModelValue::Datatype {
            ctor: "box".into(),
            args: vec![ModelValue::Bool(false)],
        },
    );
    (exec, model, term)
}

fn assignment(term: TermId, coherent: bool) -> DtEgraphAssignment {
    let mut assignment = DtEgraphAssignment {
        dtm: ay_dt::DtModel::default(),
        class_value: Default::default(),
        class_fields: Default::default(),
        class_ctor: Default::default(),
        poisoned: Default::default(),
        diseq_incoherent: Default::default(),
        self_check_ok: coherent,
    };
    assignment.class_value.insert(term, "(box false)".into());
    if !coherent {
        assignment.poisoned.insert(term);
        assignment.diseq_incoherent.insert(term);
    }
    assignment
}

#[test]
fn complete_source_carrier_reconstruction_precedes_stale_ground_in_one_batch() {
    let (mut exec, model, term) = fixture();
    assert_eq!(exec.term_value_string(&model, term).unwrap(), "(box false)");
    let requested = vec![("v".into(), term), ("again".into(), term)];
    let shared = AggregateConstantValues::for_values(&exec, &model, &requested).unwrap();
    assert_eq!(
        shared.gate.get(&term).map(String::as_str),
        Some("(box true)")
    );
    assert!(matches!(shared.resolve(&exec, &model, term).unwrap(),
        AggregateConstantValue::Value(value) if value == "(box true)"));
    let arena_len = exec.ctx.terms.len();
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert_eq!(
        exec.values(&requested),
        "((v (box true)) (again (box true)))"
    );
    assert_eq!(exec.ctx.terms.len(), arena_len);
}

#[test]
fn coherent_egraph_value_precedes_the_complete_gate_reconstruction() {
    let (mut exec, model, term) = fixture();
    let shared = AggregateConstantValues::collect(&exec, &model).unwrap();
    assert_eq!(
        shared.gate.get(&term).map(String::as_str),
        Some("(box true)")
    );
    *exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(term, true)));
    assert!(matches!(shared.resolve(&exec, &model, term).unwrap(),
        AggregateConstantValue::Value(value) if value == "(box false)"));
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert_eq!(exec.values(&[("v".into(), term)]), "((v (box false)))");
}

#[test]
fn incoherent_egraph_class_refuses_a_complete_map_and_stale_ground_fallback() {
    let (mut exec, model, term) = fixture();
    let shared = AggregateConstantValues::collect(&exec, &model).unwrap();
    assert!(shared.gate.contains_key(&term));
    *exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(term, false)));
    assert!(matches!(
        shared.resolve(&exec, &model, term).unwrap(),
        AggregateConstantValue::Poisoned
    ));
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    let output = exec.values(&[("v".into(), term)]);
    assert!(output.starts_with("(error"), "{output}");
    assert!(!output.contains("(box false)"));
    assert!(!exec.model().contains("(define-fun v "));
}

#[test]
fn scalar_only_requests_leave_aggregate_reconstruction_absent() {
    let (exec, model, term) = fixture();
    let TermData::App(_, children) = exec.ctx.terms.get(term) else {
        panic!("eager source carrier");
    };
    let scalar = children[0];
    let shared =
        AggregateConstantValues::for_values(&exec, &model, &[("payload".into(), scalar)]).unwrap();
    assert!(shared.gate.is_empty());
    assert!(matches!(
        shared.resolve(&exec, &model, scalar).unwrap(),
        AggregateConstantValue::Absent
    ));
    assert_eq!(exec.term_value_string(&model, scalar).unwrap(), "true");
}
