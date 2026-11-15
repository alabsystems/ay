// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consumer precedence under competing private model data, not SAT authority.

use super::*;
use crate::executor::model::projection_uf::ProjectionUfModel;
use ay_core::{DatatypeSort, Symbol};
use ay_model_check::{ArrayValue, GateVerdict, ModelView};

fn projection(symbol: Symbol, sort: &Sort) -> ProjectionUfModel {
    ProjectionUfModel::from_test_definitions([(
        symbol,
        vec![sort.clone(), sort.clone()],
        sort.clone(),
        1,
    )])
    .unwrap()
}

fn resolved(
    shared: &AggregateConstantValues,
    exec: &Executor,
    model: &Model,
    term: TermId,
) -> String {
    match shared.resolve(exec, model, term).unwrap() {
        AggregateConstantValue::Value(value) => value,
        _ => panic!("expected a complete aggregate value"),
    }
}

fn bool_array_text(exec: &Executor, sort: &Sort, default: bool) -> String {
    exec.format_gate_model_value(
        &ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(default),
            store: vec![],
        })),
        sort,
    )
    .unwrap()
}

#[test]
fn datatype_projection_selects_before_competing_application_egraph_and_gate_values() {
    let (mut exec, mut model, selected) = fixture();
    let sort = exec.ctx.terms.sort(selected).clone();
    let TermData::App(ctor, _) = exec.ctx.terms.get(selected).clone() else {
        unreachable!()
    };
    let no = exec.ctx.terms.false_term();
    let other = exec.ctx.terms.mk_app(ctor, [no], sort.clone());
    let symbol = Symbol::named("project_box");
    let application = exec
        .ctx
        .terms
        .mk_app(symbol.clone(), [other, selected], sort.clone());
    model.projection_ufs = projection(symbol, &sort);
    model.dt_ground.insert(
        application,
        ModelValue::Datatype {
            ctor: "box".into(),
            args: vec![ModelValue::Bool(false)],
        },
    );
    model
        .dt_pins
        .insert(application, EvalValue::Element("(box false)".into()));
    let mut shared = AggregateConstantValues::collect(&exec, &model).unwrap();
    assert_eq!(
        shared.gate.get(&selected).map(String::as_str),
        Some("(box true)")
    );
    // A stale application-keyed candidate must not stand in for the selected
    // argument, even if it looks like a complete, marker-free constructor.
    shared.gate.insert(application, "(box false)".into());
    assert_eq!(resolved(&shared, &exec, &model, application), "(box true)");
    *exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(application, true)));
    assert_eq!(resolved(&shared, &exec, &model, application), "(box true)");
    *exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(application, false)));
    assert_eq!(resolved(&shared, &exec, &model, application), "(box true)");

    // Once the argument is selected, its coherent e-graph value still owns the
    // selector-totalization branch keys ahead of the complete gate map.
    *exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(selected, true)));
    assert_eq!(resolved(&shared, &exec, &model, application), "(box false)");
    exec.dt_egraph_assignment.replace(None);
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert_eq!(
        exec.values(&[("(project_box (box false) v)".into(), application)]),
        "(((project_box (box false) v) (box true)))"
    );
}

struct Unpinned<'a>(&'a Executor);

impl ModelView for Unpinned<'_> {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }

    fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
        self.0.dt_registry_lookup(name)
    }
}

#[test]
fn array_projection_preserves_selected_and_residual_owners_and_refuses_malformed_data() {
    let mut exec = Executor::new();
    for command in ay_frontend::parse(
        "(set-logic ALL)
        (declare-const a (Array Bool Bool)) (assert (select a false))",
    )
    .unwrap()
    {
        exec.ctx.process_command(&command).unwrap();
    }
    let selected = exec.ctx.source_constant_for_value("a").unwrap().0;
    let sort = exec.ctx.terms.sort(selected).clone();
    let no = exec.ctx.terms.false_term();
    let other = exec.ctx.terms.mk_const_array(Sort::Bool, no);
    let symbol = Symbol::named("project_array");
    let application = exec
        .ctx
        .terms
        .mk_app(symbol.clone(), [other, selected], sort.clone());
    let valid = projection(symbol.clone(), &sort);
    let mut model = Model::empty();
    model.projection_ufs = valid.clone();
    let mut arrays = ay_arrays::ArrayModel::default();
    for (term, default) in [(selected, "true"), (application, "false")] {
        arrays.array_values.insert(
            term,
            ay_arrays::ArrayInterpretation {
                default: Some(default.into()),
                stores: vec![],
                index_sort: Some(Sort::Bool),
                element_sort: Some(Sort::Bool),
            },
        );
    }
    model.array_model = Some(arrays);
    let expected = bool_array_text(&exec, &sort, true);
    let wrong = bool_array_text(&exec, &sort, false);
    let mut shared = AggregateConstantValues::collect(&exec, &model).unwrap();
    assert_eq!(shared.gate.get(&selected), Some(&expected));
    shared.gate.insert(application, wrong.clone());
    assert_eq!(resolved(&shared, &exec, &model, application), expected);
    model.projection_ufs = ProjectionUfModel::from_malformed_test_definition_unchecked(
        symbol,
        vec![sort.clone(), sort.clone()],
        sort,
        2,
    );
    assert!(shared.resolve(&exec, &model, application).is_err());
    model.projection_ufs = valid;

    assert_checked_residual_projection_ownership();
}

fn assert_checked_residual_projection_ownership() {
    let mut exec = Executor::new();
    // Residual completion admits datatype-element arrays and retained equality
    // roots, not the bare Bool read used by the ordinary projection control.
    for command in ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype Cell ((cell (n (_ BitVec 8)))))
         (declare-const a (Array Bool Cell))
         (assert (= (n (select a false)) #x05))",
    )
    .unwrap()
    {
        exec.ctx.process_command(&command).unwrap();
    }
    assert_eq!(exec.ctx.assertions.len(), 1);
    assert!(matches!(exec.ctx.terms.get(exec.ctx.assertions[0]),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2));
    let selected = exec.ctx.source_constant_for_value("a").unwrap().0;
    let sort = exec.ctx.terms.sort(selected).clone();
    let ctor = exec.dt_registry_lookup("Cell").unwrap().constructors[0]
        .name
        .clone();
    let zero = exec.ctx.terms.mk_bitvec(0.into(), 8);
    let other_cell = exec.ctx.terms.mk_app(
        Symbol::named(&ctor),
        [zero],
        sort.array_element().unwrap().clone(),
    );
    let other = exec.ctx.terms.mk_const_array(Sort::Bool, other_cell);
    let symbol = Symbol::named("project_array");
    let application = exec
        .ctx
        .terms
        .mk_app(symbol.clone(), [other, selected], sort.clone());
    let mut model = Model::empty();
    model.projection_ufs = projection(symbol, &sort);
    let wrong = exec
        .format_gate_model_value(
            &ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Datatype {
                    ctor,
                    args: vec![ModelValue::BitVec {
                        value: 0.into(),
                        width: 8,
                    }],
                },
                store: vec![],
            })),
            &sort,
        )
        .unwrap();
    // Install a genuinely checked free-array completion. This remains model
    // DATA: no native publication capability is constructed by this test.
    let unpinned = Unpinned(&exec);
    let (verdict, completion) = ay_model_check::confirm_model_with_array_completion(
        &exec.ctx.terms,
        &unpinned,
        &exec.ctx.assertions,
    )
    .into_parts();
    assert!(
        matches!(verdict, GateVerdict::ConfirmedSat),
        "registered datatype-array equality must admit completion: {verdict:?}"
    );
    let assignments = completion.unwrap().into_assignments().unwrap();
    assert_eq!(assignments.len(), 1);
    model
        .install_residual_arrays(&exec.ctx, assignments)
        .unwrap();
    let owned = exec.term_value_string(&model, selected).unwrap();
    assert_ne!(
        owned, wrong,
        "retained value must satisfy the authored field value five, not zero"
    );
    let mut shared = AggregateConstantValues::collect(&exec, &model).unwrap();
    assert!(
        shared.gate.is_empty(),
        "residual ownership disables competing collection"
    );
    shared.gate.insert(selected, wrong.clone());
    shared.gate.insert(application, wrong);
    assert_eq!(resolved(&shared, &exec, &model, application), owned);
    for command in ay_frontend::parse("(declare-const later Bool)").unwrap() {
        exec.ctx.process_command(&command).unwrap();
    }
    assert!(!model.residual_arrays_are_current(&exec.ctx));
    assert!(
        shared.resolve(&exec, &model, application).is_err(),
        "a stale retained owner cannot fall through to a valid projection and complete map"
    );
}
