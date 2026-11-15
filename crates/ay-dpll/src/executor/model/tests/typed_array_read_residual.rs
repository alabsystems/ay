// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed direct reads and residual replay at the native model boundary.

use super::super::independent_gate::IndependentModelView;
use super::*;
use ay_arrays::ArrayInterpretation;
use ay_model_check::{
    confirm_completed_model, confirm_model_with_array_completion, GateVerdict, ModelValue,
    ModelView,
};

const DECLARATIONS: &str = r#"
(set-logic ALL)
(declare-datatype Cell ((Mk (number (_ BitVec 8)))))
(declare-datatype Flag ((Off) (On)))
(declare-sort Atom 0)
(declare-const cells (Array (_ BitVec 64) Cell))
(declare-const flags (Array (_ BitVec 64) Flag))
(declare-const atoms (Array (_ BitVec 64) Atom))
"#;

fn declared(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .source_constant_for_value(name)
        .expect("declared array")
        .0
}

fn direct_read(name: &str, spelling: &str) -> (Executor, Model, TermId) {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(DECLARATIONS).expect("valid declarations");
    exec.execute_all(&commands).expect("declarations execute");
    let array = declared(&exec, name);
    let Sort::Array(sort) = exec.ctx.terms.sort(array).clone() else {
        unreachable!()
    };
    let index = exec.ctx.terms.mk_bitvec(BigInt::from(0), 64);
    let read = exec.ctx.terms.mk_select(array, index);
    let mut model = empty_model();
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(
            array,
            ArrayInterpretation {
                index_sort: Some(sort.index_sort.clone()),
                element_sort: Some(sort.element_sort.clone()),
                default: Some(spelling.to_string()),
                stores: Vec::new(),
            },
        )]),
        ..Default::default()
    });
    (exec, model, read)
}

#[test]
fn typed_direct_array_read_refuses_nonnullary_constructor_text() {
    let (exec, model, read) = direct_read("cells", "(Mk #x2a)");
    let TermData::App(_, arguments) = exec.ctx.terms.get(read) else {
        unreachable!()
    };
    assert_eq!(
        exec.evaluate_select(&model, arguments[0], arguments[1]),
        EvalValue::Element("(Mk #x2a)".to_string()),
        "exercise the actual raw text producer"
    );
    let before = format!("{model:?}");
    assert!(IndependentModelView::new(&exec, &model)
        .array_select_value(read)
        .is_none());
    assert_eq!(format!("{model:?}"), before);
}

#[test]
fn typed_direct_array_read_retains_nullary_datatype() {
    let (exec, model, read) = direct_read("flags", "On");
    assert!(matches!(
        IndependentModelView::new(&exec, &model).array_select_value(read),
        Some(ModelValue::Datatype { ctor, args }) if ctor == "On" && args.is_empty()
    ));
}

#[test]
fn typed_direct_array_read_retains_non_datatype_atom() {
    let (exec, model, read) = direct_read("atoms", "@Atom!kept");
    assert!(matches!(
        IndependentModelView::new(&exec, &model).array_select_value(read),
        Some(ModelValue::Uninterpreted(value)) if value == "@Atom!kept"
    ));
}

fn poisoned_alias_fixture(conflict: bool) -> (Executor, Model, TermId, TermId) {
    let rhs = if conflict { "#x2b" } else { "#x2a" };
    let input = format!(
        r#"
        (set-logic ALL)
        (declare-datatype Cell ((Mk (number (_ BitVec 8)))))
        (declare-const a (Array (_ BitVec 64) Cell))
        (declare-const b (Array (_ BitVec 64) Cell))
        (assert (= a b))
        (assert (= (select a #x8000000000000001) (Mk #x2a)))
        (assert (= (select b #x8000000000000001) (Mk {rhs})))
    "#
    );
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(&input).expect("valid residual fixture"))
        .expect("declarations and assertions execute");
    let a = declared(&exec, "a");
    let b = declared(&exec, "b");
    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    for array in [a, b] {
        arrays.array_values.insert(
            array,
            ArrayInterpretation {
                index_sort: Some(Sort::bitvec(64)),
                element_sort: Some(Sort::Uninterpreted("Cell".to_string())),
                default: None,
                stores: vec![("#x8000000000000001".to_string(), "(Mk #x00)".to_string())],
            },
        );
        arrays.read_conflicted.insert(array);
    }
    model.array_model = Some(arrays);
    (exec, model, a, b)
}

#[test]
fn typed_direct_array_read_allows_replayed_poisoned_free_array_completion() {
    let (mut exec, mut model, a, b) = poisoned_alias_fixture(false);
    let raw_before = format!("{:?}", model.array_model);
    let view = IndependentModelView::new(&exec, &model);
    assert!(view.leaf_value(a).is_none() && view.leaf_value(b).is_none());
    let (verdict, completion) =
        confirm_model_with_array_completion(&exec.ctx.terms, &view, &exec.ctx.assertions)
            .into_parts();
    assert!(matches!(verdict, GateVerdict::ConfirmedSat), "{verdict:?}");
    let assignments = completion
        .expect("residual must materialize and replay a witness")
        .into_assignments()
        .expect("bounded stamped array assignments");
    assert_eq!(
        assignments.len(),
        2,
        "both alias members need the checked owner"
    );
    model
        .install_residual_arrays(&exec.ctx, assignments)
        .expect("current scope installs");
    assert_eq!(
        format!("{:?}", model.array_model),
        raw_before,
        "poison is not cleared"
    );
    assert!(
        matches!(
            confirm_completed_model(
                &exec.ctx.terms,
                &IndependentModelView::new(&exec, &model),
                &exec.ctx.assertions,
            ),
            GateVerdict::ConfirmedSat
        ),
        "the installed witness must replay all roots with residual recovery disabled"
    );
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn typed_direct_array_read_never_confirms_conflicting_same_index_values() {
    let (mut exec, model, a, b) = poisoned_alias_fixture(true);
    let before = format!("{model:?}");
    let view = IndependentModelView::new(&exec, &model);
    assert!(view.leaf_value(a).is_none() && view.leaf_value(b).is_none());
    let (verdict, completion) =
        confirm_model_with_array_completion(&exec.ctx.terms, &view, &exec.ctx.assertions)
            .into_parts();
    assert!(!matches!(verdict, GateVerdict::ConfirmedSat), "{verdict:?}");
    assert!(
        completion.is_none(),
        "contradictory cells cannot grant a witness"
    );
    assert_eq!(
        format!("{model:?}"),
        before,
        "refusal does not mutate the model"
    );
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(model);
    assert!(!matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}
