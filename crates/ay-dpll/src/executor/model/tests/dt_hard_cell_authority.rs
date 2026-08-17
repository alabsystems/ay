// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact hard-equality authority for opaque datatype model cells.

use super::dt_opaque_completion_scope::loaded_fixture;
use super::*;
use ay_model_check::{GateVerdict, ModelValue};

fn hard_cell_fixture(assertion: &str) -> (Executor, TermId, Sort) {
    let source = format!(
        r#"
        (set-logic ALL)
        (declare-datatype GuardCell
            ((GuardCell_mk (GuardCell_value (_ BitVec 8)))))
        (declare-const a (Array (_ BitVec 4) GuardCell))
        (declare-const b Bool)
        {assertion}
    "#,
    );
    let commands = ay_frontend::parse(&source).expect("valid hard-cell fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("hard-cell fixture executes");
    let sort = Sort::Uninterpreted("GuardCell".to_string());
    let select = executor
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(executor.ctx.terms.get(term), TermData::App(symbol, args)
                if symbol.name() == "select" && args.len() == 2)
                && executor.ctx.terms.sort(term) == &sort
        })
        .expect("fixture contains one datatype-valued select");
    (executor, select, sort)
}

fn opaque_cell_model(select: TermId, carrier: &str) -> Model {
    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(select, carrier.to_string());
    model.euf_model = Some(euf);
    model
}

#[test]
fn active_hard_select_equality_authorizes_literal_datatype_cell() {
    let (executor, select, sort) =
        hard_cell_fixture("(assert (= (select a #x0) (GuardCell_mk #x2a)))");
    let mut model = opaque_cell_model(select, "@GuardCell!11");
    let completions = executor.exact_datatype_cell_completions(&model, &[]);
    assert!(executor.exact_datatype_cell_completion(
        &completions,
        "@GuardCell!11",
        "(GuardCell_mk #x2a)",
        &sort,
    ));
    assert!(executor.apply_exact_datatype_cell_completions(&mut model, &completions));
    assert!(matches!(
        model.dt_pins.get(&select),
        Some(EvalValue::Element(value)) if value == "(GuardCell_mk #x2a)"
    ));
}

#[test]
fn active_assumption_equality_uses_the_same_exact_cell_authority() {
    let (mut executor, select, sort) =
        hard_cell_fixture("(assert (= (GuardCell_mk #x2a) (select a #x0)))");
    let equality = executor
        .ctx
        .assertions
        .pop()
        .expect("fixture has one asserted equality");
    let model = opaque_cell_model(select, "@GuardCell!14");
    let without_assumption = executor.exact_datatype_cell_completions(&model, &[]);
    assert!(without_assumption.is_empty());
    let with_assumption = executor.exact_datatype_cell_completions(&model, &[equality]);
    assert!(executor.exact_datatype_cell_completion(
        &with_assumption,
        "@GuardCell!14",
        "(GuardCell_mk #x2a)",
        &sort,
    ));
}

#[test]
fn conditional_negated_and_nonliteral_equalities_grant_no_cell_authority() {
    for assertion in [
        "(assert (or b (= (select a #x0) (GuardCell_mk #x2a))))",
        "(assert (not (= (select a #x0) (GuardCell_mk #x2a))))",
        "(assert (ite b (= (select a #x0) (GuardCell_mk #x2a)) true))",
        "(declare-const x (_ BitVec 8)) (assert (= (select a #x0) (GuardCell_mk x)))",
    ] {
        let (executor, select, sort) = hard_cell_fixture(assertion);
        let model = opaque_cell_model(select, "@GuardCell!12");
        let completions = executor.exact_datatype_cell_completions(&model, &[]);
        assert!(
            !executor.exact_datatype_cell_completion(
                &completions,
                "@GuardCell!12",
                "(GuardCell_mk #x2a)",
                &sort,
            ),
            "non-hard or nonliteral assertion unexpectedly granted authority: {assertion}"
        );
    }
}

#[test]
fn conflicting_active_cell_equalities_poison_shared_carrier() {
    let (executor, select, sort) = hard_cell_fixture(
        "(assert (and (= (select a #x0) (GuardCell_mk #x00)) (= (select a #x0) (GuardCell_mk #x01))))",
    );
    let model = opaque_cell_model(select, "@GuardCell!13");
    let completions = executor.exact_datatype_cell_completions(&model, &[]);
    for candidate in ["(GuardCell_mk #x00)", "(GuardCell_mk #x01)"] {
        assert!(
            !executor.exact_datatype_cell_completion(
                &completions,
                "@GuardCell!13",
                candidate,
                &sort,
            ),
            "conflicting hard facts must poison the carrier"
        );
    }
}

#[test]
fn quoted_datatype_names_never_authorize_bare_abstract_cells() {
    let mut executor = loaded_fixture();
    let sort = Sort::Uninterpreted("Quoted Cell".to_string());
    let term = executor.ctx.terms.mk_var("quoted_carrier", sort.clone());
    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(term, "@Quoted Cell!0".to_string());
    model.euf_model = Some(euf);
    model.dt_ground.insert(
        term,
        ModelValue::Datatype {
            ctor: "QuotedCell_mk".to_string(),
            args: Vec::new(),
        },
    );

    let completions = executor.exact_datatype_cell_completions(&model, &[]);
    assert!(!executor.exact_datatype_cell_completion(
        &completions,
        "@Quoted Cell!0",
        "QuotedCell_mk",
        &sort,
    ));
}

#[test]
fn independent_gate_rejects_congruent_uf_rows_with_distinct_structured_values() {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype GateBox ((GateBox_mk (GateBox_value (_ BitVec 8)))))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-fun f ((_ BitVec 8)) GateBox)
        (assert (not (= (f x) (f y))))
    "#,
    )
    .expect("valid synthetic gate fixture");
    let mut executor = Executor::new();
    executor.execute_all(&commands).expect("fixture executes");

    let mut x = None;
    let mut y = None;
    let mut apps = Vec::new();
    for term in executor.ctx.terms.term_ids() {
        match executor.ctx.terms.get(term) {
            TermData::Var(name, _) if name == "x" => x = Some(term),
            TermData::Var(name, _) if name == "y" => y = Some(term),
            TermData::App(symbol, _)
                if symbol.name() == "f"
                    || executor.ctx.dt_surface_name(symbol.name()) == Some("f") =>
            {
                apps.push(term);
            }
            _ => {}
        }
    }
    assert_eq!(apps.len(), 2);
    let mut model = bv_model(&[(x.unwrap(), 0), (y.unwrap(), 0)]);
    for (term, value) in apps.into_iter().zip([0u8, 1]) {
        model.dt_ground.insert(
            term,
            ModelValue::Datatype {
                ctor: "GateBox_mk".to_string(),
                args: vec![ModelValue::bitvec(BigInt::from(value), 8)],
            },
        );
    }
    executor.last_model = Some(model);

    assert!(!matches!(
        executor.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}
