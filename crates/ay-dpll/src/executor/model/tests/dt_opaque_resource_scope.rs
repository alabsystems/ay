// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Descriptor and arity boundaries for opaque datatype completion.

use super::*;
use ay_model_check::ModelValue;

fn nested_array_sort(depth: usize) -> Sort {
    let mut sort = Sort::Bool;
    for _ in 0..depth {
        sort = Sort::array(Sort::Bool, sort);
    }
    sort
}

#[test]
fn ordinary_uf_preflights_raw_arity_and_borrowed_sort_descriptors() {
    let mut executor = dt_opaque_completion_scope::loaded_fixture();
    let source_app = executor
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(executor.ctx.terms.get(term), TermData::App(symbol, _)
                if symbol.name() == "guard_cell_f")
        })
        .expect("fixture ordinary UF application");
    let TermData::App(symbol, args) = executor.ctx.terms.get(source_app).clone() else {
        unreachable!("selected term is an application");
    };
    let result_sort = executor.ctx.terms.sort(source_app).clone();
    let wide_args = vec![args[0]; 65];
    assert!(!executor.dt_completion_ordinary_uf_application(&symbol, &wide_args, source_app));

    let deep_arg = executor
        .ctx
        .terms
        .mk_var("deep_uf_arg", nested_array_sort(40));
    let forged = executor
        .ctx
        .terms
        .mk_app(symbol.clone(), vec![deep_arg], result_sort);
    assert!(!executor.dt_completion_ordinary_uf_application(&symbol, &[deep_arg], forged));
}

#[test]
fn array_select_preflights_index_descriptor_before_sort_equality() {
    let mut executor = dt_opaque_completion_scope::loaded_fixture();
    let cell_sort = Sort::Uninterpreted("GuardCell".to_string());
    let index_sort = nested_array_sort(40);
    let array = executor.ctx.terms.mk_var(
        "deep_index_array",
        Sort::array(index_sort.clone(), cell_sort.clone()),
    );
    let index = executor.ctx.terms.mk_var("deep_index", index_sort);
    let select = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![array, index], cell_sort);
    let TermData::App(symbol, args) = executor.ctx.terms.get(select) else {
        unreachable!("constructed select is an application");
    };
    assert!(!executor.dt_completion_array_select_application(symbol, args, select));
}

#[test]
fn scalar_only_roots_do_not_activate_opaque_collection_limits() {
    let commands = ay_frontend::parse("(set-logic ALL) (declare-datatype D ((K))) (assert true)")
        .expect("valid legacy datatype fixture");
    let mut executor = Executor::new();
    executor.execute_all(&commands).expect("fixture executes");
    let truth = executor.ctx.terms.true_term();
    executor.ctx.assertions.resize(1025, truth);

    let preflight = executor
        .preflight_opaque_dt_collection(&[])
        .expect("legacy no-opaque path must not inherit strict root caps");
    assert!(!preflight.is_strict());
}

#[test]
fn datatype_cell_authority_has_an_aggregate_value_budget() {
    let mut executor = dt_opaque_completion_scope::loaded_fixture();
    let sort = Sort::Uninterpreted("GuardCell".to_string());
    let oversized_value = ModelValue::Datatype {
        ctor: "GuardCell_mk".to_string(),
        args: vec![ModelValue::Bool(false); 1000],
    };
    let mut model = empty_model();
    let mut euf = EufModel::default();
    for index in 0..400 {
        let term = executor
            .ctx
            .terms
            .mk_var(format!("authority_row_{index}"), sort.clone());
        euf.term_values.insert(term, format!("@GuardCell!{index}"));
        model.dt_ground.insert(term, oversized_value.clone());
    }
    model.euf_model = Some(euf);

    assert!(executor
        .exact_datatype_cell_completions(&model, &[])
        .is_empty());
}

#[test]
fn datatype_cell_authority_rejects_nonterm_assumption_roots_without_panicking() {
    let executor = dt_opaque_completion_scope::loaded_fixture();
    let mut model = empty_model();
    model.euf_model = Some(EufModel::default());
    let marker = TermId(u32::MAX - 7);
    assert!(executor.ctx.terms.entry_stamp(marker).is_none());
    assert!(executor
        .exact_datatype_cell_completions(&model, &[marker])
        .is_empty());
}
