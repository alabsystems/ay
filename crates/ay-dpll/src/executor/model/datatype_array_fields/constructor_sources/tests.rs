// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure constructor-source tests: no check-sat or completed-witness authority.

use super::*;
use ay_model_check::ArrayValue;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod fixtures;
use fixtures::*;

#[test]
fn nested_source_and_aggregate_select_preserve_all_cells_without_dt_ground_authority() {
    let mut f = fixture();
    let key = f.exec.ctx.terms.mk_bitvec(33.into(), 64);
    let read = app(&mut f.exec, "select", vec![f.rows, key], f.row_sort.clone());
    let mut model = Model::empty();
    model
        .dt_ground
        .insert(f.row, expected_row(&f.row_ctor, false));
    model
        .dt_ground
        .insert(read, expected_row(&f.row_ctor, false));
    assert!(same(
        &value(&f.exec, &model, f.rows).unwrap(),
        &expected_rows(&f.row_ctor)
    ));
    assert!(same(
        &value(&f.exec, &model, read).unwrap(),
        &expected_row(&f.row_ctor, true)
    ));
    let overwritten = app(
        &mut f.exec,
        "store",
        vec![f.rows, key, f.empty],
        f.rows_sort.clone(),
    );
    let read = app(
        &mut f.exec,
        "select",
        vec![overwritten, key],
        f.row_sort.clone(),
    );
    assert!(same(
        &value(&f.exec, &model, read).unwrap(),
        &expected_row(&f.row_ctor, false)
    ));
}

#[test]
fn scalar_select_keeps_exact_pin_without_requiring_complete_array_default() {
    let mut exec = Executor::new();
    let array = exec
        .ctx
        .terms
        .mk_var("partial", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
    let key = exec.ctx.terms.mk_bitvec(33.into(), 64);
    let read = app(&mut exec, "select", vec![array, key], Sort::bitvec(8));
    let mut model = Model::empty();
    model.bv_model = Some(ay_bv::BvModel {
        values: [(read, 9.into())].into_iter().collect(),
        term_to_bits: Default::default(),
        bool_overrides: Default::default(),
    });
    assert!(model.array_model.is_none());
    assert!(same(&value(&exec, &model, read).unwrap(), &word(9, 8)));
    assert!(value(&exec, &model, array).is_none());
}

#[test]
fn exact_constructor_metadata_is_required_and_completion_pins_cannot_replace_it() {
    let mut f = fixture();
    let TermData::App(_, args) = f.exec.ctx.terms.get(f.row).clone() else {
        unreachable!()
    };
    let bad_arity = app(&mut f.exec, &f.row_ctor, vec![args[0]], f.row_sort.clone());
    let wrong_sort = f.exec.ctx.terms.true_term();
    let bad_field = app(
        &mut f.exec,
        &f.row_ctor,
        vec![wrong_sort, args[1]],
        f.row_sort.clone(),
    );
    let foreign = app(&mut f.exec, "foreign_row", args.clone(), f.row_sort.clone());
    let selector = app(&mut f.exec, "len", args, f.row_sort.clone());
    let carrier = f.exec.ctx.terms.mk_var("opaque_row", f.row_sort.clone());
    for source in [bad_arity, bad_field, foreign, selector, carrier] {
        let mut model = Model::empty();
        model
            .dt_ground
            .insert(source, expected_row(&f.row_ctor, true));
        assert!(value(&f.exec, &model, source).is_none(), "{source:?}");
    }
    assert!(value(&f.exec, &Model::empty(), f.row).is_some());
}

#[test]
fn malformed_rational_index_is_refused_before_aggregate_select_comparison() {
    let mut f = fixture();
    let sort = Sort::array(Sort::Real, f.row_sort.clone());
    let base = app(&mut f.exec, "const-array", vec![f.empty], sort.clone());
    let key = f.exec.ctx.terms.mk_var("real_key", Sort::Real);
    let read_key = f.exec.ctx.terms.mk_var("read_key", Sort::Real);
    let stored = app(&mut f.exec, "store", vec![base, key, f.row], sort);
    let read = app(
        &mut f.exec,
        "select",
        vec![stored, read_key],
        f.row_sort.clone(),
    );
    let mut model = Model::empty();
    model.lra_model = Some(ay_lra::LraModel {
        values: [
            (key, num_rational::BigRational::new_raw(1.into(), 0.into())),
            (
                read_key,
                num_rational::BigRational::new_raw(2.into(), 0.into()),
            ),
        ]
        .into_iter()
        .collect(),
    });
    assert!(value(&f.exec, &model, read).is_none());
    model
        .lra_model
        .as_mut()
        .unwrap()
        .values
        .insert(key, num_rational::BigRational::from_integer(0.into()));
    model
        .lra_model
        .as_mut()
        .unwrap()
        .values
        .insert(read_key, num_rational::BigRational::from_integer(0.into()));
    assert!(same(
        &value(&f.exec, &model, read).unwrap(),
        &expected_row(&f.row_ctor, true)
    ));
}

#[test]
fn source_admission_requires_authorized_constructor_and_replay_detects_changed_cells() {
    let f = fixture();
    let class = ExactClass {
        cell_sort: f.exec.ctx.terms.sort(f.outer).clone(),
        carrier: "test".into(),
        members: [f.outer].into_iter().collect(),
        fields: vec![],
    };
    let model = Model::empty();
    let denied = f
        .exec
        .constructor_array_field_sources(
            &model,
            &class,
            &f.outer_ctor,
            0,
            &f.rows_sort,
            &HashSet::default(),
            &mut 0,
        )
        .unwrap();
    assert!(denied.exact.is_empty() && !denied.unresolved);
    let authorized = [f.outer].into_iter().collect();
    let admitted = f
        .exec
        .constructor_array_field_sources(
            &model,
            &class,
            &f.outer_ctor,
            0,
            &f.rows_sort,
            &authorized,
            &mut 0,
        )
        .unwrap();
    assert_eq!(admitted.exact, [f.rows]);
    assert!(!admitted.unresolved);
    let ModelValue::Array(expected) = expected_rows(&f.row_ctor) else {
        unreachable!()
    };
    let installed =
        normalize_array_value(&expected, &mut SemanticNormalizationBudget::new()).unwrap();
    let Sort::Array(sort) = &f.rows_sort else {
        unreachable!()
    };
    assert!(f.exec.installed_constructor_array_sources_match(
        &model,
        &[f.rows],
        sort,
        &installed,
        &mut 0,
        &mut TypedArrayParseBudget::new(),
        &mut SemanticNormalizationBudget::new()
    ));
    let changed = ArrayValue {
        default: expected_row(&f.row_ctor, false),
        store: vec![],
    };
    let changed = normalize_array_value(&changed, &mut SemanticNormalizationBudget::new()).unwrap();
    assert!(!f.exec.installed_constructor_array_sources_match(
        &model,
        &[f.rows],
        sort,
        &changed,
        &mut 0,
        &mut TypedArrayParseBudget::new(),
        &mut SemanticNormalizationBudget::new()
    ));
}

#[test]
fn authored_alias_and_known_ite_remain_exact_while_cycles_and_missing_conditions_refuse() {
    let mut f = fixture();
    let alias = f.exec.ctx.terms.mk_var("alias", f.rows_sort.clone());
    let equality = app(&mut f.exec, "=", vec![alias, f.rows], Sort::Bool);
    f.exec.independent_gate_authored_assertions = Some(vec![equality]);
    assert!(same(
        &value(&f.exec, &Model::empty(), alias).unwrap(),
        &expected_rows(&f.row_ctor)
    ));
    let condition = f.exec.ctx.terms.mk_var("condition", Sort::Bool);
    let conditional = f.exec.ctx.terms.mk_ite_raw(condition, alias, f.rows);
    assert!(value(&f.exec, &Model::empty(), conditional).is_none());
    let mut model = Model::empty();
    model.bool_overrides.insert(condition, true);
    assert!(same(
        &value(&f.exec, &model, conditional).unwrap(),
        &expected_rows(&f.row_ctor)
    ));
    let other = f.exec.ctx.terms.mk_var("cycle", f.rows_sort.clone());
    let cyclic = app(&mut f.exec, "=", vec![alias, other], Sort::Bool);
    f.exec.independent_gate_authored_assertions = Some(vec![cyclic]);
    assert!(value(&f.exec, &Model::empty(), alias).is_none());
    f.exec.independent_gate_authored_assertions = Some(vec![equality]);
    assert!(value(&f.exec, &Model::empty(), alias).is_some());
}

#[test]
fn recursive_source_work_and_depth_are_shared_and_refusal_does_not_memoize_success() {
    let mut f = fixture();
    let mut cost = 0;
    assert!(f
        .exec
        .exact_constructor_source_value(
            &Model::empty(),
            f.rows,
            &f.rows_sort,
            &mut cost,
            &mut TypedArrayParseBudget::new()
        )
        .is_some());
    assert!(cost > 10 && cost < MAX_EXACT_ARRAY_FIELD_TERMS);
    let mut exact = MAX_EXACT_ARRAY_FIELD_TERMS - cost;
    assert!(f
        .exec
        .exact_constructor_source_value(
            &Model::empty(),
            f.rows,
            &f.rows_sort,
            &mut exact,
            &mut TypedArrayParseBudget::new()
        )
        .is_some());
    assert_eq!(exact, MAX_EXACT_ARRAY_FIELD_TERMS);
    let mut short = MAX_EXACT_ARRAY_FIELD_TERMS - cost + 1;
    assert!(f
        .exec
        .exact_constructor_source_value(
            &Model::empty(),
            f.rows,
            &f.rows_sort,
            &mut short,
            &mut TypedArrayParseBudget::new()
        )
        .is_none());
    let key = f.exec.ctx.terms.mk_bitvec(1.into(), 64);
    let mut deep = f.rows;
    for _ in 0..=super::super::MAX_TYPED_ARRAY_DEPTH {
        deep = app(
            &mut f.exec,
            "store",
            vec![deep, key, f.empty],
            f.rows_sort.clone(),
        );
    }
    assert!(value(&f.exec, &Model::empty(), deep).is_none());
    assert!(value(&f.exec, &Model::empty(), f.rows).is_some());
}

#[test]
fn actual_evaluation_stop_is_sticky_and_fresh_source_attempt_recovers() {
    let mut f = fixture();
    let flag = Arc::new(AtomicBool::new(false));
    f.exec.set_interrupt(Arc::clone(&flag));
    let read = f.exec.begin_external_evaluation_read();
    flag.store(true, Ordering::Relaxed);
    assert!(value(&f.exec, &Model::empty(), f.rows).is_none());
    flag.store(false, Ordering::Relaxed);
    assert!(value(&f.exec, &Model::empty(), f.rows).is_none());
    assert!(f.exec.evaluation_stop_origin().is_some());
    drop(read);
    let _fresh = f.exec.begin_external_evaluation_read();
    assert!(same(
        &value(&f.exec, &Model::empty(), f.rows).unwrap(),
        &expected_rows(&f.row_ctor)
    ));
}

#[test]
fn borrowed_array_source_sort_refuses_before_clone_or_source_work() {
    let f = fixture();
    let model = Model::empty();
    let arena_len = f.exec.ctx.terms.len();
    let mut work = 0;
    let mut parse_budget = TypedArrayParseBudget::new();
    let oversized = ArraySort::new(Sort::Uninterpreted("x".repeat(257)), Sort::Bool);
    assert!(f
        .exec
        .exact_constructor_array_source(&model, f.rows, &oversized, &mut work, &mut parse_budget)
        .is_none());
    assert_eq!(work, 0);
    assert_eq!(f.exec.ctx.terms.len(), arena_len);

    // Build and dismantle iteratively: the fixture itself never clones or
    // recursively drops this caller-owned descriptor. Production preflight
    // must stop near its depth bound, before cloning the entire chain.
    let mut deep = Sort::Bool;
    for _ in 0..4096 {
        deep = Sort::Seq(Box::new(deep));
    }
    let deep = ArraySort::new(Sort::Bool, deep);
    let refused = f
        .exec
        .exact_constructor_array_source(&model, f.rows, &deep, &mut work, &mut parse_budget)
        .is_none();
    let mut remaining = deep.element_sort;
    while let Sort::Seq(element) = remaining {
        remaining = *element;
    }
    assert!(refused);
    assert_eq!(work, 0, "no source evaluation may follow schema refusal");
    assert_eq!(f.exec.ctx.terms.len(), arena_len);
    assert!(f.exec.evaluation_stop_origin().is_none());

    // Schema refusal does not spend the caller's value budget or poison a
    // subsequent valid source; retain the exact nested-array witness control.
    let Sort::Array(sort) = &f.rows_sort else {
        unreachable!()
    };
    let actual = f
        .exec
        .exact_constructor_array_source(&model, f.rows, sort, &mut work, &mut parse_budget)
        .unwrap();
    assert!(same(&actual, &expected_rows(&f.row_ctor)));
    assert!(work > 0);
    assert_eq!(f.exec.ctx.terms.len(), arena_len);
}
