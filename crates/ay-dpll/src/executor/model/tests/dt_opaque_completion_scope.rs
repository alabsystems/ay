// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope and provenance guards for opaque datatype model completion.

use super::*;
use ay_model_check::{GateVerdict, ModelValue};

pub(super) fn loaded_fixture() -> Executor {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype GuardCell
            ((GuardCell_mk (GuardCell_value (_ BitVec 8)))))
        (declare-datatype CtorClash ((@CtorClash!0)))
        (declare-datatype UnsupportedCell
            ((UnsupportedCell_mk (UnsupportedCell_text String))))
        (declare-datatype QuotedCell ((|true|)))
        (declare-datatype |Quoted Cell| ((QuotedCell_mk)))
        (declare-datatype BranchCell
            ((BranchCell_mk (BranchCell_left GuardCell)
                            (BranchCell_right GuardCell))))
        (declare-fun guard_cell_f ((_ BitVec 8)) GuardCell)
        (declare-fun guard_cell_g ((_ BitVec 8)) GuardCell)
        (assert (= (guard_cell_f #x00) (guard_cell_g #x00)))
    "#,
    )
    .expect("valid datatype-completion fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("fixture declarations and assertion execute");
    executor
}

fn datatype_applications(executor: &Executor) -> Vec<(TermId, Symbol, Vec<TermId>)> {
    executor
        .ctx
        .terms
        .term_ids()
        .filter_map(|term| {
            executor.datatype_sort_name(executor.ctx.terms.sort(term))?;
            let TermData::App(symbol, args) = executor.ctx.terms.get(term) else {
                return None;
            };
            (executor.ctx.is_constructor(symbol.name()).is_none())
                .then(|| (term, symbol.clone(), args.clone()))
        })
        .collect()
}

#[test]
fn ordinary_opaque_apps_require_exact_live_noncanonical_declarations() {
    let mut executor = loaded_fixture();
    let applications = datatype_applications(&executor);
    assert_eq!(
        applications.len(),
        2,
        "fixture must expose its two declared UFs"
    );

    for (term, symbol, args) in &applications {
        assert!(
            executor.dt_completion_ordinary_uf_application(symbol, args, *term),
            "an exact live ordinary declaration remains eligible: {symbol}"
        );
        assert!(
            !executor.dt_completion_array_select_application(symbol, args, *term),
            "an ordinary declared function must not enter the array-select lane"
        );
    }

    let index = executor.ctx.terms.true_term();
    let canonical_lookalike = executor.ctx.terms.mk_app(
        Symbol::named("="),
        vec![index],
        Sort::Uninterpreted("GuardCell".to_string()),
    );
    let TermData::App(symbol, args) = executor.ctx.terms.get(canonical_lookalike) else {
        unreachable!("constructed canonical lookalike is an application");
    };
    assert!(!executor.dt_completion_ordinary_uf_application(symbol, args, canonical_lookalike));

    let cell_sort = Sort::Uninterpreted("GuardCell".to_string());
    executor
        .register_native_global_function_alias(
            "native-guard-cell".to_string(),
            "native-guard-cell".to_string(),
            vec![Sort::bitvec(8)],
            cell_sort.clone(),
        )
        .expect("native alias fixture registers");
    assert!(
        !executor
            .ctx
            .symbol_info_by_identity("native-guard-cell")
            .expect("native alias owns its private identity")
            .is_direct_source_declaration(),
        "fixture must exercise non-source provenance"
    );
    let arg = executor.ctx.terms.mk_bitvec(BigInt::zero(), 8);
    let native_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("native-guard-cell"), vec![arg], cell_sort);
    let TermData::App(symbol, args) = executor.ctx.terms.get(native_app) else {
        unreachable!("constructed native alias is an application");
    };
    assert!(
        !executor.dt_completion_ordinary_uf_application(symbol, args, native_app),
        "a non-source native alias must not enter datatype completion"
    );
}

#[test]
fn ordinary_opaque_apps_require_exact_declared_signature() {
    let executor = loaded_fixture();
    let (term, symbol, args) = datatype_applications(&executor)
        .into_iter()
        .next()
        .expect("ordinary fixture UF application");
    assert!(!executor.dt_completion_ordinary_uf_application(&symbol, &[], term));
    let wrong_arg = executor.ctx.terms.true_term();
    assert!(!executor.dt_completion_ordinary_uf_application(&symbol, &[wrong_arg], term));
    assert!(!executor.dt_completion_ordinary_uf_application(&symbol, &args, wrong_arg));
}

fn exact_select(executor: &mut Executor) -> (TermId, TermId, TermId, Sort) {
    let cell_sort = Sort::Uninterpreted("GuardCell".to_string());
    let index_sort = Sort::bitvec(4);
    let array = executor.ctx.terms.mk_var(
        "guard_array",
        Sort::array(index_sort.clone(), cell_sort.clone()),
    );
    let index = executor.ctx.terms.mk_bitvec(BigInt::zero(), 4);
    let exact_select = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![array, index],
        cell_sort.clone(),
    );
    (exact_select, array, index, cell_sort)
}

#[test]
fn canonical_array_select_requires_coherent_theory_identity() {
    let mut executor = loaded_fixture();
    let (exact_select, _, _, _) = exact_select(&mut executor);
    let TermData::App(exact_symbol, exact_args) = executor.ctx.terms.get(exact_select) else {
        unreachable!("constructed select is an application");
    };
    assert!(executor.dt_completion_array_select_application(
        exact_symbol,
        exact_args,
        exact_select
    ));
    assert!(!executor.dt_completion_ordinary_uf_application(
        exact_symbol,
        exact_args,
        exact_select
    ));

    let forged_select_owner = executor.ctx.terms.mk_fresh_named_var("select", Sort::Bool);
    executor
        .ctx
        .register_symbol("select".to_string(), forged_select_owner, Sort::Bool);
    let TermData::App(exact_symbol, exact_args) = executor.ctx.terms.get(exact_select) else {
        unreachable!("constructed select remains an application");
    };
    assert!(
        !executor.dt_completion_array_select_application(exact_symbol, exact_args, exact_select),
        "an ordinary owner forged at the canonical `select` identity must poison completion"
    );
}

#[test]
fn canonical_array_select_rejects_wrong_sort_and_indexed_lookalikes() {
    let mut executor = loaded_fixture();
    let (_, array, index, cell_sort) = exact_select(&mut executor);
    let bad_index = executor.ctx.terms.true_term();
    let wrong_index_select = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![array, bad_index],
        cell_sort.clone(),
    );
    let TermData::App(symbol, args) = executor.ctx.terms.get(wrong_index_select) else {
        unreachable!("constructed lookalike is an application");
    };
    assert!(!executor.dt_completion_array_select_application(symbol, args, wrong_index_select));

    let bool_array = executor
        .ctx
        .terms
        .mk_var("guard_bool_array", Sort::array(Sort::bitvec(4), Sort::Bool));
    let wrong_result_select = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![bool_array, index],
        cell_sort.clone(),
    );
    let TermData::App(symbol, args) = executor.ctx.terms.get(wrong_result_select) else {
        unreachable!("constructed lookalike is an application");
    };
    assert!(!executor.dt_completion_array_select_application(symbol, args, wrong_result_select));

    let indexed_select = executor.ctx.terms.mk_app(
        Symbol::indexed("select", vec![0]),
        vec![array, index],
        cell_sort.clone(),
    );
    let TermData::App(symbol, args) = executor.ctx.terms.get(indexed_select) else {
        unreachable!("constructed indexed lookalike is an application");
    };
    assert!(!executor.dt_completion_array_select_application(symbol, args, indexed_select));
}

#[test]
fn exact_fragment_rejects_unsupported_quoted_and_foreign_inline_schemas() {
    let executor = loaded_fixture();
    assert!(
        !executor.datatype_value_is_exactly_roundtrippable(&Sort::Uninterpreted(
            "UnsupportedCell".to_string()
        ))
    );
    assert!(!executor
        .datatype_value_is_exactly_roundtrippable(&Sort::Uninterpreted("QuotedCell".to_string())));
    assert!(executor
        .datatype_value_is_exactly_roundtrippable(&Sort::Uninterpreted("Quoted Cell".to_string())));
    assert!(!executor
        .datatype_value_is_exactly_roundtrippable(&Sort::Uninterpreted("BranchCell".to_string())));

    let foreign = Sort::Datatype(ay_core::DatatypeSort::new(
        "GuardCell",
        vec![ay_core::DatatypeConstructor::new(
            "GuardCell_mk",
            vec![ay_core::DatatypeField::new("GuardCell_value", Sort::Bool)],
        )],
    ));
    assert!(!executor.datatype_value_is_exactly_roundtrippable(&foreign));
}

#[test]
fn abstract_datatype_cell_replacement_requires_exact_class_provenance() {
    let mut executor = loaded_fixture();
    let cell_sort = Sort::Uninterpreted("GuardCell".to_string());
    let cell = executor
        .ctx
        .terms
        .mk_var("guard_cell_carrier", cell_sort.clone());
    let value = ModelValue::Datatype {
        ctor: "GuardCell_mk".to_string(),
        args: vec![ModelValue::bitvec(BigInt::zero(), 8)],
    };
    let candidate = "(GuardCell_mk #x00)";

    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(cell, "@GuardCell!7".to_string());
    model.euf_model = Some(euf);
    model.dt_ground.insert(cell, value);

    let completions = executor.exact_datatype_cell_completions(&model);
    assert!(executor.exact_datatype_cell_completion(
        &completions,
        "@GuardCell!7",
        candidate,
        &cell_sort
    ));
    assert!(!executor.exact_datatype_cell_completion(
        &completions,
        "|@GuardCell!7|",
        candidate,
        &cell_sort
    ));

    for invalid in [
        "@OtherCell!7",
        "@GuardCell!",
        "@GuardCell!07",
        "@GuardCell!x",
        "@GuardCell!+7",
        "@GuardCell!-7",
        "@GuardCell!7junk",
        "@GuardCell!999999999999999999999999999999999999999999999999999",
        "prefix@GuardCell!7",
        " @GuardCell!7",
        "@GuardCell!7 ",
        "(as @GuardCell!7 GuardCell)",
    ] {
        assert!(
            !executor.exact_datatype_cell_completion(&completions, invalid, candidate, &cell_sort),
            "invalid or wrong-sort carrier `{invalid}` must not be replaced"
        );
    }
    assert!(!executor.exact_datatype_cell_completion(
        &completions,
        "@GuardCell!7",
        "(GuardCell_mk #x01)",
        &cell_sort
    ));

    let mut missing_provenance = model.clone();
    missing_provenance.dt_ground.clear();
    let missing_completions = executor.exact_datatype_cell_completions(&missing_provenance);
    assert!(!executor.exact_datatype_cell_completion(
        &missing_completions,
        "@GuardCell!7",
        candidate,
        &cell_sort
    ));

    let clash_sort = Sort::Uninterpreted("CtorClash".to_string());
    let clash_cell = executor
        .ctx
        .terms
        .mk_var("constructor_identity_carrier", clash_sort.clone());
    let mut clash_model = empty_model();
    let mut clash_euf = EufModel::default();
    clash_euf
        .term_values
        .insert(clash_cell, "@CtorClash!0".to_string());
    clash_model.euf_model = Some(clash_euf);
    clash_model.dt_ground.insert(
        clash_cell,
        ModelValue::Datatype {
            ctor: "@CtorClash!0".to_string(),
            args: Vec::new(),
        },
    );
    let clash_completions = executor.exact_datatype_cell_completions(&clash_model);
    assert!(
        !executor.exact_datatype_cell_completion(
            &clash_completions,
            "@CtorClash!0",
            "@CtorClash!0",
            &clash_sort
        ),
        "a live constructor identity must never be reclassified as an abstract carrier"
    );
}

#[test]
fn abstract_datatype_class_authority_requires_all_rows_to_agree() {
    let mut executor = loaded_fixture();
    let sort = Sort::Uninterpreted("GuardCell".to_string());
    let first = executor.ctx.terms.mk_var("class_row_0", sort.clone());
    let second = executor.ctx.terms.mk_var("class_row_1", sort.clone());
    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(first, "@GuardCell!9".to_string());
    euf.term_values.insert(second, "@GuardCell!9".to_string());
    model.euf_model = Some(euf);
    model.dt_ground.insert(
        first,
        ModelValue::Datatype {
            ctor: "GuardCell_mk".to_string(),
            args: vec![ModelValue::bitvec(BigInt::zero(), 8)],
        },
    );
    model.dt_ground.insert(
        second,
        ModelValue::Datatype {
            ctor: "GuardCell_mk".to_string(),
            args: vec![ModelValue::bitvec(BigInt::one(), 8)],
        },
    );

    let completions = executor.exact_datatype_cell_completions(&model);
    assert!(!executor.exact_datatype_cell_completion(
        &completions,
        "@GuardCell!9",
        "(GuardCell_mk #x00)",
        &sort,
    ));
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

    let completions = executor.exact_datatype_cell_completions(&model);
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
