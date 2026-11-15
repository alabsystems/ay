// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked interpretation replacement must retire only its obsolete view.

use super::*;

#[derive(Clone, Copy)]
enum Installer {
    Certificate,
    ModelCheck,
}

fn paired_model() -> Executor {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(set-option :produce-models true)
         (declare-fun f (Int) Int) (declare-fun g (Int) Int)
         (assert (= (f 0) 0)) (assert (= (f 1) 1))
         (assert (= (g 0) 0)) (assert (= (g 1) 2)) (check-sat)",
    )
    .expect("ground model input");
    let output = executor.execute_all(&commands).expect("ground solve");
    assert_eq!(output.last().map(String::as_str), Some("sat"));
    // Isolate an ordinary raw ground candidate from whichever certified model
    // completion the solver currently prefers. These total functions satisfy
    // every authored assertion; check that independently before reading them.
    let mut raw = Model::empty();
    let mut euf = ay_euf::EufModel::default();
    for (name, at_one) in [("f", "1"), ("g", "2")] {
        euf.function_tables.insert(
            name.to_string(),
            vec![
                (vec!["0".to_string()], "0".to_string()),
                (vec!["1".to_string()], at_one.to_string()),
            ],
        );
    }
    raw.euf_model = Some(euf);
    executor.last_model = Some(raw);
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
    assert!(executor.materialize_scalar_function_rows());
    let model = executor.last_model.as_ref().expect("ground model");
    assert!(model.materialized_scalar_functions.contains_key("f"));
    assert!(model.materialized_scalar_functions.contains_key("g"));
    executor
}

fn rational(value: i64) -> EvalValue {
    EvalValue::Rational(num_rational::BigRational::from_integer(value.into()))
}

fn install(executor: &mut Executor, owner: Installer, rows: &[(i64, i64)]) -> Option<()> {
    let mut model = executor.last_model.take().expect("staged model");
    let result = match owner {
        Installer::Certificate => model.install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            rows.iter()
                .map(|&(key, value)| (vec![rational(key)], rational(value)))
                .collect(),
            rational(3),
        ),
        Installer::ModelCheck => {
            let rows: Vec<_> = rows
                .iter()
                .map(|&(key, value)| {
                    (
                        vec![executor.ctx.terms.mk_int(key.into())],
                        executor.ctx.terms.mk_int(value.into()),
                    )
                })
                .collect();
            let default = executor.ctx.terms.mk_int(3.into());
            executor.install_model_check_total_uf(
                &mut model,
                "f",
                &[Sort::Int],
                &Sort::Int,
                &rows,
                default,
            )
        }
    };
    executor.last_model = Some(model);
    result
}

fn getter_values(executor: &mut Executor) -> Vec<String> {
    executor
        .execute_all(
            &ay_frontend::parse("(get-value ((f 0) (f 1) (f 7) (g 0) (g 1) (g 7)))")
                .expect("value query"),
        )
        .expect("model reads")
}

fn assert_replacement_reads(executor: &mut Executor) {
    let model = executor.last_model.as_ref().expect("replacement model");
    assert!(!model.materialized_scalar_functions.contains_key("f"));
    assert!(model.materialized_scalar_functions.contains_key("g"));
    assert!(executor.materialized_scalar_functions_current(model));
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
    let values = executor
        .execute_all(&ay_frontend::parse("(get-value ((f 7)))").expect("new default query"))
        .expect("new default read");
    assert!(values.last().expect("value").contains(" 3)"));
    assert!(!executor.model().contains("error"));
}

#[test]
fn certified_and_checked_replacements_retire_only_the_superseded_view() {
    for owner in [Installer::Certificate, Installer::ModelCheck] {
        let mut executor = paired_model();
        let untouched = executor
            .last_model
            .as_ref()
            .expect("model")
            .euf_model
            .as_ref()
            .expect("EUF")
            .function_tables["g"]
            .clone();
        assert_eq!(install(&mut executor, owner, &[(0, 0), (1, 1)]), Some(()));
        assert_eq!(
            executor
                .last_model
                .as_ref()
                .expect("model")
                .euf_model
                .as_ref()
                .expect("EUF")
                .function_tables["g"],
            untouched
        );
        assert_replacement_reads(&mut executor);
    }
}

#[test]
fn rejected_replacements_keep_rows_views_reads_and_model_identity() {
    for owner in [Installer::Certificate, Installer::ModelCheck] {
        let mut executor = paired_model();
        let before = getter_values(&mut executor);
        let model = executor.last_model.as_mut().expect("model");
        let epoch = model.seal_cegqi_uf_recompletion();
        let raw = model
            .euf_model
            .as_ref()
            .expect("EUF")
            .function_tables
            .clone();
        assert_eq!(install(&mut executor, owner, &[(0, 0), (0, 1)]), None);
        let model = executor.last_model.as_ref().expect("model");
        assert!(model.carries_cegqi_uf_recompletion(&epoch));
        assert_eq!(model.euf_model.as_ref().expect("EUF").function_tables, raw);
        assert!(model.materialized_scalar_functions.contains_key("f"));
        assert!(model.materialized_scalar_functions.contains_key("g"));
        assert!(executor.materialized_scalar_functions_current(model));
        assert_eq!(getter_values(&mut executor), before);
    }
}

#[test]
fn raw_cleanup_without_a_replacement_does_not_authorize_stale_reads() {
    let mut executor = paired_model();
    executor
        .last_model
        .as_mut()
        .expect("model")
        .remove_raw_uf_table_interpretation("f");
    assert!(executor
        .model()
        .contains("materialized scalar function model is stale"));
    assert!(getter_values(&mut executor)
        .last()
        .expect("refused reads")
        .contains("materialized scalar function model is stale"));
}

#[test]
fn certified_raw_cleanup_retains_the_owned_total_interpretation() {
    let mut executor = paired_model();
    assert_eq!(
        install(&mut executor, Installer::Certificate, &[(0, 0), (1, 1)]),
        Some(())
    );
    assert!(executor.materialize_scalar_function_rows());
    let model = executor.last_model.as_mut().expect("model");
    assert!(model.materialized_scalar_functions.contains_key("f"));
    model.remove_raw_uf_table_interpretation("f");
    assert!(model.has_certified_total_uf("f"));
    assert!(!model
        .euf_model
        .as_ref()
        .expect("EUF")
        .function_tables
        .contains_key("f"));
    assert_replacement_reads(&mut executor);
}
