// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_frontend::parse;

use super::{Executor, Model};
use crate::executor_types::SolveResult;

#[test]
fn seq_argument_and_result_cells_use_aligned_source_terms() {
    let mut exec = Executor::new();
    let seq = Sort::Seq(Box::new(Sort::Int));
    let arg = exec.ctx.terms.mk_var("seq-table-arg", seq.clone());
    let app = exec.ctx.terms.mk_app(
        Symbol::Named("seq_table_f".to_string()),
        vec![arg],
        seq.clone(),
    );
    let table = vec![(
        vec!["@ay-seq!arg".to_string()],
        "@ay-seq!result".to_string(),
    )];

    let rewritten = exec
        .sequence_table_provenance_placeholders(
            "seq_table_f",
            std::slice::from_ref(&seq),
            &seq,
            &table,
            Some(std::slice::from_ref(&app)),
        )
        .expect("aligned provenance rewrites");
    assert_eq!(rewritten[0].0, vec![format!("@?{}", arg.0)]);
    assert_eq!(rewritten[0].1, format!("@?{}", app.0));
}

#[test]
fn missing_misaligned_or_wrong_source_provenance_fails_closed() {
    let mut exec = Executor::new();
    let seq = Sort::Seq(Box::new(Sort::Int));
    let arg = exec.ctx.terms.mk_var("seq-table-bad-arg", seq.clone());
    let wrong_app = exec.ctx.terms.mk_app(
        Symbol::Named("other_seq_table_f".to_string()),
        vec![arg],
        seq.clone(),
    );
    let table = vec![(vec!["opaque".to_string()], "opaque".to_string())];

    assert!(exec
        .sequence_table_provenance_placeholders(
            "seq_table_f",
            std::slice::from_ref(&seq),
            &seq,
            &table,
            None,
        )
        .is_err());
    assert!(exec
        .sequence_table_provenance_placeholders(
            "seq_table_f",
            std::slice::from_ref(&seq),
            &seq,
            &table,
            Some(&[]),
        )
        .is_err());
    assert!(exec
        .sequence_table_provenance_placeholders(
            "seq_table_f",
            std::slice::from_ref(&seq),
            &seq,
            &table,
            Some(std::slice::from_ref(&wrong_app)),
        )
        .is_err());
}

#[test]
fn get_model_with_missing_sequence_table_provenance_errors_without_opaque_output() {
    let commands = parse(
        "(set-logic ALL)\n\
         (declare-fun f ((Seq Int)) (Seq Int))",
    )
    .expect("valid declaration");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("declaration executes");

    let mut euf = ay_euf::EufModel::default();
    euf.function_tables.insert(
        "f".to_string(),
        vec![(
            vec!["@ay-seq!arg".to_string()],
            "@ay-seq!result".to_string(),
        )],
    );
    // Deliberately omit function_table_terms: no source application means
    // no authority to reinterpret either opaque class as a concrete Seq.
    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(Model {
        quantified_confirmation_seal: Default::default(),
        quantified_grant_model_seal: Default::default(),
        sat_model: Vec::new(),
        term_to_var: DetHashMap::default(),
        bool_overrides: DetHashMap::default(),
        euf_model: Some(euf),
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
        projection_ufs: Default::default(),
        certified_total_ufs: Default::default(),
        certified_const_interps: Default::default(),
        formula_neutral_function_defaults: Default::default(),
        completed_values: DetHashMap::default(),
        dt_ground: DetHashMap::default(),
        dt_pins: DetHashMap::default(),
        dt_array_field_classes: Vec::new(),
    });

    let output = exec.model();
    assert!(output.starts_with("(error \"model value for function f is not available:"));
    assert!(output.contains("no aligned source-term provenance"));
    assert!(
        !output.contains("@ay-seq"),
        "an error must not echo an opaque sequence token: {output}"
    );
}
