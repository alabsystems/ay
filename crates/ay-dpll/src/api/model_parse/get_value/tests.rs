// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort, Term};
use num_bigint::BigInt;

fn decode(solver: &Solver, output: &str, terms: &[Term]) -> Option<Vec<ModelValue>> {
    let requests: Vec<_> = terms
        .iter()
        .map(|term| (solver.executor.format_term(term.id()), term.id()))
        .collect();
    parse_get_value_output(output, &requests, solver.terms(), solver.executor.context())
}

#[test]
fn batch_authenticates_every_echo_and_preserves_request_order() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let y = solver.try_declare_const("y", Sort::Int).unwrap();
    assert_eq!(
        decode(&solver, "((x 7) (y 9))", &[x, y]),
        Some(vec![
            ModelValue::Int(BigInt::from(7)),
            ModelValue::Int(BigInt::from(9)),
        ])
    );
    for invalid in [
        "((y 7) (x 9))",
        "((x 7) (x 9))",
        "((x 7))",
        "((x 7 8) (y 9))",
        "((x 7) (y 9)) ()",
    ] {
        assert!(decode(&solver, invalid, &[x, y]).is_none(), "{invalid}");
    }
}

#[test]
fn one_bad_value_refuses_the_entire_batch() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let y = solver.try_declare_const("y", Sort::bitvec(8)).unwrap();
    for invalid in [
        "((x 7) (y #b1))",
        "((x 7) (y unknown))",
        "((x true) (y #x09))",
    ] {
        assert!(decode(&solver, invalid, &[x, y]).is_none(), "{invalid}");
    }
}

#[test]
fn quoted_requests_are_compared_as_smt_terms() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver
        .try_declare_const("x with space", Sort::String)
        .unwrap();
    assert_eq!(
        decode(&solver, "((|x with space| \"(;)|\"))", &[x]),
        Some(vec![ModelValue::String("(;)|".into())])
    );
    assert!(decode(&solver, "((|wrong name| \"(;)|\"))", &[x]).is_none());
}

fn record() -> DatatypeSort {
    DatatypeSort {
        name: "Record".into(),
        constructors: vec![DatatypeConstructor {
            name: "record".into(),
            fields: vec![DatatypeField {
                name: "cells".into(),
                sort: Sort::array(Sort::bitvec(2), Sort::bitvec(8)),
            }],
        }],
    }
}

#[test]
fn lowered_record_carrier_recovers_registered_array_field_sort() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let record = record();
    solver.try_declare_datatype(&record).unwrap();
    let x = solver
        .try_declare_const("x", Sort::Datatype(record))
        .unwrap();
    assert!(matches!(
        solver.terms().sort(x.id()),
        Sort::Uninterpreted(_)
    ));
    let output = "((x (record (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07) (_ bv3 2) (_ bv9 8)))))";
    assert_eq!(
        decode(&solver, output, &[x]),
        Some(vec![ModelValue::Datatype {
            constructor: "record".into(),
            args: vec![ModelValue::Array {
                default: Box::new(ModelValue::BitVec {
                    value: 7.into(),
                    width: 8
                }),
                stores: vec![(
                    ModelValue::BitVec {
                        value: 3.into(),
                        width: 2
                    },
                    ModelValue::BitVec {
                        value: 9.into(),
                        width: 8
                    }
                )],
            }],
        }])
    );
    assert!(decode(&solver, &output.replace("(_ bv9 8)", "(_ bv9 16)"), &[x]).is_none());
}

#[test]
#[ntest::timeout(10_000)]
fn public_get_value_retains_complete_registered_record() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_term_memory_limit(Some(64 * 1024 * 1024));
    let record = record();
    solver.try_declare_datatype(&record).unwrap();
    let seven = solver.try_bv_const(7, 8).unwrap();
    let cells = solver.try_const_array(Sort::bitvec(2), seven).unwrap();
    let value = solver
        .try_datatype_constructor(&record, "record", &[cells])
        .unwrap();
    let x = solver
        .try_declare_const("x", Sort::Datatype(record))
        .unwrap();
    let equality = solver.try_eq(x, value).unwrap();
    solver.try_assert_term(equality).unwrap();
    assert!(solver
        .try_check_sat_with_timeout(std::time::Duration::from_secs(2))
        .unwrap()
        .is_sat());
    assert_eq!(
        solver.try_get_value(x).unwrap(),
        ModelValue::Datatype {
            constructor: "record".into(),
            args: vec![ModelValue::Array {
                default: Box::new(ModelValue::BitVec {
                    value: 7.into(),
                    width: 8
                }),
                stores: vec![],
            }],
        }
    );
}

#[test]
fn admission_limits_apply_to_the_whole_batch_before_parsing() {
    let mut admission = admission::Admission::new();
    assert!(admission.admit(&" ".repeat(admission::MAX_BYTES)).is_some());
    assert!(admission.admit(" ").is_none());
    let mut admission = admission::Admission::new();
    assert!(admission
        .admit(&"x ".repeat(admission::MAX_NODES / 2))
        .is_some());
    assert!(admission
        .admit(&"x ".repeat(admission::MAX_NODES / 2))
        .is_some());
    assert!(admission.admit("x").is_none());
}

#[test]
fn admission_checks_depth_without_counting_quoted_or_commented_parens() {
    let at_limit = format!(
        "{}x{}",
        "(".repeat(admission::MAX_DEPTH),
        ")".repeat(admission::MAX_DEPTH)
    );
    assert!(admission::Admission::new().admit(&at_limit).is_some());
    assert!(admission::Admission::new()
        .admit(&format!("({at_limit})"))
        .is_none());
    for valid in [r#"("((;" |((;|) ; ((("#, r#"("a""((" |a\|((|)"#] {
        assert!(
            admission::Admission::new().admit(valid).is_some(),
            "{valid}"
        );
    }
    for invalid in ["(()", ")(", "\"unfinished", "|unfinished\\|"] {
        assert!(
            admission::Admission::new().admit(invalid).is_none(),
            "{invalid}"
        );
    }
}

/// THE PREFLIGHT MUST ADMIT AY'S OWN OUTPUT.
///
/// An array model prints as a left-nested `(store (store … ) i v)` chain, so
/// its LEXICAL depth is its entry count. A fully-expanded `(Array (_ BitVec 8)
/// _)` — every one of the 256 byte indices pinned, which is exactly what a
/// finite-domain-expanded `forall` over a `BV8` binder produces — is ~258 deep.
///
/// At the old bound of 128 the preflight refused it, `try_get_model_map` turned
/// that into `ModelGenerationFailed`, and the bridge reported `model extraction
/// failed: …` INSTEAD OF the `sat` the solver had decided (trust shape
/// `ABVFP`). A value `(get-model)` will print must be one `(get-value)` can
/// read back.
#[test]
fn admission_accepts_a_fully_expanded_byte_indexed_array_model() {
    let mut text =
        String::from("((as const (Array (_ BitVec 8) (_ BitVec 64))) #x0000000000000000)");
    for index in 0u32..256 {
        text = format!("(store {text} #x{index:02x} #x0000000000000001)");
    }
    assert!(
        admission::Admission::new().admit(&text).is_some(),
        "a 256-entry byte-indexed array model must survive the preflight"
    );
}

#[test]
fn adjacent_lexer_tokens_cannot_bypass_node_admission() {
    for token in ["#b1", ":a", "0x"] {
        let text = format!("({})", token.repeat(admission::MAX_NODES));
        assert!(text.len() < admission::MAX_BYTES);
        assert!(
            admission::Admission::new().admit(&text).is_none(),
            "{token}"
        );
    }
}

#[test]
fn empty_and_oversized_batches_are_explicit() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    assert_eq!(decode(&solver, "()", &[]), Some(vec![]));
    let x = solver.try_declare_const("x", Sort::Bool).unwrap();
    assert!(decode(&solver, "()", &vec![x; MAX_GET_VALUE_TERMS + 1]).is_none());
}
