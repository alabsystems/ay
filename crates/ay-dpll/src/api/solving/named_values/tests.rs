// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored name-to-value regressions, not retained compiler exports.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::api::Logic;
use ay_core::TermData;

mod integration;

fn parsed(text: &str) -> Solver {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_term_memory_limit(Some(64 * 1024 * 1024));
    solver.parse_smtlib2(text).unwrap();
    solver
}

#[test]
fn parsed_names_preserve_order_duplicates_and_exact_echoes_without_native_handles() {
    let solver = parsed(
        "(declare-const |x with space| Int)(declare-fun y () Bool)
         (declare-const |(+ x 1)| Int)",
    );
    assert!(solver.declared_variables().next().is_none());
    let size = solver.terms().len();
    let requests = solver
        .named_value_requests(&["y", "x with space", "y", "(+ x 1)"])
        .unwrap();
    assert_eq!(
        requests
            .iter()
            .map(|entry| entry.0.as_str())
            .collect::<Vec<_>>(),
        ["y", "|x with space|", "y", "|(+ x 1)|"]
    );
    assert_eq!(requests[0].1, requests[2].1);
    assert_eq!(
        model_parse::parse_get_value_output(
            "((y true)(|x with space| 7)(y true)(|(+ x 1)| 9))",
            &requests,
            solver.terms(),
            solver.executor.context(),
        ),
        Some(vec![
            ModelValue::Bool(true),
            ModelValue::Int(7.into()),
            ModelValue::Bool(true),
            ModelValue::Int(9.into())
        ]),
    );
    assert!(solver.named_value_requests(&["|x with space|"]).is_err());
    assert_eq!(solver.terms().len(), size);
}

#[test]
fn eager_record_request_uses_source_name_and_exact_registered_carrier() {
    let solver = parsed(
        "(declare-datatype R ((record (cells (Array (_ BitVec 2) (_ BitVec 8))))))
         (declare-const r R)",
    );
    let requests = solver.named_value_requests(&["r"]).unwrap();
    assert_eq!(requests[0].0, "r");
    assert!(matches!(
        solver.terms().get(requests[0].1),
        TermData::App(_, _)
    ));
    let response = "((r (record ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07))))";
    assert_eq!(
        model_parse::parse_get_value_output(
            response,
            &requests,
            solver.terms(),
            solver.executor.context()
        ),
        Some(vec![ModelValue::Datatype {
            constructor: "record".into(),
            args: vec![ModelValue::Array {
                default: Box::new(ModelValue::BitVec {
                    value: 7.into(),
                    width: 8
                }),
                stores: vec![]
            }]
        }]),
    );
    assert!(model_parse::parse_get_value_output(
        &response.replace("#x07", "#x0007"),
        &requests,
        solver.terms(),
        solver.executor.context()
    )
    .is_none());
}

#[test]
fn invalid_names_and_overloads_refuse_the_complete_request_batch() {
    let mut solver = parsed(
        "(declare-const good Int)(declare-const overloaded Int)
         (declare-const overloaded Bool)(declare-fun f (Int) Int)
         (define-fun fixed () Int 7)",
    );
    solver.try_declare_const("native", Sort::Bool).unwrap();
    let size = solver.terms().len();
    for name in ["missing", "overloaded", "f", "fixed", "native", "(f good)"] {
        assert!(
            solver.named_value_requests(&["good", name]).is_err(),
            "{name}"
        );
    }
    assert_eq!(solver.terms().len(), size);
}

#[test]
fn request_caps_are_admitted_before_lookup_and_owned_text() {
    let solver = parsed("");
    assert!(solver.named_value_requests(&vec!["missing"; 4097]).is_err());
    assert!(admit_names(&vec!["x"; 4096]).is_ok());
    let exact = "x".repeat(MAX_REQUEST_BYTES / 2 - 1);
    assert!(admit_names(&[&exact]).is_ok());
    assert!(admit_names(&[&exact, ""]).is_err());
    assert!(admit_names(&[&format!("{exact}x")]).is_err());
    assert!(solver.named_value_requests(&[]).unwrap().is_empty());
    assert_eq!(solver.terms().len(), parsed("").terms().len());
}

#[test]
fn sort_metadata_inspection_is_shared_bounded_and_does_not_normalize_widths() {
    let scalar = Sort::bitvec(u32::MAX);
    assert!(admit_sort(&scalar, 0, &mut 1).is_some());
    let mut deep = Sort::Bool;
    for _ in 0..MAX_SORT_DEPTH {
        deep = Sort::array(Sort::Bool, deep);
    }
    assert!(admit_sort(&deep, 0, &mut MAX_SORT_WORK).is_some());
    let deeper = Sort::array(Sort::Bool, deep);
    assert!(admit_sort(&deeper, 0, &mut MAX_SORT_WORK).is_none());
    let mut work = 2;
    assert!(admit_sort(&Sort::Bool, 0, &mut work).is_some());
    assert!(admit_sort(&Sort::Bool, 0, &mut work).is_some());
    assert!(admit_sort(&Sort::Bool, 0, &mut work).is_none());
    assert!(admit_sort(&Sort::Uninterpreted("abc".into()), 0, &mut 3).is_none());
    for (declared, actual) in [
        (Sort::Bool, Sort::Int),
        (Sort::bitvec(8), Sort::bitvec(16)),
        (
            Sort::Uninterpreted("old_R".into()),
            Sort::Uninterpreted("new_R".into()),
        ),
        (
            Sort::array(Sort::bitvec(2), Sort::Bool),
            Sort::array(Sort::bitvec(2), Sort::Int),
        ),
    ] {
        assert!(matching_sorts(&declared, &actual, &mut MAX_SORT_WORK).is_none());
        assert!(matching_sorts(&declared, &declared, &mut MAX_SORT_WORK).is_some());
    }
}

#[test]
fn scope_changes_keep_exact_live_lookup_and_no_result_remains_an_error() {
    let mut solver = parsed("");
    assert!(matches!(
        solver.try_get_named_values(&[]),
        Err(SolverError::NoResult)
    ));
    solver.try_push().unwrap();
    solver.parse_smtlib2("(declare-const x Int)").unwrap();
    let old = solver.named_value_requests(&["x"]).unwrap()[0].1;
    solver.try_pop().unwrap();
    assert!(solver.named_value_requests(&["x"]).is_err());
    solver.parse_smtlib2("(declare-const x Bool)").unwrap();
    let new = solver.named_value_requests(&["x"]).unwrap()[0].1;
    assert_ne!(old, new);
    assert_eq!(solver.terms().sort(new), &Sort::Bool);
    assert!(matches!(
        solver.try_get_named_values(&["x"]),
        Err(SolverError::NoResult)
    ));
}
