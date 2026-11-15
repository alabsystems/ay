// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::records::Registry;
use crate::{CancellationToken, ChcExpr, ChcOp};
use ay_core::time::Instant;
use std::{sync::Arc, time::Duration};

fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
      (declare-fun f (Bool (_ BitVec 72)) (_ BitVec 136))
      (declare-fun |unused value| () (_ BitVec 1))
      (assert false) (check-sat)",
    )
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

#[test]
fn ordered_complete_snapshot_names_and_declarations_remain_uninterpreted() {
    let source = source();
    let token = CancellationToken::new();
    let live = control(&token);
    let retained = retain(&source, &live).unwrap();
    assert_eq!(
        names(&source, &live).unwrap().collect::<Vec<_>>(),
        ["f", "unused value"]
    );
    assert_eq!(
        retained.declarations(&live).unwrap(),
        source.function_declarations()
    );
    assert_eq!(
        copy_declarations(&source, &live).unwrap(),
        source.function_declarations()
    );
    let text = declarations_smtlib(&source, &live).unwrap();
    assert_eq!(text, "(declare-fun f (Bool (_ BitVec 72)) (_ BitVec 136))\n(declare-fun |unused value| () (_ BitVec 1))\n");
    assert!(!text.contains("define-fun"));
    assert!(retained.contains("unused value", &live).unwrap());
    assert!(!retained.contains("missing", &live).unwrap());
}

#[test]
fn snapshot_checks_actual_arguments_and_recorded_result_without_normalization() {
    let source = source();
    let token = CancellationToken::new();
    let live = control(&token);
    let retained = retain(&source, &live).unwrap();
    let arguments = [ChcSort::Bool, ChcSort::BitVec(72)];
    assert_eq!(
        retained.application("f", &arguments, &ChcSort::BitVec(136), &live),
        Some(ChcSort::BitVec(136))
    );
    for (name, args, result) in [
        ("missing", arguments.to_vec(), ChcSort::BitVec(136)),
        ("f", vec![], ChcSort::BitVec(136)),
        (
            "f",
            vec![ChcSort::Bool, ChcSort::BitVec(64)],
            ChcSort::BitVec(136),
        ),
        ("f", arguments.to_vec(), ChcSort::BitVec(128)),
        ("f", arguments.to_vec(), ChcSort::Bool),
        (
            "f",
            vec![ChcSort::Bool, ChcSort::Uninterpreted("BV72".into())],
            ChcSort::BitVec(136),
        ),
    ] {
        assert!(retained.application(name, &args, &result, &live).is_none());
    }
}

#[test]
fn all_emitted_branches_authenticate_uf_metadata_and_reject_name_capture() {
    let source = source();
    let token = CancellationToken::new();
    let live = control(&token);
    let registry = Registry::new(source.source_problem()).unwrap();
    let app = |result| {
        ChcExpr::FuncApp(
            "f".into(),
            result,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(ChcExpr::BitVec(1, 72)),
            ],
        )
    };
    assert_eq!(
        expression_sort(&source, &registry, &app(ChcSort::BitVec(136)), &live),
        Some(ChcSort::BitVec(136))
    );
    let wrong = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::BitVec(0, 128)),
            Arc::new(app(ChcSort::BitVec(128))),
        ],
    );
    assert!(expression_sort(&source, &registry, &wrong, &live).is_none());
    let capture = ChcExpr::var(crate::ChcVar::new("f", ChcSort::BitVec(136)));
    assert!(expression_sort(&source, &registry, &capture, &live).is_none());
    assert!(expression_sort(&source, &registry, &ChcExpr::BitVec(256, 8), &live).is_none());
}

#[test]
fn copy_allowance_is_prepaid_atomic_sticky_and_empty_cost_is_zero() {
    let source = source();
    let token = CancellationToken::new();
    let bytes = 3 * (64 * source.functions.work() + source.functions.copy_bytes());
    assert!(bytes < 64 * 1024 * 1024);
    let exact = control(&token);
    exact.bytes(64 * 1024 * 1024 - bytes).unwrap();
    assert!(copy_declarations(&source, &exact).is_some());
    assert!(exact.bytes(0).is_some());
    assert!(exact.bytes(1).is_none());
    let short = control(&token);
    short.bytes(64 * 1024 * 1024 - bytes + 1).unwrap();
    assert!(copy_declarations(&source, &short).is_none());
    assert!(short.poll().is_none());
    assert!(copy_declarations(&source, &short).is_none());
    let empty =
        QuantifiedChcProblem::parse_smtlib("(set-logic HORN)(assert false)(check-sat)").unwrap();
    let no_bytes = control(&token);
    no_bytes.bytes(64 * 1024 * 1024).unwrap();
    assert!(copy_declarations(&empty, &no_bytes).unwrap().is_empty());
    assert_eq!(declarations_smtlib(&empty, &no_bytes).unwrap(), "");
    assert!(names(&empty, &no_bytes).unwrap().next().is_none());
    assert!(retain(&empty, &no_bytes).is_some());
}

#[test]
fn every_helper_observes_cancelled_parent_and_only_fresh_control_can_retry() {
    let source = source();
    let token = CancellationToken::new();
    let stopped = control(&token);
    token.cancel();
    assert!(names(&source, &stopped).is_none());
    token.reset();
    assert!(retain(&source, &stopped).is_none());
    assert!(copy_declarations(&source, &stopped).is_none());
    assert!(declarations_smtlib(&source, &stopped).is_none());
    assert!(retain(&source, &control(&token)).is_some());
}
