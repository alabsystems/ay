// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

use super::*;
use crate::{ChcParser, ChcProblem};

// Source-derived, not a copied/emitted full harness: MODEL_CHECKER_CONSUMER ddbfd260cc48eef296bf0492382122d5e3d896d4,
// model-checker-consumer-compiler/src/codegen_ay/chc/call/codegen_call_vec_ops/resize.rs:224-310.
// new=65 crosses that producer's literal store-unrolling cap of 64. The forall
// intentionally says nothing about index 65; replacing it by whole-array
// equality to stores over b would be an unsound strengthening of this input.
fn problem(with_fill: bool) -> ChcProblem {
    let prefix = "(=> (bvult i (_ bv2 64)) (= (select a i) (select b i)))";
    let suffix = "(=> (and (bvuge i (_ bv2 64)) (bvult i (_ bv65 64))) (= (select a i) fill))";
    let body = if with_fill {
        format!("(and {prefix} {suffix})")
    } else {
        prefix.into()
    };
    ChcParser::parse(&format!(
        r#"
        (set-logic HORN)
        (declare-var a (Array (_ BitVec 64) Bool))
        (declare-var b (Array (_ BitVec 64) Bool))
        (declare-var fill Bool)
        (declare-rel P ((Array (_ BitVec 64) Bool)))
        (rule (=> (forall ((i (_ BitVec 64))) {body}) (P a)))
        (query P)
    "#
    ))
    .unwrap()
}

fn source_env(a: &[bool]) -> Map<String, SmtValue> {
    let mut env = Map::default();
    env.insert("a".into(), array(64, a.iter().copied()));
    env.insert("b".into(), array(64, [true, false]));
    env.insert("fill".into(), SmtValue::Bool(true));
    env
}

#[test]
fn public_parser_retains_prefix_fill_at64_and_freedom_at65() {
    let problem = problem(true);
    assert!(!problem.has_stripped_body_forall());
    let result = problem.clauses()[0].body.constraint.as_ref().unwrap();
    let mut values = vec![true; 66];
    values[1] = false;
    for tail in [false, true] {
        values[65] = tail;
        assert_eq!(
            evaluate_expr(result, &source_env(&values)),
            Some(SmtValue::Bool(true))
        );
    }
    for violated in [0, 1, 2, 64] {
        values[violated] = !values[violated];
        assert_eq!(
            evaluate_expr(result, &source_env(&values)),
            Some(SmtValue::Bool(false))
        );
        values[violated] = !values[violated];
    }
}

#[test]
fn public_missing_fill_preserves_only_prefix_and_does_not_invent_value64() {
    let problem = problem(false);
    assert!(!problem.has_stripped_body_forall());
    let result = problem.clauses()[0].body.constraint.as_ref().unwrap();
    let mut values = vec![false; 66];
    values[0] = true;
    for arbitrary in [false, true] {
        values[64] = arbitrary;
        assert_eq!(
            evaluate_expr(result, &source_env(&values)),
            Some(SmtValue::Bool(true))
        );
    }
    values[0] = false;
    assert_eq!(
        evaluate_expr(result, &source_env(&values)),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn scalar_bitvector_fill_keeps_exact_width_and_source_binding() {
    let input = r#"(set-logic HORN)
        (declare-var a (Array (_ BitVec 64) (_ BitVec 129)))
        (declare-var fill (_ BitVec 129))
        (declare-rel P ((Array (_ BitVec 64) (_ BitVec 129))))
        (rule (=> (forall ((i (_ BitVec 64)))
          (=> (bvult i (_ bv2 64)) (= fill (select a i)))) (P a)))
        (query P)"#;
    let problem = ChcParser::parse(input).unwrap();
    assert!(!problem.has_stripped_body_forall());
    let result = problem.clauses()[0].body.constraint.as_ref().unwrap();
    let mut env = Map::default();
    env.insert("fill".into(), SmtValue::BitVec(1u128 << 127, 129));
    env.insert(
        "a".into(),
        SmtValue::ConstArray(Box::new(SmtValue::BitVec(1u128 << 127, 129))),
    );
    assert_eq!(evaluate_expr(result, &env), Some(SmtValue::Bool(true)));
    env.insert("fill".into(), SmtValue::BitVec(0, 129));
    assert_eq!(evaluate_expr(result, &env), Some(SmtValue::Bool(false)));
}
