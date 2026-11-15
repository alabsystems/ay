// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored, UNRUN controls. Structural and injected-control tests are not
//! safety evidence; `actual` separately invokes the real original validator.
//! These are synthetic CHC inputs, not typed MODEL_CHECKER_CONSUMER consumer qualification.

use super::projection::Projection;
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseHead, InvariantModel,
    PredicateId, PredicateInterpretation,
};
use std::sync::Arc;

mod actual;
mod controls;
mod derived_width;
mod lift;
mod pruned;
mod run;
mod static_hints;
mod static_hints_actual;
mod static_hints_controls;
mod static_hints_support;
mod structure;

fn source(expected: u32, exit: bool) -> ChcProblem {
    source_values(expected, exit, 9, 5, 1)
}

fn source_values(expected: u32, exit: bool, written: u32, initial: u32, key: u32) -> ChcProblem {
    let query = if exit {
        "(and (H a i) (bvuge i (_ bv4 64)))"
    } else {
        "(B a i)"
    };
    let text = format!(
        r#"
        (set-logic HORN)
        (declare-fun H ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
        (declare-fun B ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
        (assert (H ((as const (Array (_ BitVec 64) (_ BitVec 32))) (_ bv{initial} 32)) (_ bv0 64)))
        (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
          (=> (and (H a i) (bvult i (_ bv4 64)))
              (B (store a (_ bv{key} 64) (_ bv{written} 32)) i))))
        (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
          (=> (B a i) (H a (bvadd i (_ bv1 64))))))
        (assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
          (=> (and {query} (not (= (select a (_ bv1 64)) (_ bv{expected} 32)))) false)))
        (check-sat)
    "#
    );
    ChcParser::parse(&text).unwrap()
}

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn bv(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

fn operation(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(left), Arc::new(right)])
}

fn project(original: &ChcProblem) -> Projection<'_> {
    Projection::new(original, &mut || true).expect("finite observed cell")
}

/// A scalar candidate for the known fixture, not solver/verification evidence.
fn candidate(reduced: &ChcProblem) -> InvariantModel {
    let mut model = InvariantModel::new();
    for predicate in reduced.predicates() {
        let variables: Vec<_> = predicate
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| ChcVar::new(format!("candidate_{index}"), sort.clone()))
            .collect();
        let formula = match predicate.name.as_str() {
            "H" => {
                let cell = ChcExpr::var(variables[0].clone());
                let counter = ChcExpr::var(variables[1].clone());
                ChcExpr::or(
                    ChcExpr::and(
                        ChcExpr::eq(counter.clone(), bv(0, 64)),
                        ChcExpr::eq(cell.clone(), bv(5, 32)),
                    ),
                    ChcExpr::and_all(vec![
                        operation(ChcOp::BvUGe, counter.clone(), bv(1, 64)),
                        operation(ChcOp::BvULe, counter, bv(4, 64)),
                        ChcExpr::eq(cell, bv(9, 32)),
                    ]),
                )
            }
            "B" => ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(variables[0].clone()), bv(9, 32)),
                operation(ChcOp::BvULt, ChcExpr::var(variables[1].clone()), bv(4, 64)),
            ),
            "error" => ChcExpr::Bool(false),
            _ => ChcExpr::Bool(true),
        };
        model.set(
            predicate.id,
            PredicateInterpretation::new(variables, formula),
        );
    }
    model
}

fn same_source(before: &ChcProblem, after: &ChcProblem) {
    assert_eq!(format!("{before:?}"), format!("{after:?}"));
    assert_eq!(before.normalized_input(), after.normalized_input());
    assert_eq!(
        before.normalized_input_sha256(),
        after.normalized_input_sha256()
    );
}
