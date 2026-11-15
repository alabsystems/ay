// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtConstructors, ChcDtSelector, ChcVar, ClauseBody, HornClause};
use std::sync::Arc;

fn fixture() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let state = ChcVar::new("state", ChcSort::BitVec(8));
    let index = ChcVar::new("index", ChcSort::BitVec(8));
    let pred = problem.declare_predicate("P", vec![state.sort.clone()]);
    let lambda = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::Var(index)),
                Arc::new(ChcExpr::Var(state.clone())),
            ],
        ),
    )
    .unwrap();
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(pred, vec![ChcExpr::Var(state)])],
        Some(ChcExpr::eq(
            ChcExpr::select(lambda, ChcExpr::BitVec(3, 8)),
            ChcExpr::BitVec(4, 8),
        )),
    )));
    problem
}

fn assert_same(before: &ChcProblem, after: &ChcProblem) {
    let signatures = |problem: &ChcProblem| {
        problem
            .predicates()
            .iter()
            .map(|predicate| {
                (
                    predicate.id,
                    predicate.name.clone(),
                    predicate.arg_sorts.clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(signatures(before), signatures(after));
    assert_eq!(before.clauses().len(), after.clauses().len());
    for (left, right) in before.clauses().iter().zip(after.clauses()) {
        assert_eq!(left.body.predicates, right.body.predicates);
        assert_eq!(left.body.constraint, right.body.constraint);
        assert_eq!(left.action_id, right.action_id);
        match (&left.head, &right.head) {
            (crate::ClauseHead::False, crate::ClauseHead::False) => {}
            (crate::ClauseHead::Predicate(a, av), crate::ClauseHead::Predicate(b, bv)) => {
                assert_eq!(a, b);
                assert_eq!(av, bv);
            }
            _ => panic!("changed clause head"),
        }
    }
}

#[test]
fn array_lambda_bv_to_int_preserves_capture_and_predicate_vocabulary() {
    let problem = fixture();
    let result = Box::new(BvToIntAbstractor::new()).transform(problem.clone());
    assert_same(&problem, &result.problem);
}

#[test]
fn array_lambda_bitblast_preserves_capture_and_predicate_vocabulary() {
    let problem = fixture();
    let result = Box::new(BvToBoolBitBlaster::new()).transform(problem.clone());
    assert_same(&problem, &result.problem);
}

#[test]
fn array_lambda_dt_flatten_preserves_closed_template_types() {
    let mut problem = fixture();
    let pair = ChcSort::Datatype {
        name: "Pair".into(),
        constructors: ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "pair".into(),
            selectors: vec![
                ChcDtSelector {
                    name: "left".into(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "right".into(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };
    problem.declare_predicate("Q", vec![pair]);
    let result = Box::new(DtFlattener::new()).transform(problem.clone());
    assert_same(&problem, &result.problem);
}

#[test]
fn array_lambda_scalarization_preserves_unobserved_array_cells() {
    let mut problem = ChcProblem::new();
    let source = ChcVar::new(
        "source",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let pred = problem.declare_predicate("P", vec![source.sort.clone()]);
    let index = ChcVar::new("index", ChcSort::Int);
    let lambda = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::select(ChcExpr::Var(source.clone()), ChcExpr::Var(index)),
    )
    .unwrap();
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(pred, vec![ChcExpr::Var(source)])],
        Some(ChcExpr::eq(
            ChcExpr::select(lambda, ChcExpr::Int(0)),
            ChcExpr::Int(1),
        )),
    )));
    let before = problem.clone();
    assert!(problem
        .try_scalarize_int_indexed_const_array_selects_with_map()
        .is_none());
    assert_same(&before, &problem);
    assert!(problem.try_scalarize_property_directed_with_map().is_none());
    assert_same(&before, &problem);
    assert!(problem
        .try_scalarize_const_array_selects_with_map()
        .is_none());
    assert_same(&before, &problem);
}
