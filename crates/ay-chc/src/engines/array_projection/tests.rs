// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pure structural/model-relation and injected control-flow tests. No solver
//! or real validator runs; `run` uses explicitly simulated validation results.

use super::projection::Projection;
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId, PredicateInterpretation,
};
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use std::sync::Arc;

mod controls;
mod lift;
mod projection;
mod run;

const R22_ARRAY: &str = include_str!(
    "../../../tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_true.smt2"
);
const R22_SCALAR: &str = include_str!(
    "../../../tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_false.smt2"
);

fn source() -> ChcProblem {
    ChcParser::parse(R22_ARRAY).unwrap()
}

fn array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32)))
}

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn project(problem: &ChcProblem) -> Projection {
    Projection::new(problem, &mut || true).expect("this source has erasable array columns")
}

fn model(problem: &ChcProblem) -> InvariantModel {
    let mut model = InvariantModel::new();
    for predicate in problem.predicates() {
        let vars: Vec<_> = predicate
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| ChcVar::new(format!("retained_{index}"), sort.clone()))
            .collect();
        let formula = match predicate.name.as_str() {
            "body" => ChcExpr::Op(
                ChcOp::BvULt,
                vec![
                    Arc::new(ChcExpr::Var(vars[0].clone())),
                    Arc::new(ChcExpr::BitVec(4, 64)),
                ],
            ),
            "error" => ChcExpr::Bool(false),
            _ => ChcExpr::Bool(true),
        };
        model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    }
    model
}

fn same_original(before: &ChcProblem, after: &ChcProblem) {
    assert_eq!(format!("{before:?}"), format!("{after:?}"));
    assert_eq!(before.normalized_input(), after.normalized_input());
    assert_eq!(
        before.normalized_input_sha256(),
        after.normalized_input_sha256()
    );
}

fn signature_problem(sorts: Vec<ChcSort>) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("p", sorts);
    problem
}

fn expected_args(problem: &ChcProblem, id: PredicateId, args: &[ChcExpr]) -> Vec<ChcExpr> {
    args.iter()
        .zip(&problem.get_predicate(id).unwrap().arg_sorts)
        .filter_map(|(argument, sort)| {
            (!matches!(sort, ChcSort::Array(..))).then(|| argument.clone())
        })
        .collect()
}

fn assert_fixed_erasure(source: &ChcProblem, reduced: &ChcProblem) {
    assert_eq!(source.predicates().len(), reduced.predicates().len());
    for (original, actual) in source.predicates().iter().zip(reduced.predicates()) {
        assert_eq!((actual.id, &actual.name), (original.id, &original.name));
        assert_eq!(
            actual.arg_sorts,
            original
                .arg_sorts
                .iter()
                .filter(|sort| !matches!(sort, ChcSort::Array(..)))
                .cloned()
                .collect::<Vec<_>>()
        );
        assert_eq!(reduced.lookup_predicate(&original.name), Some(original.id));
    }
    assert_eq!(source.clauses().len(), reduced.clauses().len());
    for (original, actual) in source.clauses().iter().zip(reduced.clauses()) {
        assert_eq!(actual.action_id, original.action_id);
        assert_eq!(actual.source_query_ordinal, original.source_query_ordinal);
        assert_eq!(actual.body.constraint, original.body.constraint);
        assert_eq!(actual.body.predicates.len(), original.body.predicates.len());
        for ((op, oa), (ap, aa)) in original.body.predicates.iter().zip(&actual.body.predicates) {
            assert_eq!(ap, op);
            assert_eq!(*aa, expected_args(source, *op, oa));
        }
        match (&original.head, &actual.head) {
            (ClauseHead::False, ClauseHead::False) => {}
            (ClauseHead::Predicate(op, oa), ClauseHead::Predicate(ap, aa)) => {
                assert_eq!(ap, op);
                assert_eq!(*aa, expected_args(source, *op, oa));
            }
            _ => panic!("the source head kind changed"),
        }
    }
}
