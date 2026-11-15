// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

fn array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool))
}

fn array_read_matches(array: &ChcVar, scalar: &ChcVar) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::Bool(false)),
        ChcExpr::var(scalar.clone()),
    )
}

fn add_impossible_query(problem: &mut ChcProblem, predicate: PredicateId, sorts: &[ChcSort]) {
    let actuals: Vec<_> = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| ChcExpr::var(ChcVar::new(format!("call{index}"), sort.clone())))
        .collect();
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, actuals.clone())],
        Some(ChcExpr::not(ChcExpr::eq(
            actuals[0].clone(),
            actuals[2].clone(),
        ))),
    )));
}

pub(super) fn head_collision() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let sorts = vec![ChcSort::Bool, array_sort(), ChcSort::Bool, ChcSort::Bool];
    let predicate = problem.declare_predicate("Source", sorts.clone());
    let x = ChcVar::new("x", ChcSort::Bool);
    let array = ChcVar::new("array", array_sort());
    // Position 3 is a legitimate source name, not an internal fresh name.
    let last = ChcVar::new("__dedup_a2_x", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::not(ChcExpr::var(last.clone())),
            array_read_matches(&array, &x),
        )),
        ClauseHead::Predicate(
            predicate,
            vec![
                ChcExpr::var(x.clone()),
                ChcExpr::var(array),
                ChcExpr::var(x),
                ChcExpr::var(last),
            ],
        ),
    ));
    add_impossible_query(&mut problem, predicate, &sorts);
    (problem, predicate)
}

pub(super) fn body_collision() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let sorts = vec![ChcSort::Bool, array_sort(), ChcSort::Bool];
    let predicate = problem.declare_predicate("Source", sorts.clone());
    let x = ChcVar::new("x", ChcSort::Bool);
    let array = ChcVar::new("array", array_sort());
    let local = ChcVar::new("__dedup_a2_x", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            // This exact equality permits the existing algebraic projection
            // fast path to eliminate the local without an SMT/MBP query.
            ChcExpr::eq(
                ChcExpr::var(local.clone()),
                ChcExpr::not(ChcExpr::var(x.clone())),
            ),
            ChcExpr::var(local),
            array_read_matches(&array, &x),
        ])),
        ClauseHead::Predicate(
            predicate,
            vec![
                ChcExpr::var(x.clone()),
                ChcExpr::var(array),
                ChcExpr::var(x),
            ],
        ),
    ));
    add_impossible_query(&mut problem, predicate, &sorts);
    (problem, predicate)
}
