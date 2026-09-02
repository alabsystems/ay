// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};

fn byte_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8)))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn nullary_body(predicate: PredicateId) -> ClauseBody {
    ClauseBody::predicates_only(vec![(predicate, Vec::new())])
}

#[test]
fn slices_guarded_anchor_through_literal_true_nullary_wrappers() {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let state = problem.declare_predicate("state", vec![array.clone()]);
    let leaf = problem.declare_predicate("error_p4", Vec::new());
    let error = problem.declare_predicate("error", Vec::new());
    let memory = var("memory", array);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(state, vec![memory.clone()])],
            Some(ChcExpr::ne(
                ChcExpr::select(memory, ChcExpr::BitVec(0, 32)),
                ChcExpr::BitVec(0x2a, 8),
            )),
        ),
        ClauseHead::Predicate(leaf, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(leaf, Vec::new())], Some(ChcExpr::Bool(true))),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::query(nullary_body(error)));

    let slice = super::bounded_query_slice(&problem, None).expect("bounded error slice");
    assert_eq!(slice.sink_predicates, vec![leaf, error]);
    assert_eq!(slice.anchors.len(), 1);
    assert!(matches!(
        &slice.anchors[0].head,
        ClauseHead::Predicate(predicate, args) if *predicate == leaf && args.is_empty()
    ));
}

#[test]
fn admits_the_measured_model_checker_consumer_wrapper_width_but_caps_query_roots() {
    const MODEL_CHECKER_CONSUMER_LEAVES: usize = 115;
    let mut problem = ChcProblem::new();
    let error = problem.declare_predicate("error", Vec::new());
    for index in 0..MODEL_CHECKER_CONSUMER_LEAVES {
        let leaf = problem.declare_predicate(format!("error_p{index}"), Vec::new());
        problem.add_clause(HornClause::new(
            nullary_body(leaf),
            ClauseHead::Predicate(error, Vec::new()),
        ));
    }
    problem.add_clause(HornClause::query(nullary_body(error)));
    let slice = super::bounded_query_slice(&problem, None).expect("116-predicate sink closure");
    assert_eq!(
        slice.sink_predicates.len(),
        MODEL_CHECKER_CONSUMER_LEAVES + 1
    );

    let mut too_many_roots = ChcProblem::new();
    for index in 0..17 {
        let root = too_many_roots.declare_predicate(format!("root_{index}"), Vec::new());
        too_many_roots.add_clause(HornClause::query(nullary_body(root)));
    }
    assert!(super::bounded_query_slice(&too_many_roots, None).is_none());
}

#[test]
fn does_not_treat_nonlinear_constrained_or_nonnullary_input_as_transparent() {
    let mut problem = ChcProblem::new();
    let left = problem.declare_predicate("left", Vec::new());
    let right = problem.declare_predicate("right", Vec::new());
    let state = problem.declare_predicate("state", vec![ChcSort::Int]);
    let error = problem.declare_predicate("error", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(left, Vec::new()), (right, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(left, Vec::new())],
            Some(ChcExpr::eq(ChcExpr::Int(0), ChcExpr::Int(1))),
        ),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(state, vec![ChcExpr::Int(0)])]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::query(nullary_body(error)));

    let slice = super::bounded_query_slice(&problem, None).expect("bounded root slice");
    assert_eq!(slice.sink_predicates, vec![error]);
    assert_eq!(
        slice.anchors.len(),
        1,
        "only the guarded clause is a source"
    );
}

#[test]
fn nullary_wrapper_cycle_reaches_a_bounded_fixpoint() {
    let mut problem = ChcProblem::new();
    let left = problem.declare_predicate("left", Vec::new());
    let right = problem.declare_predicate("right", Vec::new());
    problem.add_clause(HornClause::new(
        nullary_body(left),
        ClauseHead::Predicate(right, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        nullary_body(right),
        ClauseHead::Predicate(left, Vec::new()),
    ));
    problem.add_clause(HornClause::query(nullary_body(right)));

    let slice = super::bounded_query_slice(&problem, None).expect("cycle must deduplicate");
    assert_eq!(slice.sink_predicates, vec![left, right]);
    assert!(slice.anchors.is_empty());
}
