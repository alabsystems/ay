// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use crate::{ClauseBody, ClauseHead, HornClause};

#[path = "candidate_disjunct_tests/native.rs"]
mod native;

fn int_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn one_array_problem(constraint: impl FnOnce(ChcExpr) -> ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array()]);
    let array = ChcExpr::var(ChcVar::new("array", int_array()));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array.clone()])],
        Some(constraint(array)),
    )));
    problem
}

fn bad(array: ChcExpr, index: i128) -> ChcExpr {
    ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(index)), ChcExpr::Int(0))
}

fn candidates(problem: &ChcProblem, slots: usize) -> Option<Vec<QueryAnchoredGhostCandidate>> {
    query_anchored_ghost_candidates(problem, &GhostPairSpec::analyze(problem, slots))
}

fn evaluate(candidate: &QueryAnchoredGhostCandidate, index: i128, value: i128) -> bool {
    let env = [
        (candidate.vars[1].name.clone(), SmtValue::Int(index)),
        (candidate.vars[2].name.clone(), SmtValue::Int(value)),
    ]
    .into_iter()
    .collect();
    match crate::expr::evaluate_expr(&candidate.formula, &env) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("closed guarded scalar candidate required: {other:?}"),
    }
}

#[test]
fn old_exact_or_witness_now_requires_the_complete_two_anchor_conjunction() {
    // This is the exact old OR constraint, not a reduced or sampled witness.
    let problem = one_array_problem(|array| {
        ChcExpr::or(
            ChcExpr::ne(
                ChcExpr::select(array.clone(), ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ),
            ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(1)), ChcExpr::Int(0)),
        )
    });
    let original = problem
        .clauses()
        .last()
        .expect("query")
        .body
        .constraint
        .clone();
    let batch = candidates(&problem, 1).expect("both sufficient anchors");
    assert_eq!(batch.len(), 2);
    assert_eq!(
        problem.clauses().last().expect("query").body.constraint,
        original
    );
    assert!(batch.iter().all(|candidate| candidate.vars.len() == 3));
    for index in [0, 1, 2] {
        for value in [0, 1] {
            assert_eq!(
                batch
                    .iter()
                    .all(|candidate| evaluate(candidate, index, value)),
                index > 1 || value == 0
            );
        }
    }
    let two_slots = candidates(&problem, 2).expect("existing whole-query route retained");
    assert_eq!(two_slots.len(), 1);
    assert_eq!(two_slots[0].vars.len(), 5);
}

#[test]
fn nested_positive_or_leaves_are_complete_in_original_order() {
    let problem = one_array_problem(|array| {
        ChcExpr::Op(
            ChcOp::Or,
            vec![
                Arc::new(bad(array.clone(), 0)),
                Arc::new(ChcExpr::Op(
                    ChcOp::Or,
                    vec![Arc::new(bad(array.clone(), 1)), Arc::new(bad(array, 2))],
                )),
            ],
        )
    });
    let batch = candidates(&problem, 1).expect("all three leaves");
    assert_eq!(batch.len(), 3);
    for (position, candidate) in batch.iter().enumerate() {
        assert!(!evaluate(candidate, position as i128, 1));
        assert!(evaluate(candidate, 3, 1));
    }
}

#[test]
fn too_many_reads_in_any_one_leaf_discards_every_fallback_anchor() {
    let problem = one_array_problem(|array| {
        ChcExpr::or(
            bad(array.clone(), 2),
            ChcExpr::and(bad(array.clone(), 0), bad(array, 1)),
        )
    });
    assert!(candidates(&problem, 1).is_none());
}

#[test]
fn unsupported_array_leaf_discards_supported_sibling_anchors() {
    let problem = one_array_problem(|array| {
        ChcExpr::or_vec(vec![
            bad(array.clone(), 0),
            bad(array.clone(), 1),
            ChcExpr::eq(array, ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))),
        ])
    });
    assert!(candidates(&problem, 1).is_none());
}

#[test]
fn an_unrewriteable_false_leaf_is_not_silently_deleted_by_the_fallback() {
    let mut problem = one_array_problem(|array| ChcExpr::or(bad(array.clone(), 0), bad(array, 1)));
    let array = ChcExpr::var(ChcVar::new("array", int_array()));
    problem
        .clauses_mut()
        .last_mut()
        .expect("query")
        .body
        .constraint = Some(ChcExpr::or_vec(vec![
        bad(array.clone(), 0),
        bad(array, 1),
        ChcExpr::Bool(false),
    ]));
    assert!(candidates(&problem, 1).is_none());
}

#[test]
fn rewrite_budget_includes_the_failed_whole_attempt_and_every_branch() {
    let problem = one_array_problem(|array| ChcExpr::or(bad(array.clone(), 0), bad(array, 1)));
    let spec = GhostPairSpec::analyze(&problem, 1);
    // Whole attempt: NOT/OR/NE/select/index/value/NE/select/index = 9.
    // Each complete branch then uses the existing 5-node rewrite = 10.
    assert!(query_anchored_ghost_candidates_with_budget(&problem, &spec, 18).is_none());
    let exact = query_anchored_ghost_candidates_with_budget(&problem, &spec, 19)
        .expect("one shared 19-node allowance");
    assert_eq!(exact.len(), 2);
    assert!(query_anchored_ghost_candidates_with_budget(&problem, &spec, 10).is_none());
}

#[test]
fn decomposition_and_leaf_census_share_the_same_exhaustible_counter() {
    let problem = one_array_problem(|array| ChcExpr::or(bad(array.clone(), 0), bad(array, 1)));
    let clause = problem.clauses().last().expect("query");
    let constraint = clause.body.constraint.as_ref().expect("bad OR");
    let mut remaining = 8;
    let leaves = positive_disjuncts(constraint, &mut remaining, None).expect("exact split");
    assert_eq!(remaining, 0);
    assert_eq!(leaves.len(), 2);
    let source = &problem.predicates()[0];
    let spec = GhostPairSpec::analyze(&problem, 1);
    let positions = query_argument_positions(&clause.body.predicates[0].1, &source.arg_sorts)
        .expect("declared exact arguments");
    let layout = spec.preds.get(&source.id).expect("layout");
    assert!(local_index_reads(
        leaves[0],
        &positions,
        layout,
        1,
        &mut remaining,
        &mut || false
    )
    .is_none());
    let mut one_short = 7;
    assert!(positive_disjuncts(constraint, &mut one_short, None).is_none());
}

#[test]
fn cancelled_or_expired_control_withholds_the_entire_batch() {
    let problem = one_array_problem(|array| ChcExpr::or(bad(array.clone(), 0), bad(array, 1)));
    let spec = GhostPairSpec::analyze(&problem, 1);
    let token = CancellationToken::new();
    token.cancel();
    let end = Instant::now() + std::time::Duration::from_secs(20);
    assert!(query_anchored_ghost_candidates_controlled(&problem, &spec, &token, end).is_none());
    let fresh = CancellationToken::new();
    assert!(
        query_anchored_ghost_candidates_controlled(&problem, &spec, &fresh, Instant::now())
            .is_none()
    );
}

#[test]
fn excessive_positive_or_leaf_population_refuses_without_cap_renewal() {
    let problem = one_array_problem(|array| {
        ChcExpr::or_vec(
            (0..=MAX_PROPAGATED_CANDIDATES)
                .map(|index| bad(array.clone(), index as i128))
                .collect(),
        )
    });
    assert!(candidates(&problem, 1).is_none());
}
