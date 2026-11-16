// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{
    CancellationToken, ChcExpr, ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::time::Instant;
use std::time::Duration;

fn source(declarations: ChcProblem, clauses: Vec<HornClause>) -> QuantifiedChcProblem {
    QuantifiedChcProblem::new(
        declarations,
        clauses
            .into_iter()
            .map(|clause| QuantifiedHornClause::new(clause, vec![]))
            .collect(),
    )
    .unwrap()
}

fn body(predicates: &[PredicateId]) -> ClauseBody {
    ClauseBody::predicates_only(predicates.iter().map(|p| (*p, vec![])).collect())
}

fn rule(head: PredicateId, predicates: &[PredicateId]) -> HornClause {
    HornClause::new(body(predicates), ClauseHead::Predicate(head, vec![]))
}

fn fact(head: PredicateId, constraint: ChcExpr) -> HornClause {
    HornClause::fact(constraint, head, vec![])
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn check(problem: &QuantifiedChcProblem, tree: &Derivation) {
    assert_ne!(tree.clause_indices, [] as [usize; 0]);
    assert_eq!(tree.clause_indices.len(), tree.premise_steps.len());
    let root = tree.clause_indices.len() - 1;
    let mut consumers = vec![0usize; tree.clause_indices.len()];
    for (step, (&index, children)) in tree
        .clause_indices
        .iter()
        .zip(&tree.premise_steps)
        .enumerate()
    {
        let clause = &problem.source_problem().clauses()[index];
        assert_eq!(matches!(clause.head, ClauseHead::False), step == root);
        assert_eq!(clause.body.predicates.len(), children.len());
        for ((wanted, _), &child) in clause.body.predicates.iter().zip(children) {
            assert!(child < step);
            consumers[child] += 1;
            assert!(
                matches!(&problem.source_problem().clauses()[tree.clause_indices[child]].head,
                ClauseHead::Predicate(head, _) if head == wanted)
            );
        }
    }
    assert_eq!(consumers[root], 0);
    assert!(consumers[..root].iter().all(|count| *count == 1));
}

fn chain(length: usize) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let predicates: Vec<_> = (0..length - 1)
        .map(|i| declarations.declare_predicate(format!("P{i}"), vec![]))
        .collect();
    let mut clauses = vec![fact(predicates[0], ChcExpr::Bool(true))];
    for pair in predicates.windows(2) {
        clauses.push(rule(pair[1], &[pair[0]]));
    }
    clauses.push(HornClause::query(body(&[*predicates.last().unwrap()])));
    source(declarations, clauses)
}

#[test]
fn chains_of_nine_thirty_two_and_sixty_five_occurrences_are_not_structurally_cut() {
    for length in [9, 32, 65] {
        let problem = chain(length);
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        let mut search = Search::new(&problem, &control).unwrap();
        assert_eq!(search.index.costs[length - 1], Some(length));
        let tree = search.next(&control).unwrap();
        assert_eq!(tree.clause_indices, (0..length).collect::<Vec<_>>());
        check(&problem, &tree);
        assert!(search.next(&control).is_none());
        assert!(matches!(search.step(&control), Some(Step::Exhausted)));
        assert!(control.poll().is_some());
    }
}

#[test]
fn minimum_productive_costs_handle_reverse_source_order_and_duplicate_slots() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let r = declarations.declare_predicate("R", vec![]);
    let problem = source(
        declarations,
        vec![
            HornClause::query(body(&[r])),
            rule(r, &[q, p]),
            rule(q, &[p, p]),
            fact(p, ChcExpr::Bool(false)),
        ],
    );
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    assert_eq!(search.index.minimum, vec![Some(1), Some(3), Some(5)]);
    assert_eq!(search.index.costs[0], Some(6));
    let tree = search.next(&control).unwrap();
    assert_eq!(tree.clause_indices, vec![3, 3, 2, 3, 1, 0]);
    assert_eq!(
        tree.premise_steps,
        vec![vec![], vec![], vec![0, 1], vec![], vec![2, 3], vec![4]]
    );
    check(&problem, &tree);
    assert!(search.next(&control).is_none());
}

#[test]
fn wide_bodies_keep_one_fresh_occurrence_per_original_slot() {
    for width in [8, 16, 65] {
        let mut declarations = ChcProblem::new();
        let p = declarations.declare_predicate("P", vec![]);
        let problem = source(
            declarations,
            vec![
                fact(p, ChcExpr::Bool(true)),
                HornClause::query(body(&vec![p; width])),
            ],
        );
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        let mut search = Search::new(&problem, &control).unwrap();
        let tree = search.next(&control).unwrap();
        assert_eq!(tree.clause_indices.len(), width + 1);
        assert!(tree.clause_indices[..width].iter().all(|index| *index == 0));
        assert_eq!(tree.premise_steps[width], (0..width).collect::<Vec<_>>());
        check(&problem, &tree);
        assert!(search.next(&control).is_none());
    }
}

#[test]
fn two_hundred_fifty_seven_definitions_do_not_fill_a_bfs_prefix_queue() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let mut clauses = vec![fact(p, ChcExpr::Bool(true)); 257];
    clauses.push(HornClause::query(body(&[p, p])));
    let problem = source(declarations, clauses);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    // Five cursor transitions choose the first fact independently twice and
    // publish a complete tree. No combinations are eagerly materialized.
    for _ in 0..4 {
        assert!(matches!(search.step(&control), Some(Step::Pending)));
    }
    let Some(Step::Candidate(first)) = search.step(&control) else {
        panic!("first tree");
    };
    assert_eq!(first.clause_indices, vec![0, 0, 257]);
    check(&problem, &first);
    let second = search.next(&control).unwrap();
    assert_eq!(second.clause_indices, vec![0, 1, 257]);
    assert_eq!(search.queries.len(), 1);
}

#[test]
fn more_than_sixty_four_raw_false_decoys_do_not_hide_the_later_fact() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let mut clauses = vec![fact(p, ChcExpr::Bool(false)); 70];
    clauses.push(fact(p, ChcExpr::Bool(true)));
    clauses.push(HornClause::query(body(&[p])));
    let problem = source(declarations, clauses);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    for definition in 0..71 {
        let tree = search.next(&control).unwrap();
        assert_eq!(tree.clause_indices, vec![definition, 71]);
        assert_eq!(
            problem.source_problem().clauses()[definition]
                .body
                .constraint,
            Some(ChcExpr::Bool(definition == 70))
        );
        check(&problem, &tree);
    }
    assert!(search.next(&control).is_none());
}

#[test]
fn recursive_first_query_cannot_starve_a_later_deep_query() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("Loop", vec![]);
    let q: Vec<_> = (0..32)
        .map(|i| declarations.declare_predicate(format!("Q{i}"), vec![]))
        .collect();
    let mut clauses = vec![
        fact(p, ChcExpr::Bool(false)),
        rule(p, &[p]),
        HornClause::query(body(&[p])),
        fact(q[0], ChcExpr::Bool(true)),
    ];
    for pair in q.windows(2) {
        clauses.push(rule(pair[1], &[pair[0]]));
    }
    let target = clauses.len();
    clauses.push(HornClause::query(body(&[q[31]])));
    let problem = source(declarations, clauses);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    let mut found = false;
    let mut earlier = 0;
    for _ in 0..512 {
        match search.step(&control).unwrap() {
            Step::Pending => {}
            Step::Candidate(tree) => {
                check(&problem, &tree);
                if tree.clause_indices.last() == Some(&target) {
                    found = true;
                    break;
                }
                earlier += 1;
            }
            Step::Exhausted => panic!("productive recursive query remains open"),
        }
    }
    assert!(found);
    assert!(earlier > 0);
}

#[test]
fn unproductive_cycles_and_missing_definitions_finish_without_fake_candidates() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let absent = declarations.declare_predicate("Missing", vec![]);
    let problem = source(
        declarations,
        vec![
            rule(p, &[q, q]),
            rule(q, &[p]),
            HornClause::query(body(&[p])),
            HornClause::query(body(&[absent])),
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
        ],
    );
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    assert_eq!(search.index.minimum, vec![None, None, None]);
    assert_eq!(search.next(&control).unwrap().clause_indices, vec![4]);
    assert!(search.next(&control).is_none());
    assert!(control.poll().is_some());
}

#[test]
fn exact_cost_layers_match_the_small_frozen_tree_set_without_duplicates() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let problem = source(
        declarations,
        vec![
            fact(p, ChcExpr::Bool(true)),
            rule(p, &[p, p]),
            HornClause::query(body(&[p])),
        ],
    );
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let frozen = super::super::trees::enumerate(&problem, &control).unwrap();
    let mut search = Search::new(&problem, &control).unwrap();
    let current: Vec<_> = (0..frozen.len())
        .map(|_| search.next(&control).unwrap())
        .collect();
    assert_eq!(
        current
            .iter()
            .map(|d| d.clause_indices.len())
            .collect::<Vec<_>>(),
        vec![2, 4, 6, 6, 8, 8, 8, 8, 8]
    );
    for tree in &current {
        check(&problem, tree);
    }
    let key = |values: Vec<Derivation>| {
        let mut keys: Vec<_> = values
            .into_iter()
            .map(|d| (d.clause_indices, d.premise_steps))
            .collect();
        keys.sort();
        keys
    };
    assert_eq!(key(current), key(frozen));
    assert_eq!(search.next(&control).unwrap().clause_indices.len(), 10);
}

#[test]
fn one_shared_control_and_a_refused_cursor_cannot_be_reset_between_steps() {
    let problem = chain(9);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    assert!(matches!(search.step(&control), Some(Step::Pending)));
    token.cancel();
    assert!(search.step(&control).is_none());
    token.reset();
    let fresh = SourceControl::new(deadline(), &token);
    assert!(search.step(&fresh).is_none());
    let mut retry = Search::new(&problem, &fresh).unwrap();
    assert_eq!(retry.next(&fresh).unwrap().clause_indices.len(), 9);
    let exhausted = SourceControl::new(deadline(), &token);
    assert!(exhausted.bytes(usize::MAX).is_none());
    assert!(Search::new(&problem, &exhausted).is_none());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(Search::new(&problem, &expired).is_none());
}

#[test]
fn overflowing_structural_cost_does_not_hide_an_independent_easy_query() {
    let mut declarations = ChcProblem::new();
    let predicates: Vec<_> = (0..=usize::BITS)
        .map(|i| declarations.declare_predicate(format!("Big{i}"), vec![]))
        .collect();
    let alternative = declarations.declare_predicate("Alternative", vec![]);
    let mut clauses = vec![fact(predicates[0], ChcExpr::Bool(true))];
    for pair in predicates.windows(2) {
        clauses.push(rule(pair[1], &[pair[0], pair[0]]));
    }
    clauses.push(HornClause::query(body(&[*predicates.last().unwrap()])));
    // This rule's individual cost is usize::MAX, but combining it with
    // another pending sibling overflows. A later fact must remain available.
    let child = predicates[usize::BITS as usize - 2];
    clauses.push(rule(alternative, &[child, child]));
    let cheap = clauses.len();
    clauses.push(fact(alternative, ChcExpr::Bool(true)));
    let joined = clauses.len();
    clauses.push(HornClause::query(body(&[alternative, alternative])));
    let easy = clauses.len();
    clauses.push(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let problem = source(declarations, clauses);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let mut search = Search::new(&problem, &control).unwrap();
    assert_eq!(
        search.index.minimum[predicates.last().unwrap().index()],
        None
    );
    assert_eq!(search.next(&control).unwrap().clause_indices, vec![easy]);
    assert_eq!(
        search.next(&control).unwrap().clause_indices,
        vec![cheap, cheap, joined]
    );
    assert!(search.next(&control).is_none());
    assert!(control.poll().is_some());
}
