// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcExpr, ChcProblem, ClauseBody, HornClause};
use ay_core::time::Instant;
use std::time::Duration;

fn problem(clauses: impl FnOnce(crate::PredicateId) -> Vec<HornClause>) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        clauses(p)
            .into_iter()
            .map(|clause| QuantifiedHornClause::new(clause, vec![]))
            .collect(),
    )
    .unwrap()
}

fn paths(source: &QuantifiedChcProblem) -> Vec<Vec<usize>> {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    enumerate(source, &control).unwrap()
}

#[test]
fn paths_are_breadth_first_original_indices_with_repeated_transition_occurrences() {
    let source = problem(|p| {
        vec![
            HornClause::fact(ChcExpr::Bool(true), p, vec![]),
            HornClause::new(
                ClauseBody::predicates_only(vec![(p, vec![])]),
                ClauseHead::Predicate(p, vec![]),
            ),
            HornClause::query(ClauseBody::predicates_only(vec![(p, vec![])])),
        ]
    });
    let result = paths(&source);
    let expected: Vec<Vec<usize>> = (0..=MAX_PATH_CLAUSES - 2)
        .map(|repetitions| {
            let mut path = vec![0];
            path.extend(std::iter::repeat_n(1, repetitions));
            path.push(2);
            path
        })
        .collect();
    assert_eq!(result, expected);
}

#[test]
fn path_search_preserves_raw_false_constraints_but_refuses_nonlinear_or_rootless_chains() {
    let source = problem(|p| {
        vec![
            HornClause::fact(ChcExpr::Bool(false), p, vec![]),
            HornClause::query(ClauseBody::predicates_only(vec![(p, vec![])])),
            HornClause::query(ClauseBody::predicates_only(vec![(p, vec![]), (p, vec![])])),
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
        ]
    });
    // Enumeration proposes paths, not SAT: even the false query/fact is kept
    // for the exact renderer and solver to reject.
    assert_eq!(paths(&source), vec![vec![3], vec![0, 1]]);
    let rootless = problem(|p| {
        vec![
            HornClause::new(
                ClauseBody::predicates_only(vec![(p, vec![])]),
                ClauseHead::Predicate(p, vec![]),
            ),
            HornClause::query(ClauseBody::predicates_only(vec![(p, vec![])])),
        ]
    });
    assert!(paths(&rootless).is_empty());
}

#[test]
fn path_count_and_prefix_caps_preserve_only_real_complete_candidates() {
    let source = problem(|p| {
        let mut clauses: Vec<_> = (0..MAX_PREFIXES + 1)
            .map(|_| HornClause::fact(ChcExpr::Bool(true), p, vec![]))
            .collect();
        clauses.push(HornClause::query(ClauseBody::predicates_only(vec![(
            p,
            vec![],
        )])));
        clauses
    });
    let result = paths(&source);
    assert_eq!(result.len(), MAX_PATHS);
    assert_eq!(result.first(), Some(&vec![0, MAX_PREFIXES + 1]));
    assert_eq!(result.last(), Some(&vec![MAX_PATHS - 1, MAX_PREFIXES + 1]));
    assert!(result.iter().all(|path| path.len() == 2));
}

#[test]
fn stopped_path_controls_do_not_return_partial_work_and_fresh_controls_retry() {
    let source = problem(|_| vec![HornClause::query(ClauseBody::empty())]);
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(enumerate(&source, &control).is_none());
    assert!(enumerate(&source, &control).is_none());
    assert_eq!(paths(&source), vec![vec![0]]);
    token.cancel();
    let cancelled = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(enumerate(&source, &cancelled).is_none());
    token.reset();
    assert!(enumerate(&source, &cancelled).is_none());
    assert_eq!(paths(&source), vec![vec![0]]);
}
