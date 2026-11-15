// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These private traces are deliberately unsealed topology fixtures. No test
//! invokes a solver or treats successful coordinate mapping as SAT evidence.

use super::*;
use crate::quantified::{QuantifiedChcQueryObligation, QuantifiedHornClause, UniversalPremise};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};

fn row(
    body: &[PredicateId],
    head: Option<PredicateId>,
    constraint: Option<bool>,
) -> QuantifiedHornClause {
    QuantifiedHornClause::new(
        HornClause::new(
            ClauseBody::new(
                body.iter().map(|id| (*id, vec![])).collect(),
                constraint.map(ChcExpr::Bool),
            ),
            head.map_or(ClauseHead::False, |id| ClauseHead::Predicate(id, vec![])),
        ),
        vec![],
    )
}

fn obligations(source: &QuantifiedChcProblem) -> Vec<QuantifiedChcQueryObligation> {
    source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

fn unchecked(indices: Vec<usize>, edges: Vec<Vec<usize>>) -> QuantifiedChcTrace {
    QuantifiedChcTrace {
        base: QuantifiedChcCounterexample {
            source: Arc::from("unsealed mapping fixture"),
            clause_indices: indices,
            premise_steps: edges,
            topology_sha256: [0; 32],
            obligation: String::new(),
            memory_budget: None,
        },
        bindings: vec![],
        functions: vec![],
        pinned_obligation: String::new(),
    }
}

fn early_join() -> QuantifiedChcQueryObligation {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[error], None, None),
            row(&[], Some(p), None),
            row(&[p, p], Some(error), None),
        ],
    )
    .unwrap();
    obligations(&source).remove(0)
}

#[test]
fn early_direct_query_maps_by_occurrence_not_last_slice_clause() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let unrelated = declarations.declare_predicate("Unrelated", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[p], None, Some(true)),
            row(&[], Some(unrelated), None),
            row(&[], Some(p), None),
        ],
    )
    .unwrap();
    let row = obligations(&source).remove(0);
    assert_eq!(row.id().defining_clause_index(), None);
    assert_eq!(row.id().query_clause_index(), 0);
    let trace = unchecked(vec![1, 0], vec![vec![], vec![0]]);
    let token = CancellationToken::new();
    let mapped = map(&trace, row.id(), &control(&token)).unwrap();
    assert_eq!(mapped.clause_indices, [2, 0]);
    assert_eq!(mapped.premise_steps, trace.premise_steps());
    assert_eq!(trace.clause_indices(), [1, 0]);
}

#[test]
fn unfolded_join_keeps_repeated_siblings_and_body_edge_order_then_adds_one_query() {
    let row = early_join();
    assert_eq!(row.id().defining_clause_index(), Some(2));
    let trace = unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![1, 0]]);
    let token = CancellationToken::new();
    let mapped = map(&trace, row.id(), &control(&token)).unwrap();
    assert_eq!(mapped.clause_indices, [1, 1, 2, 0]);
    assert_eq!(mapped.premise_steps, [vec![], vec![], vec![1, 0], vec![2]]);
    assert_eq!(trace.clause_indices(), [1, 1, 0]);
    assert_eq!(trace.premise_steps(), [vec![], vec![], vec![1, 0]]);
}

#[test]
fn recursive_definition_retains_original_and_synthetic_occurrences_independently() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[error], Some(p), None),
            row(&[p], Some(error), None),
            row(&[], Some(error), None),
            row(&[error], None, None),
        ],
    )
    .unwrap();
    let row = obligations(&source).remove(0);
    assert_eq!(row.id().defining_clause_index(), Some(1));
    let trace = unchecked(
        vec![2, 0, 1, 0, 3],
        vec![vec![], vec![0], vec![1], vec![2], vec![3]],
    );
    let token = CancellationToken::new();
    let mapped = map(&trace, row.id(), &control(&token)).unwrap();
    assert_eq!(mapped.clause_indices, [2, 0, 1, 0, 1, 3]);
    assert_eq!(
        mapped.premise_steps,
        [vec![], vec![0], vec![1], vec![2], vec![3], vec![4]]
    );
}

#[test]
fn premise_bearing_marker_query_remains_direct_and_keeps_its_original_ordinal() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let mut query = row(&[error], None, None);
    query.premises.push(UniversalPremise::new(
        ChcVar::new("i", ChcSort::BitVec(2)),
        ChcExpr::Bool(true),
    ));
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], None, Some(false)),
            row(&[], Some(error), None),
            query,
        ],
    )
    .unwrap();
    let row = obligations(&source).remove(1);
    assert_eq!(row.id().source_query_ordinal(), 1);
    assert_eq!(row.id().defining_clause_index(), None);
    assert_eq!(row.id().query_clause_index(), 2);
    let trace = unchecked(vec![0, 1], vec![vec![], vec![0]]);
    let token = CancellationToken::new();
    let mapped = map(&trace, row.id(), &control(&token)).unwrap();
    assert_eq!(mapped.clause_indices, [1, 2]);
    assert_eq!(mapped.premise_steps, [vec![], vec![0]]);
}

#[test]
fn malformed_origin_coordinates_and_non_tree_edges_refuse_without_partial_output() {
    let row = early_join();
    let token = CancellationToken::new();
    let cases = [
        unchecked(vec![], vec![]),
        unchecked(vec![0], vec![]),
        unchecked(vec![1], vec![vec![]]), // A definition cannot stand for the root query.
        unchecked(vec![usize::MAX, 1, 0], vec![vec![], vec![], vec![0, 1]]),
        unchecked(vec![1, 1, usize::MAX], vec![vec![], vec![], vec![0, 1]]),
        unchecked(vec![0, 1, 0], vec![vec![], vec![], vec![0, 1]]), // Nonfinal synthetic row.
        unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![0]]),
        unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![0, 1, 1]]),
        unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![0, 0]]),
        unchecked(vec![1, 1, 0], vec![vec![], vec![1], vec![0]]),
        unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![0, usize::MAX]]),
    ];
    for trace in cases {
        assert!(map(&trace, row.id(), &control(&token)).is_none());
    }
}

#[test]
fn final_origin_must_match_complete_defining_and_query_identity_tuple() {
    use QuantifiedChcClauseOrigin::{Source, UnfoldedMarker};
    let unfolded = early_join();
    for origin in [
        Source { clause_index: 0 },
        Source { clause_index: 2 },
        UnfoldedMarker {
            defining_clause_index: 1,
            query_clause_index: 0,
        },
        UnfoldedMarker {
            defining_clause_index: 2,
            query_clause_index: 1,
        },
        UnfoldedMarker {
            defining_clause_index: 0,
            query_clause_index: 0,
        },
    ] {
        assert!(root_origin(unfolded.id(), origin).is_none());
    }
    assert_eq!(
        root_origin(
            unfolded.id(),
            UnfoldedMarker {
                defining_clause_index: 2,
                query_clause_index: 0
            }
        ),
        Some((2, Some(0)))
    );
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![row(&[], None, Some(false)), row(&[], None, Some(false))],
    )
    .unwrap();
    let direct = obligations(&source).remove(1);
    assert_eq!(
        root_origin(direct.id(), Source { clause_index: 1 }),
        Some((1, None))
    );
    assert!(root_origin(direct.id(), Source { clause_index: 0 }).is_none());
    assert!(root_origin(
        direct.id(),
        UnfoldedMarker {
            defining_clause_index: 0,
            query_clause_index: 1,
        }
    )
    .is_none());
    let token = CancellationToken::new();
    let trace = unchecked(vec![0], vec![vec![]]);
    let mapped = map(&trace, direct.id(), &control(&token)).unwrap();
    assert_eq!(mapped.clause_indices, [1]);
    assert_eq!(mapped.premise_steps, [Vec::<usize>::new()]);
}

#[test]
fn exact_shared_copy_allowance_succeeds_one_short_latches_and_fresh_retry_succeeds() {
    const TOTAL_BYTES: usize = 64 * 1024 * 1024;
    const TOTAL_WORK: usize = 8_000_000;
    let row = early_join();
    let trace = unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![1, 0]]);
    let token = CancellationToken::new();
    // Four output indices/Vec headers, three output edges, and three temporary
    // consumer bytes. Work: three census rows + four visits per input row +
    // three visits per original edge + append + fixed finish.
    let bytes = 4 * (std::mem::size_of::<usize>() + std::mem::size_of::<Vec<usize>>())
        + 3 * std::mem::size_of::<usize>()
        + 3;
    let work = 3 + 4 * 3 + 3 * 2 + 1 + 1;
    let exact = control(&token);
    exact.debit(TOTAL_WORK - work, TOTAL_BYTES - bytes).unwrap();
    assert!(map(&trace, row.id(), &exact).is_some());
    assert!(exact.debit(0, 1).is_none());
    for (remaining_work, remaining_bytes) in [(work, bytes - 1), (work - 1, bytes)] {
        let short = control(&token);
        short
            .debit(TOTAL_WORK - remaining_work, TOTAL_BYTES - remaining_bytes)
            .unwrap();
        assert!(map(&trace, row.id(), &short).is_none());
        assert!(short.poll().is_none());
        assert!(map(&trace, row.id(), &short).is_none());
    }
    assert!(map(&trace, row.id(), &control(&token)).is_some());
}

#[test]
fn observed_cancellation_remains_refused_after_reset_without_mutating_fresh_attempt() {
    let row = early_join();
    let trace = unchecked(vec![1, 1, 0], vec![vec![], vec![], vec![1, 0]]);
    let token = CancellationToken::new();
    let stopped = control(&token);
    token.cancel();
    assert!(map(&trace, row.id(), &stopped).is_none());
    token.reset();
    assert!(map(&trace, row.id(), &stopped).is_none());
    assert!(map(&trace, row.id(), &control(&token)).is_some());
}
