// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::UniversalPremise;
use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use QuantifiedChcClauseOrigin::{Source, UnfoldedMarker};

mod resources;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn row(
    inputs: &[PredicateId],
    head: Option<PredicateId>,
    constraint: Option<bool>,
) -> QuantifiedHornClause {
    QuantifiedHornClause::new(
        HornClause::new(
            ClauseBody::new(
                inputs.iter().map(|id| (*id, vec![])).collect(),
                constraint.map(ChcExpr::Bool),
            ),
            head.map_or(ClauseHead::False, |id| ClauseHead::Predicate(id, vec![])),
        ),
        vec![],
    )
}

fn rows(source: &QuantifiedChcProblem) -> Vec<QuantifiedChcQueryObligation> {
    source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap()
}

fn accepts(obligation: &QuantifiedChcQueryObligation, source: &QuantifiedChcProblem) -> bool {
    let token = CancellationToken::new();
    let parent = SourceControl::new(deadline(), &token);
    obligation
        .authenticate_aggregate(source, deadline(), &token, &parent)
        .is_some()
}

fn duplicates(unused: bool) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let unused_predicate = declarations.declare_predicate("Unused", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[p], None, Some(true)),
            row(&[], Some(unused_predicate), Some(unused)),
            row(&[], Some(p), Some(false)),
            row(&[], Some(p), Some(false)),
            row(&[], None, Some(false)),
        ],
    )
    .unwrap()
}

fn matrix() -> UniversalPremise {
    UniversalPremise::with_binders(
        vec![
            ChcVar::new("i", ChcSort::BitVec(1)),
            ChcVar::new("j", ChcSort::BitVec(1)),
        ],
        ChcExpr::Bool(true),
    )
    .unwrap()
}

#[test]
fn duplicate_positions_and_early_queries_bind_without_assuming_query_last() {
    let source = duplicates(false);
    let obligations = rows(&source);
    assert_eq!(obligations.len(), 2);
    assert_eq!(
        obligations[0].id().clause_origins(),
        [
            Source { clause_index: 0 },
            Source { clause_index: 2 },
            Source { clause_index: 3 },
        ]
    );
    assert!(obligations.iter().all(|row| accepts(row, &source)));
    assert!(matches!(
        obligations[0]
            .problem
            .source_view()
            .clause(0)
            .unwrap()
            .head(),
        ClauseHead::False
    ));
    assert!(Arc::ptr_eq(
        &obligations[0].id.aggregate_source,
        &obligations[1].id.aggregate_source
    ));
    let cloned = obligations[0].id.clone();
    assert!(Arc::ptr_eq(
        &cloned.aggregate_source,
        &obligations[0].id.aggregate_source
    ));
    assert_eq!(cloned.aggregate_source.as_ref(), source.source_smtlib());
}

#[test]
fn recursive_marker_keeps_its_ordinary_definition_and_synthetic_query_distinct() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[error], Some(p), None),
            row(&[p], Some(error), None),
            row(&[], Some(error), Some(false)),
            row(&[error], None, None),
        ],
    )
    .unwrap();
    let obligations = rows(&source);
    assert_eq!(obligations.len(), 2);
    assert_eq!(
        obligations[0].id().clause_origins(),
        [
            Source { clause_index: 0 },
            Source { clause_index: 1 },
            Source { clause_index: 2 },
            UnfoldedMarker {
                defining_clause_index: 1,
                query_clause_index: 3,
            },
        ]
    );
    assert!(obligations.iter().all(|row| accepts(row, &source)));
    let mut swapped = obligations[0].clone();
    swapped.id.defining_clause_index = Some(2);
    assert!(!accepts(&swapped, &source));
}

#[test]
fn query_constraints_or_own_premises_prevent_unfolding_and_are_conserved() {
    for constraint in [None, Some(true)] {
        let mut declarations = ChcProblem::new();
        let error = declarations.declare_predicate("error", vec![]);
        let mut query = row(&[error], None, constraint);
        query.premises.push(matrix());
        let mut definition = row(&[], Some(error), None);
        definition.premises.push(matrix());
        let source = QuantifiedChcProblem::new(declarations, vec![query, definition]).unwrap();
        let mut obligation = rows(&source).remove(0);
        assert_eq!(obligation.id.defining_clause_index(), None);
        assert!(accepts(&obligation, &source));
        // Deliberately mutate raw typed state without changing the cached SMT
        // bytes: membership must check full matrices, not merely both hashes.
        obligation.problem.premises[1][0] = UniversalPremise::with_binders(
            matrix().binders().cloned().collect(),
            ChcExpr::Bool(false),
        )
        .unwrap();
        assert!(!accepts(&obligation, &source));
    }
}

#[test]
fn equal_canonical_hashes_do_not_hide_none_versus_some_true_in_mapped_clauses() {
    let make = |constraint| {
        let mut declarations = ChcProblem::new();
        let error = declarations.declare_predicate("error", vec![]);
        QuantifiedChcProblem::new(
            declarations,
            vec![row(&[], Some(error), constraint), row(&[error], None, None)],
        )
        .unwrap()
    };
    let absent = make(None);
    let explicit = make(Some(true));
    let absent_rows = rows(&absent);
    let explicit_rows = rows(&explicit);
    assert_eq!(absent.source_smtlib(), explicit.source_smtlib());
    assert_eq!(absent_rows[0].id(), explicit_rows[0].id());
    assert_eq!(
        absent_rows[0].problem.source_smtlib(),
        explicit_rows[0].problem.source_smtlib()
    );
    assert!(accepts(&absent_rows[0], &absent));
    assert!(accepts(&explicit_rows[0], &explicit));
    assert!(!accepts(&absent_rows[0], &explicit));
    assert!(!accepts(&explicit_rows[0], &absent));
}

#[test]
fn complete_source_bytes_and_every_private_query_identity_field_are_required() {
    let source = duplicates(false);
    let foreign = duplicates(true);
    let obligation = rows(&source).remove(0);
    let foreign_row = rows(&foreign).remove(0);
    assert_eq!(obligation.id.content_sha256, foreign_row.id.content_sha256);
    assert!(!accepts(&obligation, &foreign));
    for mutation in 0..8 {
        let mut changed = obligation.clone();
        match mutation {
            0 => changed.id.source_query_ordinal = 1,
            1 => changed.id.query_clause_index = 4,
            2 => changed.id.defining_clause_index = Some(2),
            3 => changed.id.label.push_str("_changed"),
            4 => changed.id.aggregate_source_sha256 = "0".repeat(64),
            5 => changed.id.content_sha256 = "0".repeat(64),
            6 => changed.id.aggregate_source = Arc::from(foreign.source_smtlib()),
            _ => {
                // Even a coherently replaced hash cannot substitute for the
                // independently retained complete aggregate source bytes.
                changed.id.aggregate_source_sha256 = foreign.source_sha256();
                assert!(!accepts(&changed, &foreign));
                continue;
            }
        }
        assert!(!accepts(&changed, &source), "{mutation}");
    }
}

#[test]
fn full_cone_and_map_order_are_checked_even_for_identical_duplicate_definitions() {
    let source = duplicates(false);
    let obligation = rows(&source).remove(0);
    for mutation in 0..4 {
        let mut changed = obligation.clone();
        let mut origins = changed.id.clause_origins.to_vec();
        match mutation {
            0 => origins.swap(1, 2),
            1 => {
                origins.pop();
            }
            2 => origins[1] = Source { clause_index: 1 },
            _ => {
                origins[0] = UnfoldedMarker {
                    defining_clause_index: 2,
                    query_clause_index: 0,
                }
            }
        }
        changed.id.clause_origins = origins.into();
        assert!(!accepts(&changed, &source), "{mutation}");
    }
    // Remove a real dependency from both the typed slice and origin map, then
    // coherently update its content hash. All remaining clauses are authentic.
    let token = CancellationToken::new();
    let control = Control::new(deadline(), &token);
    let declarations = copy::declarations(obligation.problem.source_problem(), &control).unwrap();
    let clauses = obligation
        .problem
        .source_view()
        .clauses()
        .filter(|clause| clause.index() != 1)
        .map(|clause| {
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(
                        clause.body_predicates().to_vec(),
                        clause.constraint().cloned(),
                    ),
                    clause.head().clone(),
                ),
                clause.premises().to_vec(),
            )
        })
        .collect();
    let mut changed = obligation.clone();
    changed.problem = QuantifiedChcProblem::new(declarations, clauses).unwrap();
    changed.id.content_sha256 = changed.problem.source_sha256();
    changed.id.clause_origins = vec![Source { clause_index: 0 }, Source { clause_index: 3 }].into();
    assert!(!accepts(&changed, &source));
}

#[test]
fn early_unfolded_query_preserves_every_binder_in_order() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let mut definition = row(&[], Some(error), None);
    definition.premises.push(matrix());
    let source =
        QuantifiedChcProblem::new(declarations, vec![row(&[error], None, None), definition])
            .unwrap();
    let mut obligation = rows(&source).remove(0);
    assert_eq!(obligation.id.query_clause_index(), 0);
    assert_eq!(obligation.id.defining_clause_index(), Some(1));
    assert!(accepts(&obligation, &source));
    let mut reversed = matrix().binders().cloned().collect::<Vec<_>>();
    reversed.reverse();
    obligation.problem.premises[0][0] =
        UniversalPremise::with_binders(reversed, ChcExpr::Bool(true)).unwrap();
    assert!(!accepts(&obligation, &source));
}
