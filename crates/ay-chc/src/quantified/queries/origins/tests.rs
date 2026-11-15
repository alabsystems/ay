// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::UniversalPremise;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, HornClause, PredicateId};
use QuantifiedChcClauseOrigin::{Source, UnfoldedMarker};

mod resources;

fn row(
    inputs: &[PredicateId],
    head: Option<PredicateId>,
    constraint: Option<bool>,
) -> QuantifiedHornClause {
    QuantifiedHornClause::new(
        HornClause::new(
            ClauseBody::new(
                inputs.iter().map(|p| (*p, vec![])).collect(),
                constraint.map(ChcExpr::Bool),
            ),
            head.map_or(ClauseHead::False, |p| ClauseHead::Predicate(p, vec![])),
        ),
        vec![],
    )
}

fn rows(source: &QuantifiedChcProblem) -> Vec<QuantifiedChcQueryObligation> {
    source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap()
}

fn duplicate_source(unrelated: bool) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let unused = declarations.declare_predicate("Unused", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], Some(p), Some(false)),
            row(&[], Some(unused), Some(unrelated)),
            row(&[], Some(p), Some(false)),
            row(&[p], None, Some(true)),
        ],
    )
    .unwrap()
}

fn validate_map(
    source: &QuantifiedChcProblem,
    slice: &QuantifiedChcProblem,
    origins: &[QuantifiedChcClauseOrigin],
) -> ChcResult<()> {
    let token = CancellationToken::new();
    let control = Control::new(Instant::now() + Duration::from_secs(60), &token);
    let census = copy::Census::new(source, &control)?;
    let plan = plan::plans(source, &control)?.remove(0);
    let selected = plan::cone(source, &plan, &census.definitions, &control)?;
    census.charge_conservation(&selected, plan.selected(), &control)?;
    validate(source, &plan, &selected, slice, origins, &control)
}

#[test]
fn duplicate_clause_contents_keep_distinct_exact_coordinates_and_survive_into_parts() {
    let source = duplicate_source(false);
    let mut obligations = rows(&source);
    let obligation = obligations.remove(0);
    let expected = [
        Source { clause_index: 0 },
        Source { clause_index: 2 },
        Source { clause_index: 3 },
    ];
    assert_eq!(obligation.id().clause_origins(), expected);
    assert_eq!(
        obligation.id().clause_origin(1),
        Some(Source { clause_index: 2 })
    );
    assert_eq!(obligation.id().clause_origin(3), None);
    assert_eq!(obligation.id().clause_origin(usize::MAX), None);
    let cloned = obligation.id().clone();
    let (id, slice) = obligation.into_parts();
    assert_eq!(id, cloned);
    assert!(Arc::ptr_eq(&id.clause_origins, &cloned.clause_origins));
    assert_eq!(id.clause_origins(), expected);
    assert!(validate_map(&source, &slice, id.clause_origins()).is_ok());
}

#[test]
fn early_false_head_query_is_mapped_at_its_actual_slice_position() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let unrelated = declarations.declare_predicate("Unrelated", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[p], None, Some(true)),
            row(&[], Some(unrelated), None),
            row(&[], Some(p), Some(false)),
        ],
    )
    .unwrap();
    let obligations = rows(&source);
    let obligation = &obligations[0];
    assert_eq!(
        obligation.id().clause_origins(),
        [Source { clause_index: 0 }, Source { clause_index: 2 }]
    );
    assert!(obligation.problem().source_problem().clauses()[0].is_query());
    assert!(!obligation.problem().source_problem().clauses()[1].is_query());
    assert_eq!(
        obligation.problem().source_problem().clauses()[0].source_query_ordinal,
        Some(0)
    );
}

#[test]
fn recursive_marker_definition_keeps_both_original_and_composed_origins() {
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
                query_clause_index: 3
            },
        ]
    );
    assert_eq!(
        obligations[1].id().clause_origins(),
        [UnfoldedMarker {
            defining_clause_index: 2,
            query_clause_index: 3
        }]
    );
    assert!(matches!(
        obligations[0].problem().source_problem().clauses()[1].head,
        ClauseHead::Predicate(_, _)
    ));
    assert!(obligations[0].problem().source_problem().clauses()[3].is_query());
}

#[test]
fn duplicate_unfolded_branches_and_original_query_ordinals_remain_distinct() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], Some(error), Some(false)),
            row(&[], Some(error), Some(false)),
            row(&[error], None, None),
            row(&[], None, Some(false)),
        ],
    )
    .unwrap();
    let obligations = rows(&source);
    assert_eq!(obligations.len(), 3);
    for (index, obligation) in obligations[..2].iter().enumerate() {
        assert_eq!(
            obligation.id().clause_origins(),
            [UnfoldedMarker {
                defining_clause_index: index,
                query_clause_index: 2
            }]
        );
        assert_eq!(obligation.id().source_query_ordinal(), 0);
    }
    assert_eq!(
        obligations[2].id().clause_origins(),
        [Source { clause_index: 3 }]
    );
    assert_eq!(obligations[2].id().source_query_ordinal(), 1);
    assert_eq!(
        obligations[2].problem().source_problem().clauses()[0].source_query_ordinal,
        Some(0)
    );
    assert_eq!(
        obligations[0].id().content_sha256(),
        obligations[1].id().content_sha256()
    );
    assert_ne!(obligations[0].id(), obligations[1].id());
    let retry = rows(&source);
    assert!(obligations
        .iter()
        .zip(retry)
        .all(|(left, right)| left.id() == right.id()));
}

#[test]
fn map_order_tampering_is_refused_even_when_duplicate_bodies_are_identical() {
    let source = duplicate_source(false);
    let obligations = rows(&source);
    let obligation = &obligations[0];
    let correct = obligation.id().clause_origins();
    let mut swapped = correct.to_vec();
    swapped.swap(0, 1);
    assert!(validate_map(&source, obligation.problem(), &swapped).is_err());
    assert!(validate_map(&source, obligation.problem(), &correct[..2]).is_err());
    let mut foreign = correct.to_vec();
    foreign[0] = Source { clause_index: 1 };
    assert!(validate_map(&source, obligation.problem(), &foreign).is_err());
    let mut id = obligation.id().clone();
    id.clause_origins = swapped.into();
    assert_ne!(&id, obligation.id());
}

#[test]
fn unrelated_source_mutation_changes_aggregate_binding_without_changing_map_or_slice() {
    let original = rows(&duplicate_source(false));
    let changed = rows(&duplicate_source(true));
    assert_eq!(
        original[0].id().clause_origins(),
        changed[0].id().clause_origins()
    );
    assert_eq!(
        original[0].id().content_sha256(),
        changed[0].id().content_sha256()
    );
    assert_ne!(
        original[0].id().aggregate_source_sha256(),
        changed[0].id().aggregate_source_sha256()
    );
    assert_ne!(original[0].id(), changed[0].id());
}

#[test]
fn conservation_checks_all_grouped_premises_and_rewritten_query_body() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let mut definition = row(&[], Some(error), Some(false));
    definition = QuantifiedHornClause::new(
        definition.clause,
        vec![UniversalPremise::with_binders(
            vec![
                ChcVar::new("i", ChcSort::BitVec(1)),
                ChcVar::new("j", ChcSort::BitVec(1)),
            ],
            ChcExpr::Bool(true),
        )
        .unwrap()],
    );
    let source =
        QuantifiedChcProblem::new(declarations, vec![row(&[error], None, None), definition])
            .unwrap();
    let obligations = rows(&source);
    let obligation = &obligations[0];
    assert_eq!(
        obligation.id().clause_origins(),
        [UnfoldedMarker {
            defining_clause_index: 1,
            query_clause_index: 0
        }]
    );
    assert!(validate_map(
        &source,
        obligation.problem(),
        obligation.id().clause_origins()
    )
    .is_ok());
    let mut changed = obligation.problem().clone();
    changed.premises[0][0] = UniversalPremise::with_binders(
        vec![
            ChcVar::new("j", ChcSort::BitVec(1)),
            ChcVar::new("i", ChcSort::BitVec(1)),
        ],
        ChcExpr::Bool(true),
    )
    .unwrap();
    assert!(validate_map(&source, &changed, obligation.id().clause_origins()).is_err());
    let mut changed = obligation.problem().clone();
    changed.source.clauses_mut()[0].body.constraint = Some(ChcExpr::Bool(true));
    assert!(validate_map(&source, &changed, obligation.id().clause_origins()).is_err());
}
