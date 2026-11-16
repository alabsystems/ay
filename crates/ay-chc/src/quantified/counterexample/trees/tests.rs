// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{CancellationToken, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody};
use ay_core::time::Instant;
use std::time::Duration;

fn problem(
    definitions: impl FnOnce(PredicateId, PredicateId, PredicateId) -> Vec<HornClause>,
) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let r = declarations.declare_predicate("R", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        definitions(p, q, r)
            .into_iter()
            .map(|clause| QuantifiedHornClause::new(clause, vec![]))
            .collect(),
    )
    .unwrap()
}

fn body(predicates: &[PredicateId]) -> ClauseBody {
    ClauseBody::predicates_only(predicates.iter().map(|id| (*id, vec![])).collect())
}

fn rule(head: PredicateId, predicates: &[PredicateId]) -> HornClause {
    HornClause::new(body(predicates), ClauseHead::Predicate(head, vec![]))
}

fn fact(head: PredicateId) -> HornClause {
    HornClause::fact(ChcExpr::Bool(true), head, vec![])
}

fn trees(source: &QuantifiedChcProblem) -> Vec<Derivation> {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let result = enumerate(source, &control).unwrap();
    // Independently check the occurrence tree, not merely its source-index list.
    for tree in &result {
        assert_ne!(tree.clause_indices, [] as [usize; 0]);
        assert!(tree.clause_indices.len() <= MAX_PATH_CLAUSES);
        assert_eq!(tree.clause_indices.len(), tree.premise_steps.len());
        let root = tree.clause_indices.len() - 1;
        let mut consumers = vec![0usize; tree.clause_indices.len()];
        for (step, &index) in tree.clause_indices.iter().enumerate() {
            let clause = &source.source_problem().clauses()[index];
            assert_eq!(matches!(clause.head, ClauseHead::False), step == root);
            assert_eq!(clause.body.predicates.len(), tree.premise_steps[step].len());
            for ((wanted, args), &child) in
                clause.body.predicates.iter().zip(&tree.premise_steps[step])
            {
                assert!(child < step);
                consumers[child] += 1;
                let ClauseHead::Predicate(head, head_args) =
                    &source.source_problem().clauses()[tree.clause_indices[child]].head
                else {
                    panic!("a premise occurrence must have a predicate head");
                };
                assert_eq!(head, wanted);
                assert_eq!(head_args.len(), args.len());
            }
        }
        assert_eq!(consumers[root], 0);
        assert!(consumers[..root].iter().all(|count| *count == 1));
    }
    result
}

#[test]
fn the_same_source_fact_is_two_independent_sibling_occurrences() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                fact(p),
                vec![UniversalPremise::with_binders(
                    vec![
                        ChcVar::new("i", ChcSort::BitVec(2)),
                        ChcVar::new("j", ChcSort::BitVec(2)),
                    ],
                    ChcExpr::Bool(true),
                )
                .unwrap()],
            ),
            QuantifiedHornClause::new(HornClause::query(body(&[p, p])), vec![]),
        ],
    )
    .unwrap();
    assert_eq!(
        trees(&source),
        vec![Derivation {
            clause_indices: vec![0, 0, 1],
            premise_steps: vec![vec![], vec![], vec![0, 1]],
        }]
    );
    // Enumeration does not instantiate or drop either occurrence's original
    // grouped premise. The renderer receives the same raw source index twice.
    assert_eq!(source.premises()[0][0].binder_count(), 2);
}

#[test]
fn internal_joins_and_shared_ancestors_keep_original_body_order() {
    let joined = problem(|p, q, r| {
        vec![
            fact(p),
            fact(q),
            rule(r, &[q, p, p]),
            HornClause::query(body(&[r])),
        ]
    });
    assert_eq!(
        trees(&joined),
        vec![Derivation {
            clause_indices: vec![1, 0, 0, 2, 3],
            premise_steps: vec![vec![], vec![], vec![], vec![0, 1, 2], vec![3]],
        }]
    );
    let diamond = problem(|p, q, r| {
        vec![
            fact(p),
            rule(q, &[p]),
            rule(r, &[p]),
            HornClause::query(body(&[q, r])),
        ]
    });
    assert_eq!(
        trees(&diamond),
        vec![Derivation {
            clause_indices: vec![0, 1, 0, 2, 3],
            premise_steps: vec![vec![], vec![0], vec![], vec![2], vec![1, 3]],
        }]
    );
}

#[test]
fn every_linear_candidate_and_its_order_match_the_frozen_path_enumerator() {
    let source = problem(|p, q, r| {
        vec![
            fact(p),
            HornClause::query(body(&[q])),
            fact(p),
            rule(p, &[p]),
            rule(q, &[p]),
            rule(q, &[r]),
            fact(r),
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
            HornClause::query(body(&[p])),
        ]
    });
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let expected = super::super::paths::enumerate(&source, &control).unwrap();
    let actual = trees(&source);
    assert_eq!(
        actual
            .iter()
            .map(|tree| &tree.clause_indices)
            .collect::<Vec<_>>(),
        expected.iter().collect::<Vec<_>>()
    );
    for tree in actual {
        assert_eq!(tree.premise_steps[0], [] as [usize; 0]);
        for (step, premises) in tree.premise_steps.iter().enumerate().skip(1) {
            assert_eq!(premises, &[step - 1]);
        }
    }
}

#[test]
fn recursive_joins_are_bounded_without_predicate_or_clause_deduplication() {
    let rooted = problem(|p, _, _| vec![fact(p), rule(p, &[p, p]), HornClause::query(body(&[p]))]);
    let actual = trees(&rooted);
    assert_eq!(actual.len(), 9);
    assert_eq!(
        actual
            .iter()
            .map(|tree| tree.clause_indices.len())
            .collect::<Vec<_>>(),
        vec![2, 4, 6, 6, 8, 8, 8, 8, 8]
    );
    assert_eq!(actual[1].clause_indices, vec![0, 0, 1, 2]);
    assert_eq!(
        actual[1].premise_steps,
        vec![vec![], vec![], vec![0, 1], vec![2]]
    );
    // The five eight-node trees each contain seven independent P occurrences
    // plus the query. A deeper unfinished expansion is never a candidate.
    let rootless = problem(|p, q, _| {
        vec![
            rule(p, &[q, q]),
            rule(q, &[p]),
            HornClause::query(body(&[p])),
        ]
    });
    assert_eq!(trees(&rootless), [] as [Derivation; 0]);
}

#[test]
fn raw_false_queries_facts_and_missing_definitions_are_not_rewritten() {
    let source = problem(|p, q, _| {
        vec![
            HornClause::fact(ChcExpr::Bool(false), p, vec![]),
            HornClause::query(body(&[p, p])),
            HornClause::query(body(&[p, q])),
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
        ]
    });
    let actual = trees(&source);
    assert_eq!(actual.len(), 2);
    assert_eq!(actual[0].clause_indices, vec![3]);
    assert_eq!(actual[1].clause_indices, vec![0, 0, 1]);
    assert!(matches!(
        source.source_problem().clauses()[0].body.constraint,
        Some(ChcExpr::Bool(false))
    ));
}

#[test]
fn the_node_cap_counts_all_siblings_and_the_query_not_only_branch_depth() {
    let source = problem(|p, _, _| {
        vec![
            fact(p),
            HornClause::query(body(&[p; MAX_PATH_CLAUSES - 1])),
            HornClause::query(body(&[p; MAX_PATH_CLAUSES])),
        ]
    });
    let actual = trees(&source);
    assert_eq!(actual.len(), 1);
    assert_eq!(actual[0].clause_indices.len(), MAX_PATH_CLAUSES);
    assert_eq!(actual[0].clause_indices[MAX_PATH_CLAUSES - 1], 1);
    assert_eq!(
        actual[0].premise_steps[MAX_PATH_CLAUSES - 1],
        (0..7).collect::<Vec<_>>()
    );
}

#[test]
fn candidate_and_prefix_caps_never_publish_incomplete_trees() {
    let wide = problem(|p, _, _| {
        let mut clauses = vec![fact(p); 8];
        clauses.push(HornClause::query(body(&[p, p])));
        clauses
    });
    let actual = trees(&wide);
    assert_eq!(actual.len(), MAX_PATHS);
    for (index, tree) in actual.iter().enumerate() {
        assert_eq!(tree.clause_indices, vec![index / 8, index % 8, 8]);
    }
    let prefix_limited = problem(|p, _, _| {
        let mut clauses = vec![fact(p); MAX_PREFIXES + 1];
        clauses.push(HornClause::query(body(&[p, p])));
        clauses
    });
    // All 255 admitted children still have an open second body slot. Hitting
    // the prefix cap is search incompleteness, not a partial candidate or Safe.
    assert_eq!(trees(&prefix_limited), [] as [Derivation; 0]);
}

#[test]
fn terminal_controls_discard_work_and_cannot_revive_after_parent_reset() {
    let source = problem(|p, _, _| vec![fact(p), HornClause::query(body(&[p, p]))]);
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(enumerate(&source, &control).is_none());
    assert!(enumerate(&source, &control).is_none());
    let work = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(work.charge(usize::MAX).is_none());
    assert!(enumerate(&source, &work).is_none());
    token.cancel();
    let cancelled = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(enumerate(&source, &cancelled).is_none());
    token.reset();
    assert!(enumerate(&source, &cancelled).is_none());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(enumerate(&source, &expired).is_none());
    assert_eq!(trees(&source).len(), 1);
}

#[test]
fn cumulative_copy_boundary_is_exact_and_a_fresh_attempt_retries() {
    const COPY_LIMIT: usize = 64 * 1024 * 1024;
    let source = problem(|p, _, _| vec![fact(p), HornClause::query(body(&[p, p]))]);
    let token = CancellationToken::new();
    let run = |allowance: usize| {
        let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
        control.bytes(COPY_LIMIT - allowance).unwrap();
        let result = enumerate(&source, &control);
        if result.is_none() {
            assert!(control.poll().is_none());
            assert!(enumerate(&source, &control).is_none());
        }
        result
    };
    let mut refused = 0usize;
    let mut admitted = COPY_LIMIT;
    assert!(run(refused).is_none());
    assert_eq!(run(admitted).unwrap().len(), 1);
    while admitted - refused > 1 {
        let middle = refused + (admitted - refused) / 2;
        if run(middle).is_some() {
            admitted = middle;
        } else {
            refused = middle;
        }
    }
    assert!(run(admitted - 1).is_none());
    assert_eq!(run(admitted).unwrap(), trees(&source));
}
