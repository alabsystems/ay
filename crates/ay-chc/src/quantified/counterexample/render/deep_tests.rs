// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deep/wide topology checks with an independent emitted-text SMT evaluator.

use super::*;
use crate::quantified::counterexample::render_oracle as oracle;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcOp, ChcProblem, ChcSort, ClauseBody};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

fn premise(value: bool) -> UniversalPremise {
    UniversalPremise::new(
        ChcVar::new("i", ChcSort::BitVec(2)),
        ChcExpr::Op(
            ChcOp::Eq,
            vec![
                Arc::new(ChcExpr::Bool(value)),
                Arc::new(ChcExpr::Bool(true)),
            ],
        ),
    )
}

fn source(body_count: usize, query_premise: bool) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(ChcExpr::Bool(true), p, vec![]),
                vec![premise(true)],
            ),
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::predicates_only(vec![(p, vec![])]),
                    ClauseHead::Predicate(p, vec![]),
                ),
                vec![premise(true)],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::predicates_only(vec![(p, vec![]); body_count])),
                vec![premise(query_premise)],
            ),
        ],
    )
    .unwrap()
}

fn render_case(source: &QuantifiedChcProblem, indices: &[usize], edges: &[Vec<usize>]) -> String {
    let token = CancellationToken::new();
    let deadline = Instant::now() + Duration::from_secs(30);
    let ordinary = render_derivation(
        source,
        indices,
        edges,
        &SourceControl::new(deadline, &token),
    )
    .unwrap();
    let retained = render_with_bindings(
        source,
        indices,
        edges,
        &SourceControl::new(deadline, &token),
    )
    .unwrap();
    assert_eq!(ordinary, retained.obligation);
    assert!(retained.bindings.is_empty()); // all i binders remain lexical
    assert_eq!(
        ordinary.matches("(forall ((i (_ BitVec 2)))").count(),
        indices.len()
    );
    ay_frontend::parse(&ordinary).unwrap();
    ordinary
}

#[test]
fn sixty_six_occurrence_chain_retains_every_original_premise_and_no_bound_local() {
    let mut indices = vec![0];
    indices.extend([1; 64]);
    indices.push(2);
    let edges: Vec<_> = (0..indices.len())
        .map(|step| if step == 0 { vec![] } else { vec![step - 1] })
        .collect();
    let positive = render_case(&source(1, true), &indices, &edges);
    assert_eq!(oracle::models(&positive), vec![Vec::<u64>::new()]);
    let negative = render_case(&source(1, false), &indices, &edges);
    assert_eq!(oracle::models(&negative), [] as [std::vec::Vec<u64>; 0]);
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let mut skipped = edges;
    skipped[65] = vec![63]; // occurrence64 is now orphaned
    assert!(render_derivation(&source(1, true), &indices, &skipped, &control).is_err());
}

#[test]
fn sixty_five_body_edges_remain_distinct_and_a_shared_fact_is_rejected() {
    let source = source(65, true);
    let mut indices = vec![0; 65];
    indices.push(2);
    let mut edges = vec![vec![]; 65];
    edges.push((0..65).collect());
    let script = render_case(&source, &indices, &edges);
    assert_eq!(oracle::models(&script), vec![Vec::<u64>::new()]);
    edges[65][64] = 0; // one occurrence cannot discharge two separate body slots
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(render_derivation(&source, &indices, &edges, &control).is_err());
}
