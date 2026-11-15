// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcExpr, ChcProblem, ClauseBody, HornClause};
use ay_core::time::Instant;
use std::time::Duration;

fn source() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let r = declarations.declare_predicate("R", vec![]);
    let clauses = vec![
        HornClause::fact(ChcExpr::Bool(true), p, vec![]),
        HornClause::fact(ChcExpr::Bool(true), q, vec![]),
        HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![])]),
            ClauseHead::Predicate(p, vec![]),
        ),
        HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![]), (q, vec![])]),
            ClauseHead::Predicate(r, vec![]),
        ),
        HornClause::query(ClauseBody::predicates_only(vec![(r, vec![])])),
        HornClause::query(ClauseBody::predicates_only(vec![(p, vec![]), (p, vec![])])),
        HornClause::query(ClauseBody::predicates_only(vec![(p, vec![])])),
        HornClause::query(ClauseBody::empty()),
        HornClause::fact(ChcExpr::Bool(true), p, vec![]),
    ];
    QuantifiedChcProblem::new(
        declarations,
        clauses
            .into_iter()
            .map(|clause| QuantifiedHornClause::new(clause, vec![]))
            .collect(),
    )
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

#[test]
fn complete_topological_trees_include_internal_joins_and_repeated_facts() {
    let source = source();
    let token = CancellationToken::new();
    for (indices, edges) in [
        (vec![0, 1, 3, 4], vec![vec![], vec![], vec![0, 1], vec![2]]),
        (vec![0, 0, 5], vec![vec![], vec![], vec![0, 1]]),
        (vec![0, 0, 5], vec![vec![], vec![], vec![1, 0]]),
        (vec![0, 2, 2, 6], vec![vec![], vec![0], vec![1], vec![2]]),
        (vec![7], vec![vec![]]),
    ] {
        assert!(validate(&source, &indices, &edges, &control(&token)).is_ok());
    }
}

#[test]
fn incomplete_cyclic_shared_or_unreachable_topologies_have_no_authority() {
    let source = source();
    let token = CancellationToken::new();
    for (indices, edges) in [
        (vec![], vec![]),
        (vec![0, 6], vec![vec![]]),
        (vec![0, 6], vec![vec![], vec![]]),
        (vec![0, 0, 5], vec![vec![], vec![], vec![0, 0]]),
        (vec![0, 0, 5], vec![vec![], vec![], vec![0, 2]]),
        (vec![0, 2, 6], vec![vec![], vec![1], vec![1]]),
        (vec![0, 2, 6], vec![vec![], vec![2], vec![1]]),
        (vec![0, 0, 6], vec![vec![], vec![], vec![1]]),
        (vec![0, 7, 5], vec![vec![], vec![], vec![0, 1]]),
        (vec![0, usize::MAX], vec![vec![], vec![0]]),
        (vec![0], vec![vec![]]),
    ] {
        assert!(
            validate(&source, &indices, &edges, &control(&token)).is_err(),
            "{indices:?} {edges:?}"
        );
    }
}

#[test]
fn every_edge_uses_the_original_body_predicate_in_order() {
    let source = source();
    let token = CancellationToken::new();
    let indices = [0, 1, 3, 4];
    for edges in [
        vec![vec![], vec![], vec![1, 0], vec![2]],
        vec![vec![], vec![], vec![0], vec![2]],
        vec![vec![], vec![], vec![0, 1], vec![0]],
    ] {
        assert!(validate(&source, &indices, &edges, &control(&token)).is_err());
    }
}

#[test]
fn repeated_original_indices_have_no_fixed_eight_occurrence_limit() {
    let source = source();
    let token = CancellationToken::new();
    for count in [8, 9, 32, 65, 4096] {
        let mut indices = vec![0];
        indices.extend(std::iter::repeat_n(2, count - 2));
        indices.push(6);
        let edges: Vec<_> = (0..count)
            .map(|step| if step == 0 { vec![] } else { vec![step - 1] })
            .collect();
        assert!(validate(&source, &indices, &edges, &control(&token)).is_ok());
        let identity = fingerprint(&indices, &edges, &control(&token)).unwrap();
        assert_eq!(
            fingerprint(&indices, &edges, &control(&token)),
            Some(identity)
        );
    }
}

#[test]
fn dynamic_census_retains_far_edge_cycle_sharing_and_orphan_refusals() {
    let source = source();
    let token = CancellationToken::new();
    let mut indices = vec![0];
    indices.extend(std::iter::repeat_n(2, 63));
    indices.push(6);
    let mut edges: Vec<_> = (0..65)
        .map(|step| if step == 0 { vec![] } else { vec![step - 1] })
        .collect();
    let original = fingerprint(&indices, &edges, &control(&token)).unwrap();
    assert!(validate(&source, &indices, &edges, &control(&token)).is_ok());
    for bad in [0, 63, 64, usize::MAX] {
        edges[63][0] = bad;
        assert!(validate(&source, &indices, &edges, &control(&token)).is_err());
        assert_ne!(
            fingerprint(&indices, &edges, &control(&token)),
            Some(original)
        );
    }
    edges[63][0] = 62;
    indices[63] = 1; // original Q fact cannot supply the P successor edge
    assert!(validate(&source, &indices, &edges, &control(&token)).is_err());
}

#[test]
fn dynamic_census_and_total_edge_hashing_have_shared_budget_refusals() {
    let source = source();
    let token = CancellationToken::new();
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(validate(&source, &[7], &[vec![]], &exhausted).is_err());
    assert!(fingerprint(&[0, 6], &[vec![], vec![]], &control(&token)).is_none());
    assert!(fingerprint(&[0, 6], &[vec![], vec![0, 0]], &control(&token)).is_none());
    assert!(validate(&source, &[7], &[vec![]], &control(&token)).is_ok());
}

#[test]
fn fingerprints_bind_all_original_indices_edge_order_and_partition_lengths() {
    let token = CancellationToken::new();
    let indices = [0, 0, 5];
    let edges = [vec![], vec![], vec![0, 1]];
    let original = fingerprint(&indices, &edges, &control(&token)).unwrap();
    assert_eq!(
        fingerprint(&indices, &edges, &control(&token)),
        Some(original)
    );
    for (indices, edges) in [
        (vec![8, 0, 5], vec![vec![], vec![], vec![0, 1]]),
        (vec![0, 0, 5], vec![vec![], vec![], vec![1, 0]]),
        (vec![0, 0, 5], vec![vec![], vec![0], vec![1]]),
        (vec![0, 5], vec![vec![], vec![0]]),
    ] {
        assert_ne!(
            fingerprint(&indices, &edges, &control(&token)),
            Some(original)
        );
    }
    assert!(fingerprint(&[], &[], &control(&token)).is_none());
    assert!(fingerprint(&indices, &[], &control(&token)).is_none());
}

#[test]
fn shared_control_refusals_stop_validation_and_fingerprinting() {
    let source = source();
    let token = CancellationToken::new();
    let stopped = control(&token);
    assert!(stopped.bytes(usize::MAX).is_none());
    assert!(validate(&source, &[7], &[vec![]], &stopped).is_err());
    assert!(fingerprint(&[7], &[vec![]], &stopped).is_none());
    let cancelled = control(&token);
    token.cancel();
    assert!(validate(&source, &[7], &[vec![]], &cancelled).is_err());
    token.reset();
    assert!(fingerprint(&[7], &[vec![]], &cancelled).is_none());
    assert!(validate(&source, &[7], &[vec![]], &control(&token)).is_ok());
}
