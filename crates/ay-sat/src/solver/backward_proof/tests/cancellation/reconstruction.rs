// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn prepared_reserved_reason_keeps_the_frozen_lrat_output() {
    let fixture = fixture();
    let actual = fixture
        .solver
        .reconstruct_lrat_backward_bounded_with_cancellation(&fixture.limits, &|| true)
        .expect("a prepared proof graph requires no solver invocation");
    // Frozen pre-cancellation reconstruction: original1 proves reserved3;
    // reserved3 then contradicts original2. No ID or hint order is normalized.
    assert_eq!(
        actual.steps,
        vec![LratStep {
            clause_id: fixture.reserved,
            literals: vec![fixture.positive],
            hints: vec![1],
        }]
    );
    assert_eq!(actual.empty_hints, vec![fixture.reserved, 2]);
    assert!(actual.complete);
    assert_same_result(
        Ok(actual),
        fixture
            .solver
            .reconstruct_lrat_backward_bounded(&fixture.limits),
    );
}

#[test]
fn every_reconstruction_poll_including_final_refuses_without_mutation() {
    let fixture = fixture();
    let trail = fixture.solver.trail.clone();
    let clause_ids = fixture.solver.cold.clause_ids.clone();
    let arena_len = fixture.solver.arena.len();
    let next_id = fixture.solver.cold.next_clause_id;
    let count = every_reconstruction_poll(&fixture.solver, &fixture.limits);
    assert!(count > 20, "exercise actual inner graph work");
    assert_eq!(fixture.solver.trail, trail);
    assert_eq!(fixture.solver.cold.clause_ids, clause_ids);
    assert_eq!(fixture.solver.arena.len(), arena_len);
    assert_eq!(fixture.solver.cold.next_clause_id, next_id);
}

#[test]
fn no_seed_still_has_a_final_cancellation_boundary() {
    let solver = Solver::new(1);
    let mut limits = generous_limits();
    limits.deadline = None;
    let actual = solver
        .reconstruct_lrat_backward_bounded_with_cancellation(&limits, &|| true)
        .expect("no seed is an ordinary incomplete reconstruction");
    assert!(!actual.complete);
    assert!(actual.steps.is_empty());
    assert!(actual.empty_hints.is_empty());
    every_reconstruction_poll(&solver, &limits);
}

#[test]
fn nondeferred_fixture_matches_the_independent_legacy_walk() {
    let mut fixture = fixture();
    fixture.solver.cold.backward_proof_limits = None;
    fixture
        .solver
        .record_unit_proof_id_for_lit(fixture.positive, 1);
    let expected = fixture.solver.reconstruct_lrat_backward();
    let actual = fixture
        .solver
        .reconstruct_lrat_backward_bounded_with_cancellation(&fixture.limits, &|| true)
        .expect("legacy unit proof");
    let mut steps = actual.steps;
    steps.push(LratStep {
        clause_id: 0,
        literals: Vec::new(),
        hints: actual.empty_hints.into_iter().map(|id| id as i64).collect(),
    });
    assert_eq!(steps, expected.steps);
    assert_eq!(actual.complete, expected.complete);
    assert_eq!(steps.last().expect("terminal").hints, vec![1, 2]);
}

#[test]
fn live_failures_preserve_the_original_envelope_and_refusal_is_distinct() {
    let fixture = fixture();
    for resource in [
        BackwardProofResource::Steps,
        BackwardProofResource::Literals,
        BackwardProofResource::Hints,
        BackwardProofResource::Bytes,
    ] {
        let mut limits = fixture.limits.clone();
        match resource {
            BackwardProofResource::Steps => limits.max_steps = 0,
            BackwardProofResource::Literals => limits.max_literals = 0,
            BackwardProofResource::Hints => limits.max_hints = 0,
            BackwardProofResource::Bytes => limits.max_bytes = 0,
            _ => unreachable!("fixture resource"),
        }
        let actual = fixture
            .solver
            .reconstruct_lrat_backward_bounded_with_cancellation(&limits, &|| true);
        assert!(
            matches!(&actual, Err(BackwardProofFailure::Limit { resource: seen, .. }) if *seen == resource)
        );
        assert_same_result(
            actual,
            fixture.solver.reconstruct_lrat_backward_bounded(&limits),
        );
        assert!(matches!(
            fixture
                .solver
                .reconstruct_lrat_backward_bounded_with_cancellation(&limits, &|| false),
            Err(BackwardProofFailure::Cancelled)
        ));
    }
}
