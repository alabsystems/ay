// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, Counterexample, SmtValue};
use ay_core::time::Instant;
use std::time::Duration;

fn control(callback: &mut dyn FnMut() -> bool) -> ChcQueryPlaybackControl<'_> {
    ChcQueryPlaybackControl::new(Instant::now() + Duration::from_secs(60), callback).unwrap()
}

fn chain() -> ChcProblem {
    let mut source = ChcProblem::new();
    let p = source.declare_predicate("P", vec![ChcSort::Int]);
    let middle = source.declare_predicate("middle", vec![]);
    let error = source.declare_predicate("error", vec![]);
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let fact = HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, vec![x]));
    source.add_clause(fact.clone());
    source.add_clause(fact); // equal text, different source ordinal
    source.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![y])]),
        ClauseHead::Predicate(middle, vec![]),
    ));
    source.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(middle, vec![])]),
        ClauseHead::Predicate(error, vec![]),
    ));
    source.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    source
}

fn wire(problem: &ChcProblem, steps: Vec<GroundDerivationStep>, root: usize) -> Vec<u8> {
    Counterexample::new(vec![])
        .with_ground_derivation(GroundDerivation {
            steps,
            query_step: root,
        })
        .ground_derivation_artifact_v2_with_progress(problem, &mut || true)
        .unwrap()
        .into_bytes()
}

fn step(clause: usize, name: &str, value: SmtValue, premises: Vec<usize>) -> GroundDerivationStep {
    GroundDerivationStep {
        clause_index: clause,
        env: [(name.to_owned(), value)].into_iter().collect(),
        premises,
    }
}

#[test]
fn controlled_slice_matches_ordinary_normalized_and_ordered_source() {
    let source = chain();
    let ordinary = source.query_obligations().unwrap();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let rows = source.query_obligations_with_playback(&mut owner).unwrap();
    assert_eq!(rows.len(), ordinary.len());
    for (row, expected) in rows.iter().zip(&ordinary) {
        assert_eq!(row.obligation_id(), expected.id());
        assert_eq!(
            row.problem().normalized_input(),
            expected.problem().normalized_input()
        );
        assert_eq!(
            crate::proof_metadata::ordered_chc_clause_sequence_sha256(row.problem()),
            crate::proof_metadata::ordered_chc_clause_sequence_sha256(expected.problem())
        );
    }
}

#[test]
fn repeated_identical_clause_ordinal_survives_two_composed_unfoldings() {
    let source = chain();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let mut ordinary = row.problem().clone();
    assert!(ordinary.expand_nullary_fail_queries(false));
    let (row, changed) = row.expand_nullary_queries(&mut owner).unwrap();
    assert!(changed);
    assert_eq!(
        row.problem().normalized_input(),
        ordinary.normalized_input()
    );
    let bytes = wire(
        row.problem(),
        vec![
            step(1, "x", SmtValue::Int(7), vec![]),
            step(2, "y", SmtValue::Int(7), vec![0]),
        ],
        1,
    );
    let (artifact, validated) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert_eq!(
        validated
            .steps()
            .map(|s| s.clause_index())
            .collect::<Vec<_>>(),
        [1, 2, 3, 4]
    );
    assert_eq!(
        validated.step(0).unwrap().source_binding("x"),
        Some(&SmtValue::Int(7))
    );
    assert_eq!(
        validated.step(1).unwrap().source_binding("y"),
        Some(&SmtValue::Int(7))
    );
    assert_eq!(validated.step(2).unwrap().source_bindings().count(), 0);
    assert_eq!(validated.step(3).unwrap().premises(), [2]);
    let again =
        crate::validate_chc_ground_derivation_artifact_v2(&source, artifact.bytes()).unwrap();
    assert_eq!(again.artifact_sha256(), validated.artifact_sha256());
}

#[test]
fn multiple_equal_definitions_remain_distinct_obligations() {
    let mut source = ChcProblem::new();
    let p = source.declare_predicate("error", vec![]);
    let fact = HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, vec![]));
    source.add_clause(fact.clone());
    source.add_clause(fact);
    source.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![],
    )])));
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let rows = source.query_obligations_with_playback(&mut owner).unwrap();
    assert_eq!(rows.len(), 2);
    for (ordinal, row) in rows.iter().enumerate() {
        assert_eq!(row.obligation_id().defining_clause_index(), Some(ordinal));
        let bytes = wire(
            row.problem(),
            vec![GroundDerivationStep {
                clause_index: 0,
                env: Default::default(),
                premises: vec![],
            }],
            0,
        );
        let (_, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
        assert_eq!(view.step(0).unwrap().clause_index(), ordinal);
    }
}

fn repeated_premise_source() -> ChcProblem {
    let mut source = ChcProblem::new();
    let p = source.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    source.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![x.clone()]),
    ));
    source.add_clause(HornClause::query(ClauseBody::predicates_only(vec![
        (p, vec![x.clone()]),
        (p, vec![x]),
    ])));
    source
}

#[test]
fn repeated_occurrences_and_duplicate_premises_are_preserved() {
    let source = repeated_premise_source();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    // Both equal fact occurrences participate in this rooted proof.
    let bytes = wire(
        row.problem(),
        vec![
            step(0, "x", SmtValue::Int(9), vec![]),
            step(0, "x", SmtValue::Int(9), vec![]),
            step(1, "x", SmtValue::Int(9), vec![0, 1]),
        ],
        2,
    );
    let (artifact, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert_eq!(
        view.steps().map(|s| s.clause_index()).collect::<Vec<_>>(),
        [0, 0, 1]
    );
    assert_eq!(view.step(2).unwrap().premises(), [0, 1]);
    for index in [0, 1] {
        assert_eq!(
            view.step(index).unwrap().source_binding("x"),
            Some(&SmtValue::Int(9))
        );
    }
    let again =
        crate::validate_chc_ground_derivation_artifact_v2(&source, artifact.bytes()).unwrap();
    assert_eq!(again.step_count(), 3);
    assert_eq!(again.step(2).unwrap().premises(), [0, 1]);

    // A separate rooted proof reuses one fact for both body occurrences.
    let bytes = wire(
        row.problem(),
        vec![
            step(0, "x", SmtValue::Int(9), vec![]),
            step(1, "x", SmtValue::Int(9), vec![0, 0]),
        ],
        1,
    );
    let (artifact, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert_eq!(
        view.steps().map(|s| s.clause_index()).collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(view.step(1).unwrap().premises(), [0, 0]);
    let again =
        crate::validate_chc_ground_derivation_artifact_v2(&source, artifact.bytes()).unwrap();
    assert_eq!(again.step_count(), 2);
    assert_eq!(again.premise_edge_count(), 2);
    assert_eq!(again.step(1).unwrap().premises(), [0, 0]);
}

#[test]
fn unreachable_repeated_occurrence_is_rejected_before_projection() {
    use crate::ground_derivation::{validate_ground_derivation, GroundDerivationError};
    use crate::ChcGroundDerivationArtifactErrorReason::DerivationRejected;

    let source = repeated_premise_source();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    // The old positive fixture contains an unrelated fact occurrence at step 0.
    let padded = GroundDerivation {
        steps: vec![
            step(0, "x", SmtValue::Int(9), vec![]),
            step(0, "x", SmtValue::Int(9), vec![]),
            step(1, "x", SmtValue::Int(9), vec![1, 1]),
        ],
        query_step: 2,
    };
    assert_eq!(
        validate_ground_derivation(row.problem(), &padded),
        Err(GroundDerivationError::UnreachableStep { step: 0 })
    );
    let error = Counterexample::new(vec![])
        .with_ground_derivation(padded)
        .ground_derivation_artifact_v2_with_progress(row.problem(), &mut || true)
        .unwrap_err();
    assert_eq!(error.reason, DerivationRejected);
    assert_eq!(error.detail, "step 0 is not reachable from the root step");

    // Change only the valid root's premise IDs: all counts, bindings, field
    // order and source hashes remain canonical, so refusal tests reachability.
    let valid = wire(
        row.problem(),
        vec![
            step(0, "x", SmtValue::Int(9), vec![]),
            step(0, "x", SmtValue::Int(9), vec![]),
            step(1, "x", SmtValue::Int(9), vec![0, 1]),
        ],
        2,
    );
    let text = std::str::from_utf8(&valid).unwrap();
    let premises = r#""premises":[0,1]"#;
    assert_eq!(text.matches(premises).count(), 1);
    let padded = text.replace(premises, r#""premises":[1,1]"#);
    let error = crate::validate_chc_ground_derivation_artifact_v2(row.problem(), padded.as_bytes())
        .unwrap_err();
    assert_eq!(error.reason, DerivationRejected);
    assert_eq!(error.detail, "step 0 is not reachable from the root step");
    let error = row
        .lift_ground_derivation_v2(padded.as_bytes(), &mut owner)
        .unwrap_err();
    let ChcQueryPlaybackError::Artifact(error) = error else {
        panic!("unreachable input must be rejected by artifact replay");
    };
    assert_eq!(error.reason, DerivationRejected);
    assert_eq!(error.detail, "step 0 is not reachable from the root step");
    row.lift_ground_derivation_v2(&valid, &mut owner).unwrap();
}

mod boundaries;
mod identity;
mod ledger;
mod values;
