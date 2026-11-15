// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn constrained_marker_refuses_expansion_without_publishing_partial_row() {
    let mut source = chain();
    source.clauses.last_mut().unwrap().body.constraint =
        Some(ChcExpr::var(ChcVar::new("guard", ChcSort::Bool)));
    let before = source.normalized_input();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    assert_eq!(row.obligation_id().defining_clause_index(), None);
    assert!(matches!(
        row.expand_nullary_queries(&mut owner),
        Err(ChcQueryPlaybackError::UnsupportedProjection)
    ));
    assert_eq!(source.normalized_input(), before);
}

#[test]
fn unrecorded_rewrite_or_different_source_bytes_refuse() {
    let source = chain();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let mut changed = row.problem().clone();
    changed.clauses.swap(0, 2);
    let bytes = wire(
        &changed,
        vec![
            step(1, "x", SmtValue::Int(7), vec![]),
            step(0, "y", SmtValue::Int(7), vec![0]),
            GroundDerivationStep {
                clause_index: 3,
                env: Default::default(),
                premises: vec![1],
            },
        ],
        2,
    );
    assert!(row.lift_ground_derivation_v2(&bytes, &mut owner).is_err());
}

#[test]
fn foreign_control_cannot_refresh_prepared_row_allowance() {
    let source = chain();
    let calls = Cell::new(0);
    let mut a = || true;
    let mut owner = control(&mut a);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let mut b = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut fresh = control(&mut b);
    let before = calls.get();
    assert!(matches!(
        row.lift_ground_derivation_v2(b"{}", &mut fresh),
        Err(ChcQueryPlaybackError::ForeignControl)
    ));
    assert_eq!(calls.get(), before);
    assert!(matches!(
        row.expand_nullary_queries(&mut fresh),
        Err(ChcQueryPlaybackError::ForeignControl)
    ));
    assert_eq!(calls.get(), before);
}

#[test]
fn original_expired_deadline_refuses_before_callback() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(matches!(
        ChcQueryPlaybackControl::new(Instant::now(), &mut callback),
        Err(ChcQueryPlaybackError::DeadlineExceeded)
    ));
    assert_eq!(calls.get(), 0);
}

#[test]
fn cancellation_and_callback_panic_stay_sticky_across_calls() {
    let source = chain();
    let stop = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        !stop.get()
    };
    let mut owner = control(&mut callback);
    stop.set(true);
    assert!(matches!(
        source.query_obligations_with_playback(&mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
    let before = calls.get();
    stop.set(false);
    assert!(source.query_obligations_with_playback(&mut owner).is_err());
    assert_eq!(calls.get(), before);
    let panic_now = Cell::new(false);
    let mut callback = || {
        assert!(!panic_now.get());
        true
    };
    let mut owner = control(&mut callback);
    panic_now.set(true);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || source.query_obligations_with_playback(&mut owner)
    ))
    .is_err());
    panic_now.set(false);
    assert!(matches!(
        source.query_obligations_with_playback(&mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
}

#[test]
fn reached_preparation_and_expansion_cancellation_never_returns_partial_rows() {
    let source = chain();
    let polls = Cell::new(0);
    let limit = Cell::new(usize::MAX);
    let mut callback = || {
        polls.set(polls.get() + 1);
        polls.get() < limit.get()
    };
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let preparation = polls.get();
    let start = polls.get();
    let _ = row.expand_nullary_queries(&mut owner).unwrap();
    let expansion = polls.get() - start;
    for cut in [preparation / 2, preparation - 1] {
        polls.set(0);
        limit.set(cut);
        let mut owner = control(&mut callback);
        assert!(matches!(
            source.query_obligations_with_playback(&mut owner),
            Err(ChcQueryPlaybackError::Cancelled)
        ));
    }
    polls.set(0);
    limit.set(usize::MAX);
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    limit.set(polls.get() + expansion / 2);
    assert!(matches!(
        row.expand_nullary_queries(&mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
}

#[test]
fn reached_lift_and_final_publication_cancellation_returns_no_evidence() {
    let source = chain();
    let polls = Cell::new(0);
    let limit = Cell::new(usize::MAX);
    let mut callback = || {
        polls.set(polls.get() + 1);
        polls.get() < limit.get()
    };
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let (row, _) = row.expand_nullary_queries(&mut owner).unwrap();
    let bytes = wire(
        row.problem(),
        vec![
            step(1, "x", SmtValue::Int(7), vec![]),
            step(2, "y", SmtValue::Int(7), vec![0]),
        ],
        1,
    );
    let start = polls.get();
    let _ = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    let lift_polls = polls.get() - start;
    // Each independent attempt starts a new owner and creates its own bound row;
    // the measured refusal belongs to that owner's continuing preparation grant.
    for cut in [lift_polls / 2, lift_polls] {
        polls.set(0);
        limit.set(usize::MAX);
        let mut owner = control(&mut callback);
        let row = source
            .query_obligations_with_playback(&mut owner)
            .unwrap()
            .remove(0);
        let (row, _) = row.expand_nullary_queries(&mut owner).unwrap();
        limit.set(polls.get() + cut);
        assert!(matches!(
            row.lift_ground_derivation_v2(&bytes, &mut owner),
            Err(ChcQueryPlaybackError::Cancelled)
        ));
    }
}

#[test]
fn absent_live_query_or_stripped_negative_quantifier_cannot_publish_rows() {
    let empty = ChcProblem::new();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    assert!(matches!(
        empty.query_obligations_with_playback(&mut owner),
        Err(ChcQueryPlaybackError::UnsupportedProjection)
    ));
    let mut source = chain();
    source.mark_stripped_body_forall();
    assert!(matches!(
        source.query_obligations_with_playback(&mut owner),
        Err(ChcQueryPlaybackError::UnsupportedProjection)
    ));
}

#[test]
fn malformed_wire_and_missing_source_bindings_never_return_projected_evidence() {
    let source = chain();
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    assert!(row.lift_ground_derivation_v2(b"{}", &mut owner).is_err());
    let invalid = Counterexample::new(vec![]).with_ground_derivation(GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: vec![],
        }],
        query_step: 0,
    });
    assert!(invalid
        .ground_derivation_artifact_v2_with_progress(row.problem(), &mut || true)
        .is_err());
}
