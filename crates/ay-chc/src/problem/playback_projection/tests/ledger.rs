// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Callback continuity only, not a complete allocation/pricing theorem.

use super::*;
use ay_core::original_query::{QueryError, StopReason, WorkBudget};
use std::cell::Cell;
use std::ops::ControlFlow;

fn input(row: &ChcQueryPlayback<'_>) -> Vec<u8> {
    wire(
        row.problem(),
        vec![
            step(1, "x", SmtValue::Int(7), vec![]),
            step(2, "y", SmtValue::Int(7), vec![0]),
        ],
        1,
    )
}

#[test]
fn one_borrowed_work_budget_spans_prepare_expand_lift_and_final_fence() {
    let end = Instant::now() + Duration::from_secs(20);
    let source = chain();
    let admitted = Cell::new(0u64);
    let mut checkpoint = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    let mut callback = || match budget.charge(1) {
        Ok(()) => {
            admitted.set(admitted.get() + 1);
            true
        }
        Err(_) => false,
    };
    let mut owner = ChcQueryPlaybackControl::new(end, &mut callback).unwrap();
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let prepared = admitted.get();
    let (row, changed) = row.expand_nullary_queries(&mut owner).unwrap();
    assert!(changed && admitted.get() > prepared);
    let expanded = admitted.get();
    let bytes = input(&row);
    let (artifact, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert!(admitted.get() > expanded);
    assert_eq!(
        view.steps().map(|s| s.clause_index()).collect::<Vec<_>>(),
        [1, 2, 3, 4]
    );
    assert_eq!(view.step(3).unwrap().premises(), [2]);
    drop(view);
    drop(artifact);
    drop(bytes);
    drop(row);
    owner.poll().unwrap();
    drop(owner);
    drop(callback);
    assert_eq!(budget.remaining(), 1_000_000 - admitted.get());
    budget.charge(0).unwrap();
}

#[test]
fn original_work_budget_stop_cannot_publish_or_revive_after_observer_reset() {
    let end = Instant::now() + Duration::from_secs(20);
    let source = chain();
    let stopped = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut checkpoint = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else if stopped.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    let mut callback = || {
        calls.set(calls.get() + 1);
        budget.charge(1).is_ok()
    };
    let mut owner = ChcQueryPlaybackControl::new(end, &mut callback).unwrap();
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let (row, _) = row.expand_nullary_queries(&mut owner).unwrap();
    let bytes = input(&row);
    stopped.set(true);
    assert!(matches!(
        row.lift_ground_derivation_v2(&bytes, &mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
    let before = calls.get();
    stopped.set(false);
    assert!(matches!(
        row.lift_ground_derivation_v2(&bytes, &mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
    assert_eq!(calls.get(), before);
    drop(owner);
    drop(callback);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn original_work_exhaustion_is_preserved_without_a_second_projection_grant() {
    let end = Instant::now() + Duration::from_secs(20);
    let source = chain();
    let offer = Cell::new(1usize);
    let mut checkpoint = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000_000, &mut checkpoint);
    let mut callback = || budget.charge(offer.get()).is_ok();
    let mut owner = ChcQueryPlaybackControl::new(end, &mut callback).unwrap();
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let (row, _) = row.expand_nullary_queries(&mut owner).unwrap();
    let bytes = input(&row);
    offer.set(1_000_001);
    assert!(matches!(
        row.lift_ground_derivation_v2(&bytes, &mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
    offer.set(1);
    assert!(matches!(
        row.lift_ground_derivation_v2(&bytes, &mut owner),
        Err(ChcQueryPlaybackError::Cancelled)
    ));
    drop(owner);
    drop(callback);
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}
