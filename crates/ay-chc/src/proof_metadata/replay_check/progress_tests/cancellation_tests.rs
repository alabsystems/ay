// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::CancellationToken;

#[test]
fn live_typed_token_preserves_exact_checked_ground_evidence() {
    let run = truth_run();
    let parent = CancellationToken::new();
    let token = parent.child();
    let expected = run.run_checked_replay(BUDGET).unwrap();
    let checked = run
        .run_checked_replay_with_cancellation(BUDGET, &token)
        .unwrap();
    assert_eq!(
        checked.summary().identity_sha256(),
        expected.summary().identity_sha256()
    );
    assert!(!parent.is_cancelled());
    assert!(!token.is_cancelled());
}

#[test]
fn precancelled_parent_declines_before_borrowed_callback_or_metadata_changes() {
    let run = truth_run();
    let metadata = run.metadata().to_json_value();
    let parent = CancellationToken::new();
    let token = parent.child().child();
    parent.cancel();
    assert_interrupted(run.run_checked_replay_with_progress_and_cancellation(
        BUDGET,
        &mut || panic!("pre-cancelled entry must not call user code"),
        Some(&token),
    ));
    assert_interrupted(run.run_checked_replay_with_cancellation(BUDGET, &token));
    assert_eq!(run.metadata().to_json_value(), metadata);
}

#[test]
fn typed_entry_preserves_zero_and_overflow_precedence() {
    let run = truth_run();
    let token = CancellationToken::new();
    token.cancel();
    for budget in [Duration::ZERO, Duration::MAX] {
        assert_eq!(
            run.run_checked_replay_with_cancellation(budget, &token)
                .unwrap_err()
                .to_string(),
            run.run_checked_replay(budget).unwrap_err().to_string(),
        );
    }
}

#[test]
fn token_cancellation_at_every_public_poll_rejects_the_attempt() {
    let run = truth_run();
    let mut samples = 0;
    let token = CancellationToken::new();
    run.run_checked_replay_with_progress_and_cancellation(
        BUDGET,
        &mut || {
            samples += 1;
            true
        },
        Some(&token),
    )
    .unwrap();
    assert!(samples > 2);
    for stop_at in 1..=samples {
        let parent = CancellationToken::new();
        let token = parent.child();
        let mut calls = 0;
        assert_interrupted(run.run_checked_replay_with_progress_and_cancellation(
            BUDGET,
            &mut || {
                calls += 1;
                if calls == stop_at {
                    parent.cancel();
                }
                true
            },
            Some(&token),
        ));
        assert_eq!(calls, stop_at);
    }
}

#[test]
fn wrapper_setup_never_grants_a_fresh_smt_wall() {
    let run = truth_run();
    let token = CancellationToken::new();
    let started = Instant::now().checked_sub(Duration::from_secs(5)).unwrap();
    assert_interrupted(run.run_checked_replay_with_controls_started_at(
        started,
        Duration::from_secs(1),
        &mut || panic!("expired original wrapper wall"),
        Some(&token),
    ));
    assert!(!token.is_cancelled());
}
