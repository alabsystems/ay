// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::CancellationToken;

#[test]
fn typed_report_entry_preserves_checked_identity_and_solve_telemetry() {
    let original = run();
    let token = CancellationToken::new();
    let expected = report(original.clone(), true).with_checked_replay(REPLAY_BUDGET);
    let actual =
        report(original, true).with_checked_replay_with_cancellation(REPLAY_BUDGET, &token);
    assert_eq!(
        actual.checked_replay().unwrap().summary().identity_sha256(),
        expected
            .checked_replay()
            .unwrap()
            .summary()
            .identity_sha256()
    );
    assert_eq!(actual.stop_reason(), expected.stop_reason());
    assert_eq!(actual.adaptive_trace(), expected.adaptive_trace());
    assert!(actual.cancellation_requested_at_return());
    assert!(actual.budget_report().total_elapsed >= SOLVE_ELAPSED);
    assert!(!token.is_cancelled());
}

#[test]
fn typed_parent_refusal_preserves_metadata_and_completion_snapshot() {
    for solve_cancelled in [false, true] {
        let original = run();
        let metadata = original.metadata().to_json_value();
        let parent = CancellationToken::new();
        let child = parent.child();
        parent.cancel();
        let stopped = report(original, solve_cancelled)
            .with_checked_replay_with_cancellation(REPLAY_BUDGET, &child);
        assert!(stopped.checked_replay().is_none());
        assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
        assert_eq!(stopped.stop_reason(), ChcProofRunStopReason::Definitive);
        assert_eq!(stopped.cancellation_requested_at_return(), solve_cancelled);
        assert!(stopped.budget_report().total_elapsed >= SOLVE_ELAPSED);
    }
}

#[test]
fn typed_precancelled_zero_budget_does_not_revoke_existing_evidence() {
    let checked = report(run(), false).with_checked_replay(REPLAY_BUDGET);
    let identity = checked
        .checked_replay()
        .unwrap()
        .summary()
        .identity_sha256();
    let elapsed = checked.budget_report().total_elapsed;
    let token = CancellationToken::new();
    token.cancel();
    let retained = checked.with_checked_replay_with_cancellation(Duration::ZERO, &token);
    assert_eq!(
        retained
            .checked_replay()
            .unwrap()
            .summary()
            .identity_sha256(),
        identity
    );
    assert_eq!(retained.budget_report().total_elapsed, elapsed);
    assert!(!retained.cancellation_requested_at_return());
}

#[test]
fn typed_token_does_not_change_ineligible_report() {
    let original = ChcPdrProofRun::new(
        ChcProblem::new(),
        VerifiedChcResult::from_validated(
            crate::ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        ),
        "typed-ineligible",
    );
    let metadata = original.metadata().to_json_value();
    let token = CancellationToken::new();
    token.cancel();
    let unchanged =
        report(original, false).with_checked_replay_with_cancellation(Duration::MAX, &token);
    assert_eq!(unchanged.proof_run().metadata().to_json_value(), metadata);
    assert_eq!(unchanged.budget_report().total_elapsed, SOLVE_ELAPSED);
    assert!(unchanged.checked_replay().is_none());
}
