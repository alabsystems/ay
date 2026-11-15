// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn absolute_wall_uses_the_original_start_and_rejects_overflow() {
    let start = Instant::now().checked_sub(Duration::from_secs(5)).unwrap();
    let budget = Duration::from_secs(1);
    let deadline = replay_deadline(start, budget).unwrap();
    assert_eq!(deadline, start.checked_add(budget).unwrap());
    assert!(deadline < Instant::now(), "setup time must not be renewed");
    assert!(replay_deadline(start, Duration::MAX).is_err());
}

#[test]
fn default_deadline_overflow_precedes_progress_and_preserves_metadata() {
    let run = truth_run();
    let original = run.metadata().to_json_value();
    let mut calls = 0;
    let error = run
        .run_checked_replay_with_progress(Duration::MAX, &mut || {
            calls += 1;
            true
        })
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("cannot be represented as an absolute deadline"));
    assert_eq!(calls, 0);
    assert_eq!(run.metadata().to_json_value(), original);
    assert_eq!(
        run.run_checked_replay(Duration::MAX)
            .unwrap_err()
            .to_string(),
        error.to_string()
    );
}

#[test]
fn supplied_deadline_overflow_precedes_id_conversion_and_progress() {
    let run = truth_run();
    let conversions = Cell::new(0);
    let mut calls = 0;
    let error = run
        .run_checked_replay_with_binding_and_progress(
            ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
            ChcProofSolverIdentity::new("overflow-test"),
            ObservedId {
                conversions: &conversions,
            },
            None,
            Duration::MAX,
            &mut || {
                calls += 1;
                true
            },
        )
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("cannot be represented as an absolute deadline"));
    assert_eq!(conversions.get(), 0);
    assert_eq!(calls, 0);
}
