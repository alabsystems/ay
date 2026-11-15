// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn metadata_only_never_launches_replay_or_changes_the_value() {
    let parent = CancellationToken::new();
    for cancelled in [false, true] {
        if cancelled {
            parent.cancel();
        }
        let report = checked_replay_if_requested(
            String::from("original"),
            QueryProofReplay::MetadataOnly,
            Some(&parent),
            |_, _, _| panic!("metadata-only must not start replay"),
        );
        assert_eq!(report, "original");
    }
}

#[test]
fn absent_parent_preserves_one_replay_call_and_the_exact_budget() {
    for budget in [Duration::ZERO, Duration::from_nanos(987654321)] {
        let mut calls = 0;
        let result = checked_replay_if_requested(
            41,
            QueryProofReplay::Checked(budget),
            None,
            |report, actual_budget, progress| {
                calls += 1;
                assert_eq!(actual_budget, budget);
                for _ in 0..8 {
                    assert!(progress());
                }
                report + 1
            },
        );
        assert_eq!(calls, 1);
        assert_eq!(result, 42);
    }
}

#[test]
fn precancelled_parent_preserves_the_unstarted_report() {
    let parent = CancellationToken::new();
    parent.cancel();
    let original = vec![1, 2, 3];
    let pointer = original.as_ptr();
    let result = checked_replay_if_requested(
        original,
        QueryProofReplay::Checked(Duration::from_secs(10)),
        Some(&parent),
        |_, _, _| panic!("pre-cancelled replay must not start"),
    );
    assert_eq!(result, [1, 2, 3]);
    assert_eq!(result.as_ptr(), pointer);
}

#[test]
fn active_replay_observes_the_same_parent_and_cannot_resume_after_reset() {
    let parent = CancellationToken::new();
    let result = checked_replay_if_requested(
        17,
        QueryProofReplay::Checked(Duration::from_secs(10)),
        Some(&parent),
        |report, _, progress| {
            assert!(progress());
            parent.cancel();
            assert!(!progress());
            parent.reset();
            assert!(!parent.is_cancelled());
            assert!(
                !progress(),
                "observed cancellation is call-local and sticky"
            );
            assert!(!progress());
            report
        },
    );
    assert_eq!(result, 17);
}

#[test]
fn cancellation_after_admission_but_before_first_poll_is_observed() {
    let parent = CancellationToken::new();
    checked_replay_if_requested(
        (),
        QueryProofReplay::Checked(Duration::from_secs(10)),
        Some(&parent),
        |(), _, progress| {
            parent.cancel();
            assert!(!progress());
            parent.reset();
            assert!(!progress());
        },
    );
}

#[test]
fn fresh_replay_may_retry_without_a_cancelled_child_poisoning_the_parent() {
    let parent = CancellationToken::new();
    let child = parent.child();
    child.cancel();
    for _ in 0..2 {
        checked_replay_if_requested(
            (),
            QueryProofReplay::Checked(Duration::from_secs(10)),
            Some(&parent),
            |(), _, progress| {
                assert!(progress());
                parent.cancel();
                assert!(!progress());
                parent.reset();
                assert!(!progress());
            },
        );
    }
    assert!(!parent.is_cancelled());
    assert!(child.is_cancelled());
}
