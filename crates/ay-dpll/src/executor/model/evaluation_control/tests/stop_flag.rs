// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// `is_stopped` answers as `stop_origin().is_some()` without the lock: every
/// clone, on any thread, reads the first stop, and a fresh attempt none.
#[test]
fn the_first_stop_reaches_every_clone_and_no_fresh_attempt() {
    let attempt = EvaluationAttempt::default();
    let clone = attempt.clone();
    assert!(!clone.is_stopped());
    assert_eq!(clone.stop_origin(), None);
    assert_eq!(
        attempt.record_stop(UnknownOrigin::SolveDeadline),
        UnknownOrigin::SolveDeadline
    );
    assert!(clone.is_stopped());
    assert_eq!(
        clone.record_stop(UnknownOrigin::InterruptFlag),
        UnknownOrigin::SolveDeadline,
        "the first stop wins"
    );
    let elsewhere = clone.clone();
    let seen = std::thread::spawn(move || (elsewhere.is_stopped(), elsewhere.stop_origin()))
        .join()
        .expect("reader thread");
    assert_eq!(seen, (true, Some(UnknownOrigin::SolveDeadline)));
    let fresh = EvaluationAttempt::default();
    assert!(!fresh.is_stopped());
    assert_eq!(fresh.stop_origin(), None);
}
