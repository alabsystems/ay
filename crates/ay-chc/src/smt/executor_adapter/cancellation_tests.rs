// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::CancellationToken;
use std::time::Duration;

const SAT: &str = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n";
const UNSAT: &str =
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n";

fn deadline() -> Instant {
    Instant::now().checked_add(Duration::from_secs(60)).unwrap()
}

#[test]
fn ordinary_precancel_refuses_valid_and_malformed_surfaces() {
    let token = CancellationToken::new();
    token.cancel();
    let cancellation = ReplayCancellation::new(&token);
    for script in [SAT, UNSAT, "(malformed", ""] {
        assert!(smtlib_first_verdict_via_executor_with_limit(
            script,
            ReplayLimit::Cancellable {
                deadline: deadline(),
                cancellation: &cancellation
            },
            None,
        )
        .is_none());
    }
    assert!(token.is_cancelled());
}

#[test]
fn ordinary_live_cancellation_control_preserves_sat_and_unsat_verdicts() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    for (script, expected) in [(SAT, "sat"), (UNSAT, "unsat")] {
        let wall = deadline();
        let actual = smtlib_first_verdict_via_executor_with_limit(
            script,
            ReplayLimit::Cancellable {
                deadline: wall,
                cancellation: &cancellation,
            },
            None,
        );
        assert_eq!(actual.as_deref(), Some(expected));
        assert_eq!(
            actual,
            smtlib_first_verdict_via_executor_until(script, wall, None)
        );
    }
    assert!(!token.is_cancelled());
    assert!(!cancellation.is_cancelled());
}

#[test]
fn inherited_precancel_is_sticky_only_for_the_current_replay_attempt() {
    let parent = CancellationToken::new();
    let child = parent.child();
    let cancellation = ReplayCancellation::new(&child);
    parent.cancel();
    assert!(smtlib_first_verdict_via_executor_with_limit(
        SAT,
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation
        },
        None,
    )
    .is_none());
    parent.reset();
    assert!(!child.is_cancelled());
    assert!(smtlib_first_verdict_via_executor_with_limit(
        SAT,
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation
        },
        None,
    )
    .is_none());
    let retry = ReplayCancellation::new(&child);
    assert_eq!(
        smtlib_first_verdict_via_executor_with_limit(
            SAT,
            ReplayLimit::Cancellable {
                deadline: deadline(),
                cancellation: &retry
            },
            None,
        )
        .as_deref(),
        Some("sat"),
    );
}

#[test]
fn cancellation_does_not_replace_deadline_memory_or_override_guards() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    assert!(smtlib_first_verdict_via_executor_with_limit(
        SAT,
        ReplayLimit::Cancellable {
            deadline: Instant::now(),
            cancellation: &cancellation
        },
        None,
    )
    .is_none());
    assert!(smtlib_first_verdict_via_executor_with_limit(
        SAT,
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation
        },
        Some(1),
    )
    .is_none());
    assert!(smtlib_first_verdict_via_executor_with_limit(
        "(set-option :timeout 0)\n(assert false)\n(check-sat)\n",
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation
        },
        None,
    )
    .is_none());
    assert!(
        !cancellation.is_cancelled(),
        "non-cancellation limits do not poison the token"
    );
}
