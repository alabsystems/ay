// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn phase_observation_survives_parent_reset_and_later_work_success() {
    let caller = CancellationToken::new();
    let reached_later_phase = Cell::new(false);
    let result = checked_attempt(Duration::from_secs(60), &caller, |_, attempt| {
        let phase = attempt.child().child();
        caller.cancel();
        assert!(phase.is_cancelled());
        caller.reset();
        reached_later_phase.set(true);
        assert!(attempt.child().is_cancelled());
        Some(17)
    });
    assert!(reached_later_phase.get());
    assert_eq!(result, None);
    assert!(!caller.is_cancelled());
    assert_eq!(
        checked_attempt(Duration::from_secs(60), &caller, |_, _| Some(18)),
        Some(18)
    );
}

#[test]
fn a_local_phase_timeout_does_not_poison_other_phases_or_the_caller() {
    let caller = CancellationToken::new();
    assert_eq!(
        checked_attempt(Duration::from_secs(60), &caller, |_, attempt| {
            let phase = attempt.child();
            phase.cancel();
            assert!(phase.is_cancelled());
            assert!(!attempt.child().is_cancelled());
            Some(23)
        }),
        Some(23)
    );
    assert!(!caller.is_cancelled());
}

struct ObserveOnDrop<'a> {
    caller: &'a CancellationToken,
    phase: CancellationToken,
}

impl Drop for ObserveOnDrop<'_> {
    fn drop(&mut self) {
        self.caller.cancel();
        assert!(self.phase.is_cancelled());
        self.caller.reset();
    }
}

#[test]
fn cancellation_observed_during_context_cleanup_prevents_admission() {
    let caller = CancellationToken::new();
    assert_eq!(
        checked_attempt(Duration::from_secs(60), &caller, |_, attempt| {
            let _cleanup = ObserveOnDrop {
                caller: &caller,
                phase: attempt.child(),
            };
            Some(29)
        }),
        None
    );
    assert!(!caller.is_cancelled());
}

#[test]
fn no_work_runs_after_entry_refusal_and_parent_deadline_is_not_extended() {
    let caller = CancellationToken::new();
    let entered = Cell::new(false);
    let work = |_, _: &CancellationToken| {
        entered.set(true);
        Some(31)
    };
    for budget in [Duration::ZERO, Duration::MAX] {
        assert_eq!(checked_attempt(budget, &caller, work), None);
    }
    caller.cancel();
    assert_eq!(
        checked_attempt(Duration::from_secs(60), &caller, work),
        None
    );
    caller.reset();
    {
        let _scope = ScopedSmtDeadline::install_until(Instant::now());
        assert_eq!(
            checked_attempt(Duration::from_secs(60), &caller, work),
            None
        );
    }
    assert!(!entered.get());
    let parent = Instant::now() + Duration::from_secs(30);
    let _scope = ScopedSmtDeadline::install_until(parent);
    assert_eq!(
        checked_attempt(Duration::from_secs(60), &caller, |deadline, _| {
            assert_eq!(deadline, parent);
            Some(37)
        }),
        Some(37)
    );
}
