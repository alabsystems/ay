// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::{Instant, ReplayLimit};
use std::cell::Cell;
use std::time::Duration;

fn times() -> (Instant, Instant) {
    let before = Instant::now();
    (before, before + Duration::from_secs(1))
}

#[test]
fn legacy_phase_preserves_results_without_reading_clock() {
    for proposed in [None, Some(7)] {
        let called = Cell::new(0);
        let result = ReplayLimit::Legacy.phase_with_clock(
            || panic!("legacy compatibility must not sample an absolute wall"),
            || {
                called.set(called.get() + 1);
                proposed
            },
        );
        assert_eq!(result, proposed);
        assert_eq!(called.get(), 1);
    }
}

#[test]
fn live_phase_preserves_result_and_samples_both_boundaries() {
    let (before, deadline) = times();
    let samples = Cell::new(0);
    let result = ReplayLimit::Until(deadline).phase_with_clock(
        || {
            samples.set(samples.get() + 1);
            before
        },
        || Some(17),
    );
    assert_eq!(result, Some(17));
    assert_eq!(samples.get(), 2);
}

#[test]
fn deadline_tie_and_past_refuse_before_starting_phase() {
    let (_, deadline) = times();
    for now in [deadline, deadline + Duration::from_nanos(1)] {
        let result = ReplayLimit::Until(deadline).phase_with_clock(
            || now,
            || -> Option<()> { panic!("expired phase must not start") },
        );
        assert_eq!(result, None);
    }
}

#[test]
fn phase_work_cannot_renew_its_deadline() {
    let (before, deadline) = times();
    let now = Cell::new(before);
    let result = ReplayLimit::Until(deadline).phase_with_clock(
        || now.get(),
        || {
            now.set(deadline);
            Some(23)
        },
    );
    assert_eq!(result, None);
}

struct DropAt<'a> {
    now: &'a Cell<Instant>,
    deadline: Instant,
    dropped: &'a Cell<bool>,
}

impl Drop for DropAt<'_> {
    fn drop(&mut self) {
        self.now.set(self.deadline);
        self.dropped.set(true);
    }
}

#[test]
fn closure_local_destruction_precedes_final_admission() {
    let (before, deadline) = times();
    let now = Cell::new(before);
    let dropped = Cell::new(false);
    let result = ReplayLimit::Until(deadline).phase_with_clock(
        || now.get(),
        || {
            let _owned_phase_state = DropAt {
                now: &now,
                deadline,
                dropped: &dropped,
            };
            Some("proposed certificate")
        },
    );
    assert!(dropped.get());
    assert_eq!(result, None);
}

#[test]
fn refused_proposal_is_dropped_without_becoming_a_result() {
    let (before, deadline) = times();
    let now = Cell::new(before);
    let dropped = Cell::new(false);
    let result = ReplayLimit::Until(deadline).phase_with_clock(
        || now.get(),
        || {
            now.set(deadline);
            Some(DropAt {
                now: &now,
                deadline,
                dropped: &dropped,
            })
        },
    );
    assert!(result.is_none());
    assert!(dropped.get());
}

#[test]
fn failed_phase_still_samples_its_final_boundary() {
    let (before, deadline) = times();
    let samples = Cell::new(0);
    let result = ReplayLimit::Until(deadline).phase_with_clock(
        || {
            samples.set(samples.get() + 1);
            before
        },
        || None::<()>,
    );
    assert_eq!(result, None);
    assert_eq!(samples.get(), 2);
}

#[test]
fn composed_phases_share_one_origin_and_stop_at_refusal() {
    let (before, deadline) = times();
    let now = Cell::new(before);
    let limit = ReplayLimit::Until(deadline);
    let called = Cell::new(0);
    let result = (|| {
        for index in 0..5 {
            limit.phase_with_clock(
                || now.get(),
                || {
                    called.set(called.get() + 1);
                    if index == 2 {
                        now.set(deadline);
                    }
                    Some(())
                },
            )?;
        }
        Some(())
    })();
    assert_eq!(result, None);
    assert_eq!(called.get(), 3);
}

#[test]
fn optional_presentation_absence_is_not_phase_refusal() {
    let (before, deadline) = times();
    let limit = ReplayLimit::Until(deadline);
    assert_eq!(
        limit.phase_with_clock(|| before, || Some(None::<String>)),
        Some(None)
    );
    assert_eq!(
        limit.phase_with_clock(|| deadline, || Some(None::<String>)),
        None
    );
}

#[test]
fn precancel_refuses_before_clock_or_phase_work() {
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    token.cancel();
    let limit = ReplayLimit::Cancellable {
        deadline: times().1,
        cancellation: &cancellation,
    };
    assert!(limit
        .phase_with_clock(
            || panic!("precancel must precede clock sampling"),
            || -> Option<()> { panic!("precancel must precede work") },
        )
        .is_none());
}

#[test]
fn cancellation_during_clock_sample_precedes_phase_work() {
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    let (before, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    assert!(limit
        .phase_with_clock(
            || {
                token.cancel();
                before
            },
            || -> Option<()> { panic!("clock-sample cancellation must precede work") },
        )
        .is_none());
    token.reset();
    assert!(cancellation.is_cancelled());
}

#[test]
fn observed_cancellation_during_work_cannot_be_reset_before_admission() {
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    let worker = cancellation.clone();
    let (before, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    assert!(limit
        .phase_with_clock(
            || before,
            || {
                token.cancel();
                assert!(worker.is_cancelled());
                token.reset();
                Some("proposed certificate")
            },
        )
        .is_none());
    assert!(!token.is_cancelled());
}

#[test]
fn cancellation_during_final_clock_sample_rejects_proposal() {
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    let (before, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    let mut samples = 0;
    assert_eq!(
        limit.phase_with_clock(
            || {
                samples += 1;
                if samples == 2 {
                    token.cancel();
                }
                before
            },
            || Some(31),
        ),
        None
    );
    assert_eq!(samples, 2);
    token.reset();
    assert!(cancellation.is_cancelled());
}

#[test]
fn deadline_expiry_does_not_cancel_caller_or_parent() {
    let parent = crate::CancellationToken::new();
    let token = parent.child();
    let cancellation = super::ReplayCancellation::new(&token);
    let (_, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    assert_eq!(limit.phase_with_clock(|| deadline, || Some(())), None);
    assert!(!cancellation.is_cancelled());
    assert!(!token.is_cancelled());
    assert!(!parent.is_cancelled());
    assert_eq!(limit.deadline(), Some(deadline));
    assert!(std::ptr::eq(limit.cancellation().unwrap(), &cancellation));
}

#[test]
fn live_cancellable_phase_preserves_deadline_and_result() {
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    let (before, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    assert_eq!(limit.phase_with_clock(|| before, || Some(47)), Some(47));
    assert_eq!(limit.deadline(), Some(deadline));
    assert!(!cancellation.is_cancelled());
}

#[test]
fn cancellation_in_local_destruction_precedes_final_admission() {
    struct CancelOnDrop<'a>(&'a crate::CancellationToken);
    impl Drop for CancelOnDrop<'_> {
        fn drop(&mut self) {
            self.0.cancel();
        }
    }
    let token = crate::CancellationToken::new();
    let cancellation = super::ReplayCancellation::new(&token);
    let (before, deadline) = times();
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    let result = limit.phase_with_clock(
        || before,
        || {
            let _owned_phase_state = CancelOnDrop(&token);
            Some("proposed certificate")
        },
    );
    assert_eq!(result, None);
    token.reset();
    assert!(cancellation.is_cancelled());
}

#[test]
fn admitted_completed_check_ignores_a_stop_after_it_returns() {
    let (before, deadline) = times();
    let now = Cell::new(before);
    let samples = Cell::new(0);
    let clock = || {
        samples.set(samples.get() + 1);
        now.get()
    };
    // The deadline lands as the check's last step completes: still accepted.
    let result = ReplayLimit::Until(deadline).admit_with_clock(clock, || {
        now.set(deadline);
        Some("completed check")
    });
    assert_eq!(result, Some("completed check"));
    assert_eq!(samples.get(), 1, "only the entry is sampled");
    // Negative control: an already-expired entry never starts the operation.
    let result = ReplayLimit::Until(deadline).admit_with_clock(
        || deadline,
        || -> Option<()> { panic!("expired admission must not start") },
    );
    assert_eq!(result, None);
}
