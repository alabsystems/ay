// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only observation of completed transfers for one original attempt.

#![cfg(test)]

use super::EvaluationAttempt;
use std::cell::RefCell;

struct Observed {
    attempt: EvaluationAttempt,
    successes: usize,
    inspector: Option<fn(&ay_sat::ClauseTrace)>,
    inspections: usize,
}

thread_local! {
    static OBSERVED: RefCell<Option<Observed>> = const { RefCell::new(None) };
}

pub(super) fn note_successful_handoff(attempt: &EvaluationAttempt) {
    OBSERVED.with_borrow_mut(|slot| {
        if let Some(observed) = slot {
            // A nested proof fallback on a fresh executor must not satisfy
            // the assertion about the original primary solver's transfer.
            if observed.attempt.is_same_attempt(attempt) {
                observed.successes += 1;
            }
        }
    });
}

/// Borrow the actual transferred trace after its original-owner fence and
/// before proof assembly legitimately consumes it. No copy or retained trace.
pub(super) fn inspect_successful_handoff(attempt: &EvaluationAttempt, trace: &ay_sat::ClauseTrace) {
    let inspector = OBSERVED.with_borrow(|slot| {
        slot.as_ref()
            .filter(|observed| observed.attempt.is_same_attempt(attempt))
            .and_then(|observed| observed.inspector)
    });
    if let Some(inspect) = inspector {
        // Run outside the RefCell borrow: native validation may invoke controls.
        inspect(trace);
        OBSERVED.with_borrow_mut(|slot| {
            let observed = slot.as_mut().expect("active trace inspection");
            assert!(observed.attempt.is_same_attempt(attempt));
            observed.inspections += 1;
        });
    }
}

pub(in crate::executor::theories::bv) fn observe<T>(
    attempt: &EvaluationAttempt,
    run: impl FnOnce() -> T,
) -> (T, usize) {
    observe_inner(attempt, None, run)
}

pub(in crate::executor::theories::bv) fn observe_trace<T>(
    attempt: &EvaluationAttempt,
    inspector: fn(&ay_sat::ClauseTrace),
    run: impl FnOnce() -> T,
) -> (T, usize) {
    observe_inner(attempt, Some(inspector), run)
}

fn observe_inner<T>(
    attempt: &EvaluationAttempt,
    inspector: Option<fn(&ay_sat::ClauseTrace)>,
    run: impl FnOnce() -> T,
) -> (T, usize) {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            OBSERVED.with_borrow_mut(|slot| *slot = None);
        }
    }
    OBSERVED.with_borrow_mut(|slot| {
        assert!(slot.is_none(), "overlapping consuming-handoff observation");
        *slot = Some(Observed {
            attempt: attempt.clone(),
            successes: 0,
            inspector,
            inspections: 0,
        });
    });
    let _reset = Reset;
    let result = run();
    let successes = OBSERVED.with_borrow(|slot| {
        let observed = slot.as_ref().expect("active consuming-handoff observation");
        if observed.inspector.is_some() {
            assert_eq!(
                observed.inspections, observed.successes,
                "every successful original transfer must inspect its actual trace"
            );
        }
        observed.successes
    });
    (result, successes)
}
