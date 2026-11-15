// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Propagate an opaque nested refusal into the original evaluation attempt.

use std::cell::RefCell;
use std::sync::Arc;

use ay_core::resource::CheckStop;

use super::{EvaluationAttempt, UnknownOrigin};

thread_local! {
    // Track invocation, not ownership. Distinct threads may legitimately poll
    // the same callback concurrently; only recursion on this thread refuses.
    static ACTIVE: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

struct Latch {
    original: Option<CheckStop>,
    attempt: EvaluationAttempt,
}

pub(super) fn capture(original: Option<CheckStop>, attempt: EvaluationAttempt) -> CheckStop {
    let latch = Arc::new(Latch { original, attempt });
    Arc::new(move || latch.poll())
}

impl Latch {
    fn poll(&self) -> bool {
        if self.attempt.stop_origin().is_some() {
            return true;
        }
        let Some(original) = &self.original else {
            return false;
        };
        // self remains owned by the callback's Arc for the whole invocation.
        // The pointer is an identity token only; it is never dereferenced.
        let identity = std::ptr::from_ref(self) as usize;
        let admitted = ACTIVE
            .try_with(|active| {
                let Ok(mut active) = active.try_borrow_mut() else {
                    return false;
                };
                if active.contains(&identity) || active.try_reserve(1).is_err() {
                    return false;
                }
                active.push(identity);
                true
            })
            .unwrap_or(false);
        if !admitted {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            return true;
        }
        let mut invocation = Invocation {
            identity,
            attempt: &self.attempt,
            completed: false,
        };
        let stopped = original();
        if stopped {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
        invocation.completed = true;
        // A reentrant invocation or another worker may have recorded the stop
        // even when this original callback itself returned false.
        self.attempt.stop_origin().is_some()
    }
}

struct Invocation<'a> {
    identity: usize,
    attempt: &'a EvaluationAttempt,
    completed: bool,
}

impl Drop for Invocation<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
        let _ = ACTIVE.try_with(|active| {
            if let Ok(mut active) = active.try_borrow_mut() {
                if active.last() == Some(&self.identity) {
                    active.pop();
                } else {
                    self.attempt
                        .record_stop(UnknownOrigin::IncompleteSolverLane);
                }
            } else {
                self.attempt
                    .record_stop(UnknownOrigin::IncompleteSolverLane);
            }
        });
    }
}
