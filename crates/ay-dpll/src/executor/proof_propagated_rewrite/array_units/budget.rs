// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One sticky envelope for the entire L1 structural-array replay invocation.
//! The owned stop closure observes the live deadline and shared interrupt;
//! executor RSS limits are captured and the process guard remains live.

use std::cell::Cell;

use super::super::{Executor, MAX_STORED_PROPAGATION_RECORDS, PLAN_NODE_BUDGET};

const MAX_WORK: usize = PLAN_NODE_BUDGET * MAX_STORED_PROPAGATION_RECORDS;
const MAX_BYTES: usize = 64 * 1024 * 1024;
const POLL_INTERVAL: usize = 1024;

pub(in crate::executor::proof_propagated_rewrite) struct ArrayReplayBudget {
    work_left: Cell<usize>,
    bytes_left: Cell<usize>,
    calls_since_poll: Cell<usize>,
    refused: Cell<bool>,
    stopped: Box<dyn Fn() -> bool>,
}

impl ArrayReplayBudget {
    pub(in crate::executor::proof_propagated_rewrite) fn new(executor: &Executor) -> Self {
        let should_stop = executor.make_should_stop();
        let memory_limit = executor.memory_limit();
        Self::with_controls(
            MAX_WORK,
            MAX_BYTES,
            Box::new(move || {
                should_stop()
                    || crate::memory::memory_exceeded(memory_limit)
                    || ay_sys::process_memory_exceeded()
            }),
        )
    }

    fn with_controls(work: usize, bytes: usize, stopped: Box<dyn Fn() -> bool>) -> Self {
        let budget = Self {
            work_left: Cell::new(work),
            bytes_left: Cell::new(bytes),
            calls_since_poll: Cell::new(0),
            refused: Cell::new(false),
            stopped,
        };
        budget.charge(0, 0);
        budget
    }

    /// Debit both counters atomically; no refusal or later candidate can reset
    /// this allowance. Zero-delta calls always poll, including final admission.
    pub(in crate::executor::proof_propagated_rewrite) fn charge(
        &self,
        work: usize,
        bytes: usize,
    ) -> bool {
        if self.refused.get() {
            return false;
        }
        let (Some(work_left), Some(bytes_left)) = (
            self.work_left.get().checked_sub(work),
            self.bytes_left.get().checked_sub(bytes),
        ) else {
            self.refused.set(true);
            return false;
        };
        // Reset on every poll, so this counter is always below POLL_INTERVAL
        // before incrementing; unlike a lifetime call counter it cannot wrap.
        let calls = self.calls_since_poll.get() + 1;
        if (work == 0 && bytes == 0) || calls == POLL_INTERVAL {
            self.calls_since_poll.set(0);
            if (self.stopped)() {
                self.refused.set(true);
                return false;
            }
        } else {
            self.calls_since_poll.set(calls);
        }
        self.work_left.set(work_left);
        self.bytes_left.set(bytes_left);
        true
    }
}

#[cfg(test)]
mod tests;
