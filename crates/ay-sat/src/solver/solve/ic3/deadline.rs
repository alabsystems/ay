// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental IC3 queries sample an actual absolute deadline even without an
//! atomic interrupt. One propagation/analysis/cleanup operation remains opaque;
//! this is cooperative polling, not a wall-clock latency guarantee.

use super::{AssumeResult, SatUnknownReason, Solver};

const DEADLINE_INTERVAL: usize = 256;

pub(super) struct DeadlinePoll {
    remaining: usize,
}

impl DeadlinePoll {
    pub(super) fn new() -> Self {
        Self { remaining: 0 }
    }

    #[cfg(test)]
    pub(super) fn check(&mut self, solver: &Solver) -> Option<SatUnknownReason> {
        self.check_controlled(solver, &|| false)
    }

    pub(super) fn check_controlled<F>(
        &mut self,
        solver: &Solver,
        should_stop: &F,
    ) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        if self.remaining == 0 {
            self.remaining = DEADLINE_INTERVAL - 1;
            solver.solve_stop_reason(should_stop)
        } else {
            self.remaining -= 1;
            solver.active_interrupt_reason()
        }
    }
}

impl Solver {
    // Called only after the incremental driver's raw frame and learned-clause
    // cleanup have finished. No late model/core escapes a timed-out query.
    #[cfg(test)]
    pub(super) fn finish_ic3_query(&mut self, result: AssumeResult) -> AssumeResult {
        self.finish_ic3_query_controlled(result, &|| false)
    }

    pub(super) fn finish_ic3_query_controlled<F>(
        &mut self,
        result: AssumeResult,
        should_stop: &F,
    ) -> AssumeResult
    where
        F: Fn() -> bool + ?Sized,
    {
        if let Some(reason) = self.solve_stop_reason(should_stop) {
            drop(result);
            self.declare_assume_unknown_with_reason(reason)
        } else {
            result
        }
    }
}

#[cfg(test)]
mod tests;
