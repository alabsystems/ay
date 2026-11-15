// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Search-batch ownership of cancellation, absolute wall time and term memory.
//! The observer is joined before publication, including on unwind. Cooperative
//! polling and opaque executor phases do not establish a hard latency bound.

use super::{memory, BmcSolver, SingleExecutorOutcome};
use crate::smt::executor_adapter::{InterruptObserver, ReplayCancellation};
use crate::ChcEngineResult;
use ay_core::time::Instant;
use std::sync::atomic::AtomicBool;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BatchPhase {
    Installed,
    Executed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AttemptStop {
    Cancelled,
    Deadline,
    Memory,
    Observer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BatchFailure {
    Unavailable,
    LocalDeadline,
    Stopped(AttemptStop),
}

impl BmcSolver {
    pub(super) fn execution_deadline(&self, deadline: Option<Instant>) -> Option<Instant> {
        [
            deadline,
            self.solve_deadline.get(),
            crate::smt::current_thread_solve_deadline(),
            crate::smt::deadline::current_smt_deadline(),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    pub(super) fn execution_stopped(&self, deadline: Option<Instant>) -> bool {
        self.batch_admission(deadline).is_err()
    }

    fn stop_execution(&self, cause: AttemptStop) -> BatchFailure {
        let cause = self.execution_stop.get().unwrap_or(cause);
        self.execution_stop.set(Some(cause));
        let mut stats = self.stats.borrow_mut();
        stats.exhausted_search = false;
        stats.budget_exhausted = cause == AttemptStop::Deadline;
        BatchFailure::Stopped(cause)
    }

    fn batch_admission(&self, local: Option<Instant>) -> Result<(), BatchFailure> {
        if let Some(cause) = self.execution_stop.get() {
            return Err(BatchFailure::Stopped(cause));
        }
        // The token, or the portfolio lane this BMC runs on (a nested BMC built
        // without a token still stops when its lane is cancelled).
        if self
            .config
            .base
            .cancellation_token
            .as_ref()
            .is_some_and(|token| token.is_cancelled())
            || crate::smt::deadline::lane_cancelled()
        {
            return Err(self.stop_execution(AttemptStop::Cancelled));
        }
        // Test the enclosing wall separately: a clamped local/global tie is
        // terminal, not permission to start another depth with a new budget.
        if self
            .execution_deadline(None)
            .is_some_and(|d| Instant::now() >= d)
        {
            return Err(self.stop_execution(AttemptStop::Deadline));
        }
        if !memory::Budget::capture(self.config.memory_budget, None).open() {
            return Err(self.stop_execution(AttemptStop::Memory));
        }
        if local.is_some_and(|d| Instant::now() >= d) {
            return Err(BatchFailure::LocalDeadline);
        }
        Ok(())
    }

    pub(super) fn single_batch_failure(
        &self,
        failure: BatchFailure,
        k: usize,
        first_unchecked_depth: Option<usize>,
        consecutive_unsat: usize,
    ) -> Option<SingleExecutorOutcome> {
        match failure {
            BatchFailure::Unavailable => None,
            BatchFailure::Stopped(_) => {
                Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown))
            }
            BatchFailure::LocalDeadline => Some(SingleExecutorOutcome::RetryFresh {
                start_depth: first_unchecked_depth.unwrap_or(k),
                consecutive_unsat: if first_unchecked_depth.is_some() {
                    0
                } else {
                    consecutive_unsat
                },
            }),
        }
    }

    pub(super) fn execute_controlled_batch(
        &self,
        exec: &mut ay_dpll::Executor,
        commands: &[ay_frontend::Command],
        deadline: Option<Instant>,
        mut observe: impl FnMut(BatchPhase, Option<&AtomicBool>),
    ) -> Result<Vec<String>, BatchFailure> {
        self.batch_admission(deadline)?;
        let deadline = self.execution_deadline(deadline);
        let memory = memory::Budget::capture(self.config.memory_budget, None);
        if !memory.constrain(exec) {
            return Err(self.stop_execution(AttemptStop::Memory));
        }
        let _memory = memory.install();
        // Snapshot the already-sticky BMC attempt, not merely its leaf atomic.
        // The shared adapter handles spawn failure, worker panic and joining.
        let cancellation = self
            .config
            .base
            .cancellation_token
            .as_ref()
            .map(ReplayCancellation::new);
        let mut observer = cancellation
            .as_ref()
            .map(InterruptObserver::new)
            .transpose()
            .map_err(|error| {
                tracing::debug!("BMC-exec: {error}");
                self.stop_execution(AttemptStop::Observer)
            })?;
        let interrupt = observer.as_ref().map(InterruptObserver::interrupt);
        exec.set_deadline(deadline);
        if let Some(interrupt) = &interrupt {
            exec.set_interrupt(interrupt.clone());
        }
        observe(BatchPhase::Installed, interrupt.as_deref());
        let result = self.batch_admission(deadline).and_then(|()| {
            Self::exec_commands_inner(exec, commands).ok_or(BatchFailure::Unavailable)
        });
        // Capture memory refusal while the executor and its last result still
        // exist. Cleanup or a new executor must not erase this attempt's stop.
        if !memory.executor_open(exec)
            || exec.unknown_origin() == Some(ay_dpll::UnknownOrigin::MemoryBudget)
        {
            self.stop_execution(AttemptStop::Memory);
        }
        let landing = self.batch_admission(deadline);
        observe(BatchPhase::Executed, interrupt.as_deref());
        // Do not renew the deadline or accept an output on a stopped landing.
        // Persistent executors retain the interrupt flag; the next batch
        // replaces it only after admission against the SAME sticky attempt.
        let observer_open = observer.as_mut().is_none_or(InterruptObserver::finish);
        exec.set_deadline(None);
        if !observer_open {
            self.stop_execution(
                if self
                    .config
                    .base
                    .cancellation_token
                    .as_ref()
                    .is_some_and(|token| token.is_cancelled())
                {
                    AttemptStop::Cancelled
                } else {
                    AttemptStop::Observer
                },
            );
        }
        self.batch_admission(deadline)?;
        landing?;
        result
    }
}

#[cfg(test)]
mod tests;
