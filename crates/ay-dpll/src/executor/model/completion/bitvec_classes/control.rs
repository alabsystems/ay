// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed ownership for equality-class offers and cross-lane agreement.

use ay_core::resource::{
    current_check_stop, current_guard, enter_check_stop, CheckStop, CheckStopScope, Exhausted,
    Guard,
};
use ay_core::{TermData, TermId, TermStore};

use crate::executor::model::{EvaluationArena, EvaluationAttempt};
use crate::executor::theories::FpStop;
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

mod latch;

pub(in crate::executor) struct CandidateOwner {
    stop: FpStop,
    callback: CheckStop,
    guard: Option<Guard>,
    attempt: EvaluationAttempt,
    arena: EvaluationArena,
    source_bytes: usize,
    requested: usize,
    limit: Option<usize>,
    polling: bool,
}

impl CandidateOwner {
    /// Capture existing authority once. An arena accounts scratch; it is NOT
    /// a fresh work grant. Guard clones debit the original node and ancestors.
    pub(in crate::executor) fn capture(exec: &Executor) -> Result<Self, UnknownOrigin> {
        let attempt = exec.evaluation_attempt();
        let original = current_check_stop()
            .map_err(|_| attempt.record_stop(UnknownOrigin::IncompleteSolverLane))?;
        let guard = current_guard();
        let mut owner = Self {
            stop: FpStop::from_executor_for_term_construction(exec),
            callback: latch::capture(original, attempt.clone()),
            guard,
            arena: attempt.temporary_arena()?,
            attempt,
            source_bytes: exec.ctx.terms.true_memory_bytes(),
            requested: 0,
            limit: exec.evaluation_term_memory_limit(),
            polling: false,
        };
        owner.pay(0, 0)?;
        Ok(owner)
    }

    /// Observe only the original count still available; this allocates and
    /// reserves nothing. A missing count is unbounded, not a new grant.
    pub(in crate::executor) fn remaining_work(&self) -> Option<u64> {
        self.guard.as_ref().and_then(Guard::remaining)
    }

    /// Nested solvers may translate a Boolean stop to bare `Incomplete`.
    /// Share the original attempt's refusal latch through their callback so
    /// consuming a one-shot stop cannot make a later fallback look healthy.
    /// Declare this scope after its owner: restore TLS before owner teardown.
    pub(in crate::executor) fn enter_nested(&self) -> CheckStopScope {
        enter_check_stop(std::sync::Arc::clone(&self.callback))
    }

    pub(in crate::executor) fn refuse(&self, origin: UnknownOrigin) -> UnknownOrigin {
        self.attempt.record_stop(self.stop.refuse(origin))
    }

    pub(in crate::executor) fn poll(&mut self) -> Result<(), UnknownOrigin> {
        if self.polling {
            return Err(self.refuse(UnknownOrigin::IncompleteSolverLane));
        }
        if let Some(origin) = self.attempt.stop_origin() {
            return Err(origin);
        }
        self.stop.check().map_err(|origin| self.refuse(origin))?;
        if let Some(exhausted) = self.guard.as_ref().and_then(Guard::poll) {
            return Err(self.refuse(origin(exhausted)));
        }
        if ay_core::resource::process_cancelled() {
            return Err(self.refuse(UnknownOrigin::InterruptFlag));
        }
        // Mark before arbitrary caller code: unwinding cannot revive a later
        // pass by losing an observed/unfinished callback in this local owner.
        self.polling = true;
        let stopped = (self.callback)();
        self.polling = false;
        if stopped {
            return Err(self.refuse(UnknownOrigin::IncompleteSolverLane));
        }
        if let Some(origin) = self.attempt.stop_origin() {
            return Err(origin);
        }
        self.stop.check().map_err(|origin| self.refuse(origin))?;
        if let Some(exhausted) = self.guard.as_ref().and_then(Guard::poll) {
            return Err(self.refuse(origin(exhausted)));
        }
        Ok(())
    }

    pub(in crate::executor) fn pay(
        &mut self,
        work: usize,
        bytes: usize,
    ) -> Result<(), UnknownOrigin> {
        self.poll()?;
        let work = u64::try_from(work)
            .map_err(|_| self.refuse(UnknownOrigin::DeterministicResourceBudget))?;
        if let Some(guard) = &self.guard {
            guard.tick(work).map_err(|stop| self.refuse(origin(stop)))?;
        }
        self.requested = self
            .requested
            .checked_add(bytes)
            .ok_or_else(|| self.refuse(UnknownOrigin::MemoryBudget))?;
        self.arena
            .check_usage(self.source_bytes, self.requested, self.limit)?;
        self.poll()
    }

    /// A cumulative conservative allowance for these fixed-size container
    /// entries: spare capacity, hash controls and stack copies are included.
    /// It is logical requested storage, not a claim to bound allocator RSS.
    pub(in crate::executor) fn entries(&mut self, count: usize) -> Result<(), UnknownOrigin> {
        let bytes = count
            .checked_mul(128)
            .ok_or_else(|| self.refuse(UnknownOrigin::MemoryBudget))?;
        self.pay(count, bytes)
    }

    pub(in crate::executor) fn sort(&mut self, count: usize) -> Result<(), UnknownOrigin> {
        let work = count
            .checked_mul((usize::BITS - count.leading_zeros()) as usize + 1)
            .ok_or_else(|| self.refuse(UnknownOrigin::DeterministicResourceBudget))?;
        self.pay(work, 0)
    }

    /// Pre-admit children()'s allocation, including the let body. Charging
    /// before calling it avoids an unbounded temporary Vec ahead of the owner.
    pub(in crate::executor) fn children(
        &mut self,
        terms: &TermStore,
        term: TermId,
    ) -> Result<Vec<TermId>, UnknownOrigin> {
        let count = match terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => 0,
            TermData::App(_, args) => args.len(),
            TermData::Let(bindings, _) => bindings
                .len()
                .checked_add(1)
                .ok_or_else(|| self.refuse(UnknownOrigin::MemoryBudget))?,
            TermData::Ite(..) => 3,
            _ => 1,
        };
        self.entries(count)?;
        Ok(terms.children(term))
    }

    pub(in crate::executor) fn finish(&mut self, source_bytes: usize) -> Result<(), UnknownOrigin> {
        self.source_bytes = source_bytes;
        self.pay(0, 0)
    }
}

impl Drop for CandidateOwner {
    fn drop(&mut self) {
        if self.polling {
            self.refuse(UnknownOrigin::IncompleteSolverLane);
        }
    }
}

fn origin(stop: Exhausted) -> UnknownOrigin {
    match stop {
        Exhausted::Cancelled => UnknownOrigin::InterruptFlag,
        Exhausted::Deadline | Exhausted::Cpu => UnknownOrigin::SolveDeadline,
        Exhausted::Rlimit => UnknownOrigin::DeterministicResourceBudget,
        Exhausted::Memory => UnknownOrigin::MemoryBudget,
    }
}

#[cfg(test)]
mod tests;
