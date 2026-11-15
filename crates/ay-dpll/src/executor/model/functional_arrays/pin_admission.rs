// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed native ownership for complete model-pin construction.
//!
//! This adapter supplies no allowance or model/proof authority. The composing
//! caller still validates the original source before capture and after cleanup.

use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ay_core::original_query::{
    CountedAdmissionError, OriginalAdmissionError, QueryError, StopReason,
};
use ay_core::resource::{current_check_stop, process_cancelled, CheckStop};
use ay_core::term::TermConstructionAdmission;

use crate::executor::model::{EvaluationArena, EvaluationAttempt};
use crate::executor::theories::FpStop;
use crate::executor_types::UnknownOrigin;

use super::{work_counter, Executor, Model};

pub(in crate::executor::model) struct PinAdmission {
    model_owner: Option<Arc<super::super::construction_owner::ModelConstructionOwner>>,
    stop: FpStop,
    original_check_stop: Option<CheckStop>,
    attempt: EvaluationAttempt,
    used: Arc<AtomicUsize>,
    arena: Arc<EvaluationArena>,
    source_bytes: usize,
    requested_bytes: Cell<usize>,
    paying: Cell<bool>,
    construction_refusal: Cell<Option<OriginalAdmissionError>>,
    term_limit: Option<usize>,
}

impl PinAdmission {
    pub(in crate::executor::model) fn charges_work_to(&self, used: &Arc<AtomicUsize>) -> bool {
        Arc::ptr_eq(&self.used, used)
    }
    pub(in crate::executor::model) fn captured_term_limit(&self) -> Option<usize> {
        self.term_limit
    }
    /// Retain prepaid MODEL DATA storage without retaining FpStop or invoking
    /// the old execution clock during a later public read.
    pub(in crate::executor::model) fn retain_data_memory(
        &self,
    ) -> super::super::evaluation_copies::RetainedEvaluationMemory {
        super::super::evaluation_copies::RetainedEvaluationMemory {
            _arena: Arc::clone(&self.arena),
            original: self.attempt.clone(),
            bytes: self.requested_bytes.get(),
            ceiling: self.term_limit,
        }
    }
    /// A retained native caller's absolute execution end, not a new allowance.
    pub(in crate::executor::model) fn refuse_deadline(&self) -> UnknownOrigin {
        self.refuse(UnknownOrigin::SolveDeadline)
    }
    pub(in crate::executor::model) fn refuse_source(&self) -> UnknownOrigin {
        match self.poll() {
            Err(origin) => origin,
            Ok(()) => self.refuse(UnknownOrigin::IncompleteSolverLane),
        }
    }
    /// Borrow the existing functional MODEL counter, not a fresh attempt grant.
    /// A native read can have its own stop frame while retaining that model's
    /// original cumulative counter. Model/attempt clones never replenish it.
    pub(in crate::executor::model) fn capture(
        exec: &Executor,
        model: &Model,
    ) -> Result<Self, UnknownOrigin> {
        let Some(data) = model.construction_owner.as_ref() else {
            return Err(UnknownOrigin::UnsupportedFeature);
        };
        // Retain the original ledger and preserve/latch native resource
        // origins BEFORE any source-validation poll can observe a stop.
        let mut admission = Self::capture_counter(exec, Arc::clone(&data.used))?;
        admission.model_owner = Some(Arc::clone(data));
        if !data.validate(exec) {
            admission.poll()?;
            return Err(UnknownOrigin::UnsupportedFeature);
        }
        Ok(admission)
    }

    /// Borrow the CURRENT read's existing ledger for preflight only. This
    /// does not establish a retained model binding or permit Exact model pins.
    pub(in crate::executor::model) fn capture_current_read(
        exec: &Executor,
    ) -> Result<Self, UnknownOrigin> {
        Self::capture_counter(exec, exec.evaluation_attempt().functional_work_counter())
    }

    fn capture_counter(exec: &Executor, used: Arc<AtomicUsize>) -> Result<Self, UnknownOrigin> {
        exec.poll_evaluation_stop().map_err(|origin| {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            origin
        })?;
        let attempt = exec.evaluation_attempt();
        let original_check_stop = current_check_stop().map_err(|_| {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            attempt.record_stop(UnknownOrigin::IncompleteSolverLane)
        })?;
        let arena = attempt.temporary_arena().map_err(|origin| {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            origin
        })?;
        let arena_storage =
            std::mem::size_of::<EvaluationArena>() + 2 * std::mem::size_of::<usize>();
        arena
            .check_usage(
                exec.ctx.terms.true_memory_bytes(),
                arena_storage,
                exec.evaluation_term_memory_limit(),
            )
            .map_err(|origin| attempt.record_stop(origin))?;
        let admission = Self {
            model_owner: None,
            stop: FpStop::from_executor_for_term_construction(exec),
            original_check_stop,
            attempt,
            used,
            arena: Arc::new(arena),
            source_bytes: exec.ctx.terms.true_memory_bytes(),
            requested_bytes: Cell::new(arena_storage),
            paying: Cell::new(false),
            construction_refusal: Cell::new(None),
            term_limit: exec.evaluation_term_memory_limit(),
        };
        admission
            .arena
            .check_usage(admission.source_bytes, arena_storage, admission.term_limit)
            .map_err(|origin| admission.refuse(origin))?;
        admission.poll()?;
        Ok(admission)
    }

    fn refuse(&self, origin: UnknownOrigin) -> UnknownOrigin {
        // Terminal MODEL storage, not an admitted work unit. A later read
        // frame cannot revive construction refused under this original grant.
        self.used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
        let first = self.attempt.record_stop(origin);
        self.stop.refuse(first);
        first
    }

    pub(in crate::executor::model) fn poll(&self) -> Result<(), UnknownOrigin> {
        if let Some(origin) = self.attempt.stop_origin() {
            return Err(self.refuse(origin));
        }
        self.stop.check().map_err(|origin| self.refuse(origin))?;
        // An opaque Boolean owner supplies no precise deadline/memory/raw-flag
        // cause. Preserve known origins above; otherwise withhold as incomplete.
        // Retain this original callback even after its TLS scope is restored.
        if process_cancelled() || self.original_check_stop.as_ref().is_some_and(|stop| stop()) {
            return Err(self.refuse(UnknownOrigin::IncompleteSolverLane));
        }
        // An opaque observer may return false after the live end/interrupt
        // changed. It supplies no authority to cross that original stop.
        if let Some(origin) = self.attempt.stop_origin() {
            return Err(self.refuse(origin));
        }
        self.stop.check().map_err(|origin| self.refuse(origin))?;
        if !work_counter::debit(&self.used, 0) {
            return Err(self.refuse(UnknownOrigin::DeterministicResourceBudget));
        }
        Ok(())
    }

    /// Re-observe a growing producer arena against this ORIGINAL ceiling and
    /// cumulative requests. This is no callback, capture, refund or new balance.
    pub(in crate::executor::model) fn check_source_usage(
        &self,
        source_bytes: usize,
    ) -> Result<(), UnknownOrigin> {
        self.arena
            .check_usage(source_bytes, self.requested_bytes.get(), self.term_limit)
            .map_err(|origin| self.refuse(origin))
    }

    pub(in crate::executor::model) fn matches_model(&self, model: &Model) -> bool {
        model.construction_owner.as_ref().is_some_and(|data| {
            self.model_owner
                .as_ref()
                .is_some_and(|owner| Arc::ptr_eq(owner, data))
                && Arc::ptr_eq(&self.used, &data.used)
        })
    }

    pub(in crate::executor::model) fn matches_current_read(&self, exec: &Executor) -> bool {
        let current = exec.evaluation_attempt();
        self.attempt.is_same_attempt(&current)
            && Arc::ptr_eq(&self.used, &current.functional_work_counter())
    }

    /// Prepay every direct progress debit against the SAME atomic counter and
    /// conservative cumulative storage requests before the opaque operation.
    /// Logical requested bytes are neither RSS nor a reusable storage refund.
    pub(in crate::executor::model) fn pay(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), UnknownOrigin> {
        // The retained stop callback can reenter native model construction.
        // Reject that before invoking it, without holding a RefMut or lock.
        if self.paying.replace(true) {
            self.note_construction_refusal(OriginalAdmissionError::Reentrant);
            return Err(self.refuse(UnknownOrigin::IncompleteSolverLane));
        }
        let mut entry = PaymentEntry {
            admission: self,
            completed: false,
        };
        let result = self.pay_entered(work, bytes);
        entry.completed = result.is_ok();
        result
    }

    fn pay_entered(&self, work: usize, bytes: usize) -> Result<(), UnknownOrigin> {
        self.poll()?;
        if !work_counter::debit(&self.used, work) {
            return Err(self.refuse(UnknownOrigin::DeterministicResourceBudget));
        }
        let requested = self
            .requested_bytes
            .get()
            .checked_add(bytes)
            .ok_or_else(|| self.refuse(UnknownOrigin::MemoryBudget))?;
        self.arena
            .check_usage(self.source_bytes, requested, self.term_limit)
            .map_err(|origin| self.refuse(origin))?;
        self.requested_bytes.set(requested);
        self.poll()
    }

    /// Latch a constructor-origin resource refusal before any caller retry.
    /// Precise already-observed interrupt/deadline/memory origins take priority.
    pub(in crate::executor::model) fn refuse_resource(&self) -> UnknownOrigin {
        match self.poll() {
            Err(origin) => origin,
            Ok(()) => self.refuse(UnknownOrigin::DeterministicResourceBudget),
        }
    }

    /// Caller must first dispose topology/row/snapshot scratch. Check the live
    /// producer accounting, release the arena, then perform a final owner poll.
    /// This preserves the existing capacity-accounting policy, not an all-RSS
    /// or allocator/hard-preemption guarantee. No work debit is refunded.
    pub(in crate::executor::model) fn finish(
        self,
        live_source_bytes: usize,
    ) -> Result<(), UnknownOrigin> {
        let Self {
            model_owner,
            stop,
            original_check_stop,
            attempt,
            used,
            arena,
            source_bytes: _,
            requested_bytes,
            paying: _,
            construction_refusal: _,
            term_limit,
        } = self;
        // Retain refusal custody while releasing scratch AND invoking the
        // terminal callback. An unwind must remain terminal on this model,
        // including when a later reader installs a fresh stop frame.
        let mut fence = TerminalFence {
            stop: &stop,
            attempt: &attempt,
            used: &used,
            completed: false,
        };
        let retained_bytes = if Arc::strong_count(&arena) > 1 {
            requested_bytes.get()
        } else {
            0
        };
        let checked = arena.check_usage(live_source_bytes, retained_bytes, term_limit);
        drop(arena);
        if let Some(origin) = attempt.stop_origin() {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            return Err(origin);
        }
        checked?;
        stop.check().map_err(|origin| {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            attempt.record_stop(origin)
        })?;
        if process_cancelled() || original_check_stop.as_ref().is_some_and(|stop| stop()) {
            used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            return Err(attempt.record_stop(stop.refuse(UnknownOrigin::IncompleteSolverLane)));
        }
        if let Some(origin) = attempt.stop_origin() {
            return Err(origin);
        }
        stop.check().map_err(|origin| attempt.record_stop(origin))?;
        if !work_counter::debit(&used, 0) {
            return Err(
                attempt.record_stop(stop.refuse(UnknownOrigin::DeterministicResourceBudget))
            );
        }
        fence.completed = true;
        drop(model_owner);
        Ok(())
    }

    fn note_construction_refusal(&self, error: OriginalAdmissionError) {
        if self.construction_refusal.get().is_none() {
            self.construction_refusal.set(Some(error));
        }
    }

    fn construction_error(&self, origin: UnknownOrigin) -> CountedAdmissionError {
        match origin {
            UnknownOrigin::MemoryBudget => CountedAdmissionError::Memory,
            UnknownOrigin::DeterministicResourceBudget => CountedAdmissionError::WorkExhausted,
            UnknownOrigin::SolveDeadline => {
                OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline)).into()
            }
            UnknownOrigin::InterruptFlag => {
                OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Cancelled)).into()
            }
            _ => CountedAdmissionError::Original(
                self.construction_refusal
                    .get()
                    .unwrap_or(OriginalAdmissionError::ObserverStopped),
            ),
        }
    }
}

/// Restore entry bookkeeping on every exit; an unwound callback cannot leave
/// the same model apparently eligible for another construction attempt.
struct PaymentEntry<'a> {
    admission: &'a PinAdmission,
    completed: bool,
}

impl Drop for PaymentEntry<'_> {
    fn drop(&mut self) {
        if !self.completed {
            if std::thread::panicking() {
                self.admission
                    .note_construction_refusal(OriginalAdmissionError::ObserverPanicked);
            }
            self.admission.refuse(UnknownOrigin::IncompleteSolverLane);
        }
        self.admission.paying.set(false);
    }
}

struct TerminalFence<'a> {
    stop: &'a FpStop,
    attempt: &'a EvaluationAttempt,
    used: &'a AtomicUsize,
    completed: bool,
}

impl Drop for TerminalFence<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.used.fetch_max(work_counter::REFUSED, Ordering::AcqRel);
            let first = self
                .attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            self.stop.refuse(first);
        }
    }
}

impl TermConstructionAdmission for PinAdmission {
    fn admit(&self, work: usize, bytes: usize) -> Result<(), CountedAdmissionError> {
        self.pay(work, bytes)
            .map_err(|origin| self.construction_error(origin))
    }

    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        // Core's construction errors are a coarse cross-crate projection.
        // Preserve the precise first origin on the SAME original attempt;
        // never infer a deadline/interrupt from a generic observer refusal.
        let origin = match error {
            CountedAdmissionError::StorageExhausted | CountedAdmissionError::Memory => {
                UnknownOrigin::MemoryBudget
            }
            CountedAdmissionError::WorkExhausted => UnknownOrigin::DeterministicResourceBudget,
            _ => UnknownOrigin::IncompleteSolverLane,
        };
        self.construction_error(PinAdmission::refuse(self, origin))
    }
}

#[cfg(test)]
mod tests;
