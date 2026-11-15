// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fixed eager-CNF trace capture. Ordinary and incremental APIs stay unchanged.

use super::*;
pub use crate::clause_trace::originals::ConsumingTraceStop;
use crate::clause_trace::originals::OriginalControl;

/// Failure to publish an owned trace does not itself refute the SAT result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ConsumingTraceError {
    /// Unsupported storage/event history, poisoned capture, or local quota.
    /// Independent proof reconstruction may use its existing remaining grant.
    #[error("consuming clause trace is unavailable")]
    Unavailable,
    /// An original caller control refused; no alternative may revive it.
    #[error(transparent)]
    Stopped(ConsumingTraceStop),
}

/// Read-only retained refusal from one capture, with no reset or new grant.
/// Keep this through solver cleanup when a caller may retry another lane.
#[derive(Clone, Debug)]
pub struct ConsumingTraceControl(OriginalControl);

impl ConsumingTraceControl {
    /// Read the first observed ORIGINAL stop without polling or issuing work.
    /// Local capture refusal alone returns `None`.
    #[must_use]
    pub fn observed_stop(&self) -> Option<ConsumingTraceStop> {
        self.0.stop_reason()
    }
}

impl Solver {
    /// Capture a fresh fixed-CNF solver's original rows without a second copy.
    ///
    /// Only the consuming handoff can expose this trace. Scopes, a prior solve,
    /// other proof writers, late/theory originals and original-empty inputs are
    /// outside this mode and refuse publication; they never silently fall back
    /// to an incomplete snapshot. This is a storage API, not a proof validator.
    pub fn enable_consuming_clause_trace(
        &mut self,
    ) -> Result<ConsumingTraceControl, ConsumingTraceError> {
        if !self.arena.is_empty()
            || !self.cold.original_ledger.is_empty()
            || self.has_empty_clause
            || self.cold.has_ever_scoped
            || self.cold.has_solved_once
            || self.proof_manager.is_some()
            || self.cold.internal_lrat_enabled
            || self.cold.clause_trace.is_some()
            || self.cold.lrat_enabled
            || !self.cold.original_ledger.trace_transfer_supported()
        {
            return Err(ConsumingTraceError::Unavailable);
        }
        let Some(control) = OriginalControl::capture(
            self.cold.interrupt.clone(),
            self.cold.deadline_interrupt.clone(),
            self.cold.solve_deadline,
        ) else {
            let mut trace = ClauseTrace::new();
            trace.mark_proof_work_exhausted();
            self.cold.clause_trace = Some(trace);
            return Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Observer));
        };
        let mut trace = ClauseTrace::new();
        if !trace.begin_original_transfer(control.clone()) {
            return Err(ConsumingTraceError::Unavailable);
        }
        crate::clause_trace::note_clause_trace_armed();
        self.cold.clause_trace = Some(trace);
        // Retain the armed control before invoking arbitrary caller code.
        // Even a caught panic cannot turn this solver into a fresh capture.
        let open = control.open();
        if !open {
            if let Some(trace) = self.cold.clause_trace.as_mut() {
                trace.mark_proof_work_exhausted();
            }
        }
        self.refresh_proof_consumer_state();
        if open {
            Ok(ConsumingTraceControl(control))
        } else {
            Err(capture_error(&control))
        }
    }

    pub(super) fn consuming_trace_pending(&self) -> bool {
        self.cold
            .clause_trace
            .as_ref()
            .is_some_and(ClauseTrace::original_transfer_pending)
    }

    pub(super) fn note_consuming_original(&mut self, supported: bool) {
        let bytes = self.cold.original_ledger.trace_storage_bytes();
        let count = self.cold.original_ledger.num_clauses();
        // Registration now changes only count/size fields. No literal copy,
        // per-original EntryMeta, or historical 4*len+16 copy debit remains.
        let admitted = supported
            && !self.cold.has_ever_scoped
            && !self.cold.has_solved_once
            && self.cold.original_ledger.trace_transfer_supported()
            && self.charge_proof_bookkeeping(4);
        if let Some(trace) = self.cold.clause_trace.as_mut() {
            if !admitted || bytes.is_none_or(|bytes| !trace.note_ledger_original(count, bytes)) {
                trace.mark_proof_work_exhausted();
                if let Some(control) = trace.original_control() {
                    control.refuse();
                }
            }
        }
    }

    /// Check the exact admitted original IDs, not their numeric range. Live
    /// completeness is bounded by the hint chain, not a full ledger scan.
    /// Every binary-search probe debits both existing proof work and the
    /// captured Guard; neither an ambient replacement nor a fresh grant is used.
    pub(super) fn consuming_original_contains(&mut self, id: u64) -> Option<bool> {
        let control = self.cold.clause_trace.as_ref()?.original_control()?;
        let mut low = 0;
        let mut high = self.cold.original_ledger.clause_ids().len();
        while low < high {
            if !control.work(1, &mut |units| {
                self.consuming_work_open(&control, &mut || false, units)
            }) {
                return None;
            }
            let mid = low + (high - low) / 2;
            match self.cold.original_ledger.clause_ids()[mid].cmp(&id) {
                std::cmp::Ordering::Less => low = mid + 1,
                std::cmp::Ordering::Greater => high = mid,
                std::cmp::Ordering::Equal => return Some(true),
            }
        }
        Some(false)
    }

    /// Consume this fixed-CNF solver, moving (not cloning) its original arena.
    ///
    /// The borrowed stop predicate remains in force through solver/control
    /// cleanup. Unavailable capture is separate from original caller refusal;
    /// semantic proof replay remains required even on a successful handoff.
    /// No deadline, work allowance, or proof authority is created here.
    pub fn into_consuming_clause_trace(
        mut self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<ClauseTrace, ConsumingTraceError> {
        let control = self
            .cold
            .clause_trace
            .as_ref()
            .and_then(ClauseTrace::original_control);
        let Some(control) = control else {
            drop(self);
            return if should_stop() {
                Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Observer))
            } else {
                Err(ConsumingTraceError::Unavailable)
            };
        };
        let result = self.finish_consuming_trace(&control, should_stop);
        drop(self);
        // Capture failure must not short-circuit genuine caller observation.
        // Cleanup precedes this fence even when no trace could be produced.
        let accepted = caller_open(&control, should_stop);
        let error = capture_error(&control);
        drop(control);
        // Release the last retained callback before the final caller fence.
        if !accepted {
            drop(result);
            return Err(error);
        }
        if should_stop() {
            drop(result);
            return Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Observer));
        }
        result.ok_or(ConsumingTraceError::Unavailable)
    }

    fn finish_consuming_trace(
        &mut self,
        control: &OriginalControl,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Option<ClauseTrace> {
        if self.cold.has_ever_scoped
            || self.scope_depth() != 0
            || self.proof_manager.is_some()
            || self.cold.internal_lrat_enabled
            || !self.cold.original_ledger.trace_transfer_supported()
            || !self.consuming_work_open(control, should_stop, 0)
        {
            return None;
        }
        let mut trace = self.cold.clause_trace.take()?;
        if !trace.has_empty_clause() {
            return None;
        }
        let ledger = std::mem::replace(&mut self.cold.original_ledger, cold::OriginalLedger::new());
        let originals = ledger.into_trace_arena()?;
        if !trace.finish_original_transfer(originals, self.total_num_vars(), &mut |units| {
            self.consuming_work_open(control, should_stop, units)
        }) {
            return None;
        }
        for row in trace.entries() {
            if !control.work(1, &mut |units| {
                self.consuming_work_open(control, should_stop, units)
            }) || self.is_original_clause_id(row.id) != row.is_original
            {
                return None;
            }
        }
        trace.stamp_solver_provenance(self.total_num_vars(), &[]);
        self.consuming_work_open(control, should_stop, 0)
            .then_some(trace)
    }

    fn consuming_work_open(
        &mut self,
        control: &OriginalControl,
        should_stop: &mut dyn FnMut() -> bool,
        units: u64,
    ) -> bool {
        if self.cold.process_memory_interrupt {
            control.stop(ConsumingTraceStop::Memory);
        }
        if !caller_open(control, should_stop) || !control.open() {
            return false;
        }
        if !self.charge_proof_bookkeeping(units) {
            control.refuse();
            return false;
        }
        true
    }
}

fn capture_error(control: &OriginalControl) -> ConsumingTraceError {
    control.stop_reason().map_or(
        ConsumingTraceError::Unavailable,
        ConsumingTraceError::Stopped,
    )
}

fn caller_open(control: &OriginalControl, should_stop: &mut dyn FnMut() -> bool) -> bool {
    if !control.caller_open() {
        return false;
    }
    if should_stop() {
        control.stop(ConsumingTraceStop::Observer);
        return false;
    }
    control.caller_open()
}

#[cfg(test)]
#[path = "consuming_clause_trace/tests.rs"]
mod tests;
