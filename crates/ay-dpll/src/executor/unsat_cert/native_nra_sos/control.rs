// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One terminal allowance for SOS search, independent replay, and publication.
//!
//! Charged work/bytes are cumulative across phases, not measurements of every
//! allocation or peak memory. Existing kernel operations, allocation, memory
//! probes, and destruction can contain opaque intervals. Callers must poll after
//! scratch destruction and before publication; this is not a hard latency bound.
//! Process memory is sampled periodically, not on every inner progress call;
//! arena boundaries and caller callbacks force samples before and after work.

use crate::executor::{Executor, SolveDeadlineCell};
use ay_core::{time::Instant, TermStore};
use std::fmt;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

const MAX_WORK: usize = 16_000_000;
const MAX_CHARGED_BYTES: usize = 256 * 1024 * 1024;
const MEMORY_POLL_INTERVAL: usize = 1024;

#[derive(Clone, Copy)]
enum MemorySample {
    Skip,
    Now,
}

/// Why one attempt stopped. Every stop is sticky; only the reason differs.
///
/// A spent lane allowance means this lane found no evidence inside the work it
/// is allowed to spend, exactly like a bounded SOS search returning no witness.
/// It says nothing about the executor's own clocks or memory, so the mint may
/// keep an already checked presentation. A terminal stop is a refusal of the
/// executor itself; no attempt may continue past it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Stop {
    /// The cumulative work or charged-byte allowance of this lane is spent.
    Allowance,
    /// Interrupt, deadline, a memory ceiling, or a caller refusal.
    Terminal,
}

/// Owns control handles, never an executor/term-store borrow. A prepared result
/// can retain this same allowance through mutable proof construction and bind.
pub(super) struct Control<'a> {
    callback: Option<&'a mut dyn FnMut(usize, usize) -> bool>,
    interrupt: Option<Arc<AtomicBool>>,
    search_deadline: SolveDeadlineCell,
    certification_deadline: SolveDeadlineCell,
    original_deadline: Option<Instant>,
    memory_limit: Option<usize>,
    term_memory_limit: Option<usize>,
    work: usize,
    charged_bytes: usize,
    memory_polls_left: usize,
    stopped: Option<Stop>,
}

impl fmt::Debug for Control<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Control")
            .field("work", &self.work)
            .field("charged_bytes", &self.charged_bytes)
            .field("stopped", &self.stopped)
            .finish_non_exhaustive()
    }
}

impl Control<'static> {
    pub(super) fn new(executor: &Executor) -> Self {
        Self::capture(executor, None)
    }
}

impl<'a> Control<'a> {
    #[cfg(test)]
    pub(super) fn with_progress(
        executor: &Executor,
        callback: &'a mut dyn FnMut(usize, usize) -> bool,
    ) -> Self {
        Self::capture(executor, Some(callback))
    }

    fn capture(
        executor: &Executor,
        callback: Option<&'a mut dyn FnMut(usize, usize) -> bool>,
    ) -> Self {
        let original_deadline = executor
            .solve_deadline
            .get()
            .into_iter()
            .chain(executor.certification_deadline.get())
            .min();
        Self {
            callback,
            interrupt: executor.solve_interrupt.clone(),
            search_deadline: executor.solve_deadline.clone(),
            certification_deadline: executor.certification_deadline.clone(),
            original_deadline,
            memory_limit: executor.memory_limit(),
            term_memory_limit: executor.term_memory_limit(),
            work: 0,
            charged_bytes: 0,
            memory_polls_left: 0,
            stopped: None,
        }
    }

    pub(super) fn stopped(&self) -> bool {
        self.stopped.is_some()
    }

    /// The reason this attempt stopped, once it has.
    pub(super) fn stop(&self) -> Option<Stop> {
        self.stopped
    }

    /// Poll owned resources and charge one phase's incremental accounting.
    /// The evolving arena is checked separately with `poll_terms` at boundaries.
    pub(super) fn poll(&mut self, work: usize, bytes: usize) -> bool {
        self.poll_inner(None, work, bytes)
    }

    /// Also sample the supplied arena against the captured per-store ceiling.
    /// No arena borrow escapes this call. Use this before and after builders.
    pub(super) fn poll_terms(&mut self, terms: &TermStore, work: usize, bytes: usize) -> bool {
        self.poll_inner(Some(terms), work, bytes)
    }

    fn poll_inner(&mut self, terms: Option<&TermStore>, work: usize, bytes: usize) -> bool {
        if self.stopped.is_some() {
            return false;
        }
        // Latch BEFORE callbacks and opaque probes. If a lower frame catches a
        // panic, this same attempt cannot resume or authorize another phase.
        // The latch is terminal; only the two allowance checks below relabel it.
        self.stopped = Some(Stop::Terminal);
        let memory_sample =
            if terms.is_some() || self.callback.is_some() || self.memory_polls_left == 0 {
                self.memory_polls_left = MEMORY_POLL_INTERVAL - 1;
                MemorySample::Now
            } else {
                self.memory_polls_left -= 1;
                MemorySample::Skip
            };
        if !self.resources_live(terms, memory_sample) {
            return false;
        }
        let Some(work) = self.work.checked_add(work).filter(|&sum| sum <= MAX_WORK) else {
            self.stopped = Some(Stop::Allowance);
            return false;
        };
        let Some(charged_bytes) = self
            .charged_bytes
            .checked_add(bytes)
            .filter(|&sum| sum <= MAX_CHARGED_BYTES)
        else {
            self.stopped = Some(Stop::Allowance);
            return false;
        };
        let delta_work = work - self.work;
        self.work = work;
        self.charged_bytes = charged_bytes;
        if self
            .callback
            .as_mut()
            .is_some_and(|callback| !callback(delta_work, bytes))
            || !self.resources_live(terms, memory_sample)
        {
            return false;
        }
        self.stopped = None;
        true
    }

    fn deadline_live(&self) -> bool {
        let now = Instant::now();
        self.original_deadline.is_none_or(|deadline| now < deadline)
            && self
                .search_deadline
                .get()
                .is_none_or(|deadline| now < deadline)
            && self
                .certification_deadline
                .get()
                .is_none_or(|deadline| now < deadline)
    }

    fn interrupted(&self) -> bool {
        self.interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }

    fn resources_live(&self, terms: Option<&TermStore>, memory_sample: MemorySample) -> bool {
        !self.interrupted()
            && self.deadline_live()
            && !terms.is_some_and(|terms| {
                self.term_memory_limit
                    .is_some_and(|limit| terms.instance_memory_exceeded(limit))
            })
            && (matches!(memory_sample, MemorySample::Skip)
                || (!crate::memory::memory_exceeded(self.memory_limit)
                    && !ay_sys::process_memory_exceeded()))
            // Recheck after potentially opaque probes as well as after the
            // caller callback. A true callback is not a deadline extension.
            && !self.interrupted()
            && self.deadline_live()
    }
}

#[cfg(test)]
mod tests;
