// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Aggregate proof-check resource metering and stop-signal diagnostics.

use super::*;
use crate::api::proofs::EnvelopeStop;

pub(super) struct StrictCheckMeter {
    work: usize,
    bytes: usize,
    max_work: usize,
    max_bytes: usize,
    pub(super) refusal: Option<StrictCheckRefusal>,
    /// The typed stop behind a `Cancelled` refusal, classified when the walk
    /// observed it (P4a.1), for the executor's `certification_stop`.
    pub(super) stop: Option<EnvelopeStop>,
}

pub(super) fn executor_stopped(executor: &Executor, should_stop: &impl Fn() -> bool) -> bool {
    let stop = strided_memory_poll(should_stop, executor.memory_limit());
    if !stop.poll() {
        return false;
    }
    executor.note_certification_stop(stop.reason().unwrap_or_else(|| typed_stop_signal(executor)));
    true
}

/// Name which of [`executor_stopped`]'s four signals is currently asserted, for
/// the cancellation probe.
///
/// The hot path deliberately collapses interrupt / deadline / executor-memory /
/// process-memory into one boolean, so a cancelled strict check used to report
/// only the disjunction — "interrupt, solve deadline, or memory limit". That is
/// the whole differential diagnosis, and it was missing: telling those apart
/// required hand-instrumenting four sites and rebuilding. (The answer, measured
/// on the model-checker-consumer `dyn_ptr` CHC obligation, was the DEADLINE 233 times out of
/// 233 — never the interrupt, never either memory guard.)
///
/// Re-polls each signal individually rather than threading state out of the hot
/// path, so it costs nothing unless `--probe-strict-check` is set and a stop has
/// already been observed. A signal that flipped in between reports as
/// `none-now`, which is itself worth seeing.
pub(super) fn describe_stop_signal(executor: &Executor) -> String {
    let interrupt = executor.solve_interrupt_is_set();
    let deadline = executor.solve_deadline_state();
    let exec_mem = crate::memory::memory_exceeded(executor.memory_limit());
    let proc_mem = ay_sys::process_memory_exceeded();
    if !interrupt && !exec_mem && !proc_mem && !deadline.starts_with("expired") {
        return format!("none-now (deadline={deadline})");
    }
    let mut parts: Vec<String> = Vec::new();
    if interrupt {
        parts.push("interrupt".to_string());
    }
    if deadline.starts_with("expired") {
        parts.push(format!("deadline {deadline}"));
    }
    if exec_mem {
        parts.push(format!(
            "executor-memory(limit={:?})",
            executor.memory_limit()
        ));
    }
    if proc_mem {
        parts.push("process-memory".to_string());
    }
    parts.join(" + ")
}

/// The typed stop behind a cancelled walk, read at the moment the walk
/// observed it: the interrupt, the solve deadline (a backstop), a portfolio
/// lane's memory share. An opaque/reset signal remains Caller: it is not
/// evidence of a memory breach. Sampled OS memory and GuardTree/caller stops
/// are recorded directly by StopPoll and do not use this fallback.
pub(super) fn typed_stop_signal(executor: &Executor) -> EnvelopeStop {
    if executor.solve_interrupt_is_set() {
        EnvelopeStop::Interrupt
    } else if executor.solve_deadline.expired() {
        EnvelopeStop::Backstop
    } else if ay_sys::current_memory_group_soft_tripped() {
        EnvelopeStop::LaneShare
    } else {
        EnvelopeStop::Caller
    }
}

impl StrictCheckMeter {
    /// Aggregate metered work consumed so far, surfaced by the
    /// `_reporting_work` wrapper and replayed verbatim by
    /// #strict-walk-memo. Purely structural — see that wrapper's note on why
    /// this figure is machine- and load-independent.
    pub(super) fn work(&self) -> usize {
        self.work
    }

    /// The verdict of a walk this meter governed, read once the walk has
    /// returned (#completed-check-accepted).
    ///
    /// A refusal the walk OBSERVED is final and is named by the limb that
    /// gave it: `Cancelled` for a stop, `ResourceLimit` for this envelope's
    /// budget. That includes a walk that returned `Ok` after a refused
    /// callback (a validator that swallowed the refusal and took another
    /// route), so no refusal ever authenticates a document. A stop the walk
    /// never observed, because it arrived after the walk's last callback, is
    /// not consulted: nothing here polls. A genuine verdict about the proof is
    /// returned unchanged.
    pub(super) fn settle<T>(
        &self,
        outcome: Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        match (outcome, self.refusal) {
            (Ok(_) | Err(ProofCheckError::ResourceLimit), Some(StrictCheckRefusal::Cancelled)) => {
                Err(ProofCheckError::Cancelled)
            }
            (Ok(_), Some(StrictCheckRefusal::BudgetRefused)) => Err(ProofCheckError::ResourceLimit),
            (other, _) => other,
        }
    }

    pub(super) fn production() -> Self {
        Self::with_limits(MAX_CHECK_WORK, MAX_CHECK_BYTES)
    }

    pub(super) fn with_limits(max_work: usize, max_bytes: usize) -> Self {
        Self {
            work: 0,
            bytes: 0,
            max_work,
            max_bytes,
            refusal: None,
            stop: None,
        }
    }

    pub(super) fn charge(&mut self, work_delta: usize, byte_delta: usize) -> bool {
        let Some(work) = self.work.checked_add(work_delta) else {
            return false;
        };
        let Some(bytes) = self.bytes.checked_add(byte_delta) else {
            return false;
        };
        if work > self.max_work || bytes > self.max_bytes {
            return false;
        }
        self.work = work;
        self.bytes = bytes;
        true
    }

    /// `classify_stop` names the stop the first time one is observed.
    pub(super) fn charge_while_running(
        &mut self,
        work_delta: usize,
        byte_delta: usize,
        stopped: impl FnOnce() -> bool,
        describe_stop: impl FnOnce() -> String,
        classify_stop: impl FnOnce() -> Option<EnvelopeStop>,
    ) -> bool {
        if stopped() {
            if self.refusal.is_none() {
                self.stop = classify_stop();
            }
            self.refusal.get_or_insert(StrictCheckRefusal::Cancelled);
            probe_strict_check_refusal(|| {
                format!(
                    "cancelled: {} (work {} of {}, bytes {} of {})",
                    describe_stop(),
                    self.work,
                    self.max_work,
                    self.bytes,
                    self.max_bytes
                )
            });
            return false;
        }
        if self.charge(work_delta, byte_delta) {
            return true;
        }
        self.refusal
            .get_or_insert(StrictCheckRefusal::BudgetRefused);
        probe_strict_check_refusal(|| {
            format!(
                "budget: work {}+{} of {}, bytes {}+{} of {}",
                self.work, work_delta, self.max_work, self.bytes, byte_delta, self.max_bytes
            )
        });
        false
    }
}
