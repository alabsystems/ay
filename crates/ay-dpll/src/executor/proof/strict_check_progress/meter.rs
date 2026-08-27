// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Aggregate proof-check resource metering and stop-signal diagnostics.

use super::*;

pub(super) struct StrictCheckMeter {
    work: usize,
    bytes: usize,
    max_work: usize,
    max_bytes: usize,
    pub(super) refusal: Option<StrictCheckRefusal>,
}

pub(super) fn executor_stopped(executor: &Executor, should_stop: &impl Fn() -> bool) -> bool {
    should_stop()
        || crate::memory::memory_exceeded(executor.memory_limit())
        || ay_sys::process_memory_exceeded()
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

impl StrictCheckMeter {
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

    pub(super) fn charge_while_running(
        &mut self,
        work_delta: usize,
        byte_delta: usize,
        stopped: impl FnOnce() -> bool,
        describe_stop: impl FnOnce() -> String,
    ) -> bool {
        if stopped() {
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
