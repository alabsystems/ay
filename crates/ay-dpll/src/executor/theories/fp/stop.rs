// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One sticky stop owner shared by stateless FP construction, transfer and SAT.

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;
use ay_fp::FpBuildError;

use crate::executor::model::EvaluationReadControls;
use crate::executor::{Executor, SolveDeadlineCell};
use crate::executor_types::UnknownOrigin;

/// Most stop checks one attempt performs between two operating-system memory
/// observations.
const MEMORY_POLL_INTERVAL: u32 = 1_024;

/// Longest wall-clock gap between two operating-system memory observations
/// while checks keep arriving (a tenth of the CLI memory watchdog's tick).
const MEMORY_POLL_PERIOD: Duration = Duration::from_millis(10);

/// Checks between two wall-clock reads of the period test. A clock read is
/// cheap but not free (about 23 ns here), and it was a quarter of the fixed
/// Float64 `fp.rem` solve's user time when every check took one.
const MEMORY_CLOCK_STRIDE: u32 = 16;

/// Rate limit for one attempt's operating-system memory observation.
///
/// `FpStop::check` runs at every construction checkpoint, for every Tseitin
/// definition, and at least four times per clause transferred into SAT. A
/// process-memory observation is not an atomic load: on Linux it opens and
/// reads `/proc/self/statm` and calls `getrusage`, on macOS it is a
/// `task_info` RPC. Taken on every check, those syscalls were about 70 s of the
/// 85 s the CLI needed for a Float64 `fp.rem` query (25.9M observations,
/// nearly all of them during clause transfer, about 2.7 us each); the same
/// query takes 2.3 s with the process memory limit disabled (`--memory 0`).
///
/// The first check of an attempt always observes, so an attempt that starts
/// over budget is refused before it builds anything. After that an observation
/// is due once `MEMORY_POLL_INTERVAL` checks or `MEMORY_POLL_PERIOD` of wall
/// time have passed since the previous one, whichever comes first. The wall
/// clock is read only every `MEMORY_CLOCK_STRIDE` checks, so a sparsely polled
/// phase (the SAT callback runs once per 100 conflicts) still observes within
/// `MEMORY_CLOCK_STRIDE` polls of the period elapsing. Interrupt, deadline and the
/// term-store admission snapshot are not rate limited. Growth between two
/// observations is what the allocator's hard ceiling
/// (`ay_sys::arm_hard_memory_ceiling`) and the CLI memory watchdog exist to
/// refuse.
///
/// A gate lives as long as the attempt it limits: an FP construction owns one
/// inside its [`FpStop`], and a model evaluation attempt owns one for every
/// stop poll it makes (`Executor::poll_evaluation_stop`), so the per-term
/// polls of one evaluation share a single rate limit.
#[derive(Default)]
pub(in crate::executor) struct MemoryPollGate {
    checks_since_observation: Cell<u32>,
    observed_at: Cell<Option<Instant>>,
}

impl MemoryPollGate {
    pub(in crate::executor) fn new() -> Self {
        Self::default()
    }

    /// [`Self::due`], reading `clock` only every `MEMORY_CLOCK_STRIDE` checks
    /// and when the first check or the interval forces an observation anyway.
    pub(in crate::executor) fn due_lazily(&self, clock: impl FnOnce() -> Instant) -> bool {
        let checks = self.checks_since_observation.get().saturating_add(1);
        if self.observed_at.get().is_some()
            && checks < MEMORY_POLL_INTERVAL
            && !checks.is_multiple_of(MEMORY_CLOCK_STRIDE)
        {
            self.checks_since_observation.set(checks);
            return false;
        }
        self.due(clock())
    }

    /// Whether the check made at `now` must take a fresh observation.
    fn due(&self, now: Instant) -> bool {
        let checks = self.checks_since_observation.get().saturating_add(1);
        let due = self.observed_at.get().is_none_or(|observed| {
            checks >= MEMORY_POLL_INTERVAL
                || now.saturating_duration_since(observed) >= MEMORY_POLL_PERIOD
        });
        if due {
            self.checks_since_observation.set(0);
            self.observed_at.set(Some(now));
        } else {
            self.checks_since_observation.set(checks);
        }
        due
    }
}

/// The production memory source: the term-store admission snapshot on every
/// check, the operating-system `observe` only when `due` (the schedule of a
/// [`MemoryPollGate`]) says an observation is due.
fn memory_source(
    term_memory_exceeded: bool,
    due: impl Fn() -> bool + Send + 'static,
    observe: impl Fn() -> bool + Send + 'static,
) -> Box<dyn Fn() -> bool + Send> {
    Box::new(move || term_memory_exceeded || (due() && observe()))
}

pub(in crate::executor) struct FpStop {
    interrupt: Option<Arc<AtomicBool>>,
    deadline: SolveDeadlineCell,
    // An explicitly captured original end for mutable term construction.
    construction_end: Option<Instant>,
    memory_exceeded: Box<dyn Fn() -> bool + Send>,
    refusal: Cell<Option<UnknownOrigin>>,
    read_controls: Option<EvaluationReadControls>,
}

impl FpStop {
    /// Capture controls without borrowing the executor during construction.
    ///
    /// The deadline and process-memory observations remain live; the latter is
    /// rate limited by [`MemoryPollGate`]. The term-store admission is a
    /// snapshot: stateless encoding only borrows that store, and its owner must
    /// recheck the executor after any later mutable term work.
    pub(in crate::executor) fn from_executor(executor: &Executor) -> Self {
        let gate = MemoryPollGate::new();
        Self::from_executor_gated(executor, move || gate.due_lazily(Instant::now))
    }

    /// [`Self::from_executor`] whose operating-system memory observation
    /// follows `due`, the schedule of a [`MemoryPollGate`] that outlives this
    /// stop. A fresh gate always observes on its first check, so a stop built
    /// per poll (one per evaluated term) would take one syscall per poll.
    pub(in crate::executor) fn from_executor_gated(
        executor: &Executor,
        due: impl Fn() -> bool + Send + 'static,
    ) -> Self {
        let read_controls = executor.evaluation_read_controls();
        let memory_limit = executor
            .memory_limit()
            .into_iter()
            .chain(
                read_controls
                    .as_ref()
                    .and_then(|controls| controls.memory_limit),
            )
            .min();
        let term_memory_exceeded = executor
            .evaluation_term_memory_limit()
            .is_some_and(|limit| executor.ctx.terms.instance_memory_exceeded(limit));
        let mut stop = Self::with_sources(
            executor.solve_interrupt.clone(),
            executor.solve_deadline.clone(),
            memory_source(term_memory_exceeded, due, move || {
                crate::memory::memory_exceeded(memory_limit) || ay_sys::process_memory_exceeded()
            }),
        );
        stop.read_controls = read_controls;
        stop
    }

    /// Preserve the currently earliest absolute end while producer terms grow.
    /// The live control cell can shorten it, but later restoration/extension
    /// cannot renew this construction's original end. No timer/grant is created.
    pub(in crate::executor) fn from_executor_for_term_construction(executor: &Executor) -> Self {
        let mut stop = Self::from_executor(executor);
        stop.construction_end = stop
            .deadline
            .get()
            .into_iter()
            .chain(
                stop.read_controls
                    .as_ref()
                    .and_then(|controls| controls.deadline),
            )
            .min();
        stop
    }

    fn with_sources(
        interrupt: Option<Arc<AtomicBool>>,
        deadline: SolveDeadlineCell,
        memory_exceeded: Box<dyn Fn() -> bool + Send>,
    ) -> Self {
        Self {
            interrupt,
            deadline,
            construction_end: None,
            memory_exceeded,
            refusal: Cell::new(None),
            read_controls: None,
        }
    }

    pub(in crate::executor) fn check(&self) -> Result<(), UnknownOrigin> {
        if let Some(origin) = self.refusal.get() {
            return Err(origin);
        }
        // Match Executor::should_abort_theory_loop's source priority.
        let origin = if self
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || self
                .read_controls
                .as_ref()
                .is_some_and(|controls| controls.interrupt.load(Ordering::Relaxed))
        {
            UnknownOrigin::InterruptFlag
        } else if self.deadline.expired()
            || self
                .construction_end
                .is_some_and(|end| Instant::now() >= end)
            || self
                .read_controls
                .as_ref()
                .and_then(|controls| controls.deadline)
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            UnknownOrigin::SolveDeadline
        } else if (self.memory_exceeded)() {
            UnknownOrigin::MemoryBudget
        } else {
            return Ok(());
        };
        Err(self.refuse(origin))
    }

    pub(in crate::executor) fn should_stop(&self) -> bool {
        self.check().is_err()
    }

    pub(in crate::executor) fn refuse_build_error(&self, error: FpBuildError) -> UnknownOrigin {
        if let Some(origin) = self.refusal.get() {
            return origin;
        }
        match error {
            FpBuildError::VariableLimit => self.refuse(UnknownOrigin::DeterministicResourceBudget),
            FpBuildError::Interrupted => match self.check() {
                Err(origin) => origin,
                Ok(()) => self.refuse(UnknownOrigin::InterruptFlag),
            },
        }
    }

    /// Retain an observed SAT/resource refusal under the same attempt owner.
    pub(in crate::executor) fn refuse(&self, origin: UnknownOrigin) -> UnknownOrigin {
        let first = self.refusal.get().unwrap_or(origin);
        self.refusal.set(Some(first));
        first
    }
}

#[cfg(test)]
#[path = "stop/tests.rs"]
mod tests;
