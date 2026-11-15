// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain caller refusal across the optional consuming SAT trace and fallback.
//! Local trace quota/shape refusal is NOT an enclosing evaluation stop.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::resource::{CheckStop, CheckStopCaptureError, CheckStopScope, CheckStopWitness};
use ay_sat::{ClauseTrace, ConsumingTraceControl, ConsumingTraceError, ConsumingTraceStop};

use crate::executor::model::EvaluationAttempt;
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

pub(super) struct TraceCaller {
    state: Arc<State>,
    callback: CheckStop,
    capture: Option<ConsumingTraceControl>,
}

struct State {
    original: Result<Option<CheckStop>, CheckStopCaptureError>,
    interrupt: Option<Arc<AtomicBool>>,
    attempt: EvaluationAttempt,
    polling: AtomicBool,
}

impl TraceCaller {
    pub(super) fn capture(executor: &Executor) -> Self {
        let state = Arc::new(State {
            original: ay_core::resource::current_check_stop(),
            interrupt: executor.solve_interrupt.clone(),
            attempt: executor.evaluation_attempt(),
            polling: AtomicBool::new(false),
        });
        let retained = Arc::clone(&state);
        Self {
            state,
            callback: Arc::new(move || retained.stopped()),
            capture: None,
        }
    }

    pub(super) fn retain_capture(&mut self, capture: ConsumingTraceControl) {
        // The handle stays outside State: its original callback owns State,
        // so putting it in State would create an Arc ownership cycle.
        if self.capture.is_some() {
            self.state
                .attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            return;
        }
        self.capture = Some(capture);
    }

    /// Enter the callback as the thread's check stop. Without an original
    /// of its own its whole answer is three flags (`State::witness`), so it
    /// is entered with them: the strict walks it encloses poll it at every
    /// checker offer (911 M on qb44) and read those flags instead of calling
    /// it until one is raised.
    pub(super) fn enter(&self) -> CheckStopScope {
        let callback = Arc::clone(&self.callback);
        match self.state.witness() {
            Some(witness) => ay_core::resource::enter_witnessed_check_stop(callback, witness),
            None => ay_core::resource::enter_check_stop(callback),
        }
    }

    pub(super) fn stopped(&self) -> bool {
        if let Some(reason) = self
            .capture
            .as_ref()
            .and_then(ConsumingTraceControl::observed_stop)
        {
            self.record(reason);
            return true;
        }
        (self.callback)()
    }

    pub(super) fn record(&self, reason: ConsumingTraceStop) -> UnknownOrigin {
        let origin = match reason {
            ConsumingTraceStop::Observer => UnknownOrigin::IncompleteSolverLane,
            ConsumingTraceStop::Interrupt => UnknownOrigin::InterruptFlag,
            ConsumingTraceStop::Deadline => UnknownOrigin::SolveDeadline,
            ConsumingTraceStop::Work => UnknownOrigin::DeterministicResourceBudget,
            ConsumingTraceStop::Memory => UnknownOrigin::MemoryBudget,
        };
        self.state.attempt.record_stop(origin)
    }

    pub(super) fn handoff(
        &self,
        trace: Result<ClauseTrace, ConsumingTraceError>,
    ) -> Result<Option<ClauseTrace>, UnknownOrigin> {
        let result = match trace {
            Ok(trace) => Some(trace),
            Err(ConsumingTraceError::Unavailable) => None,
            Err(ConsumingTraceError::Stopped(reason)) => return Err(self.record(reason)),
        };
        if self.stopped() {
            return Err(self
                .state
                .attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane));
        }
        #[cfg(test)]
        if let Some(trace) = &result {
            observation::note_successful_handoff(&self.state.attempt);
            observation::inspect_successful_handoff(&self.state.attempt, trace);
        }
        // The old producer may independently reconstruct from ALL authored
        // roots when this capture is unavailable. No quota is renewed here.
        Ok(result)
    }
}

impl Drop for TraceCaller {
    fn drop(&mut self) {
        if let Some(reason) = self
            .capture
            .as_ref()
            .and_then(ConsumingTraceControl::observed_stop)
        {
            self.record(reason);
        }
        // A panic from an opaque callback elsewhere inside the SAT handoff
        // must not disappear if the caller catches it and tries another lane.
        if std::thread::panicking() {
            self.state
                .attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
    }
}

impl State {
    /// With no original, `stopped` reads only `outer_stop`'s three sources
    /// and answers `false`, recording nothing, while all are down: the
    /// attempt's stop flag (raised by every `record_stop`), the process
    /// cancel and the interrupt.
    fn witness(&self) -> Option<CheckStopWitness> {
        matches!(self.original, Ok(None)).then(|| {
            CheckStopWitness::new(
                std::iter::once(self.attempt.stop_flag()).chain(self.interrupt.clone()),
            )
        })
    }

    fn outer_stop(&self) -> Option<UnknownOrigin> {
        if let Some(reason) = self.attempt.stop_origin() {
            return Some(reason);
        }
        if ay_core::resource::process_cancelled()
            || self
                .interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Acquire))
        {
            return Some(UnknownOrigin::InterruptFlag);
        }
        // Do not turn an ambient search slice into an explicit caller stop.
        // SAT captures its Guard/deadline itself and returns typed failures;
        // subsequent proof assembly deliberately uses Certify/CancelOnly.
        None
    }

    fn stopped(&self) -> bool {
        if let Some(reason) = self.outer_stop() {
            self.attempt.record_stop(reason);
            return true;
        }
        if matches!(self.original, Ok(None)) {
            // No opaque callback: no code runs between this read and the
            // one after it, so there is no invocation to mark and the second
            // read answers as the first did.
            return false;
        }
        if self.polling.swap(true, Ordering::AcqRel) {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            return true;
        }
        let mut invocation = Invocation {
            state: self,
            completed: false,
        };
        let stopped = match &self.original {
            Err(_) => true,
            Ok(original) => original.as_ref().is_some_and(|stop| stop()),
        };
        if stopped {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
        if let Some(reason) = self.outer_stop() {
            self.attempt.record_stop(reason);
        }
        invocation.completed = true;
        self.polling.store(false, Ordering::Release);
        self.attempt.stop_origin().is_some()
    }
}

struct Invocation<'a> {
    state: &'a State,
    completed: bool,
}

impl Drop for Invocation<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.state
                .attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
    }
}

#[cfg(test)]
pub(super) mod observation;
#[cfg(test)]
mod tests;
