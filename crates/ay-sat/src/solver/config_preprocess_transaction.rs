// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stop classification and deadline cleanup for initial preprocessing.

use super::config_preprocess_cleanup::PreprocessOutcome;
use super::*;

impl Solver {
    /// Publish a cooperative stop at a top-level SAT entry boundary.
    pub(super) fn finish_stopped_sat_entry<F>(&mut self, should_stop: &F) -> Option<SatResult>
    where
        F: Fn() -> bool + ?Sized,
    {
        let reason = self.solve_stop_reason(should_stop)?;
        let result = self.declare_unknown_with_reason(reason);
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        Some(result)
    }

    /// Publish a cooperative stop at an assumption API boundary.
    pub(super) fn finish_stopped_assumption_entry<F>(
        &mut self,
        should_stop: Option<&F>,
    ) -> Option<AssumeResult>
    where
        F: Fn() -> bool + ?Sized,
    {
        let reason = self.optional_solve_stop_reason(should_stop)?;
        let result = self.declare_assume_unknown_with_reason(reason);
        self.emit_diagnostic_assumption_result(&result);
        self.trace_result(SolveOutcome::Unknown);
        self.finish_tla_trace();
        self.reset_constraint();
        Some(result)
    }

    /// Classify a whole-solve cooperative stop in stable priority order.
    ///
    /// The shared interrupt covers both the external `Arc<AtomicBool>` and the
    /// process-memory trip wire. A real solve deadline is kept distinct from a
    /// callback stop so DPLL(T) can preserve timeout provenance.
    #[inline]
    pub(super) fn solve_stop_reason<F>(&self, should_stop: &F) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        if self.solve_deadline_expired() {
            Some(SatUnknownReason::DeadlineExceeded)
        } else if self.is_interrupted() || should_stop() {
            Some(SatUnknownReason::Interrupted)
        } else {
            None
        }
    }

    #[inline]
    pub(super) fn optional_solve_stop_reason<F>(
        &self,
        should_stop: Option<&F>,
    ) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        match should_stop {
            Some(stop) => self.solve_stop_reason(stop),
            None => self.solve_stop_reason(&|| false),
        }
    }

    /// Preserve deadline provenance on legacy hot paths that poll the atomic
    /// interrupt every iteration. The clock is read only after the cheap
    /// interrupt poll fires.
    #[inline]
    pub(super) fn active_interrupt_reason(&self) -> Option<SatUnknownReason> {
        if !self.is_interrupted() {
            None
        } else if self.solve_deadline_expired() {
            Some(SatUnknownReason::DeadlineExceeded)
        } else {
            Some(SatUnknownReason::Interrupted)
        }
    }

    /// Stop predicate used inside initial preprocessing.
    ///
    /// A local preprocessing deadline only truncates this optional phase and
    /// therefore remains a normal completion. The transaction wrapper
    /// distinguishes it from the whole-solve stop reasons above.
    #[inline]
    pub(super) fn preprocessing_should_stop<F>(&self, should_stop: &F) -> bool
    where
        F: Fn() -> bool + ?Sized,
    {
        self.solve_stop_reason(should_stop).is_some() || self.preprocess_timed_out()
    }

    /// Sample stops once after mandatory clause/watch cleanup. A previously
    /// latched callback remains sticky without calling a non-monotonic callback
    /// again, while a newly expired deadline can still refine its provenance.
    pub(super) fn stop_reason_after_preprocess_cleanup<F>(
        &self,
        outcome: PreprocessOutcome,
        should_stop: &F,
    ) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        match outcome {
            PreprocessOutcome::Stopped(latched) => {
                self.solve_stop_reason(&|| false).or(Some(latched))
            }
            PreprocessOutcome::Complete | PreprocessOutcome::Unsat => {
                self.solve_stop_reason(should_stop)
            }
        }
    }

    /// Run preprocessing as a deadline-clean transaction.
    ///
    /// The callback is latched because cooperative stop callbacks are not
    /// required to remain true. The local preprocessing budget is only a
    /// heuristic phase cap and maps to `Complete`; external interrupts and the
    /// whole-solve deadline remain typed stops for the solve caller.
    pub(super) fn preprocess_interruptible<F>(&mut self, should_stop: &F) -> PreprocessOutcome
    where
        F: Fn() -> bool + ?Sized,
    {
        let callback_stopped = std::cell::Cell::new(false);
        let latched_should_stop = || {
            if callback_stopped.get() {
                true
            } else if should_stop() {
                callback_stopped.set(true);
                true
            } else {
                false
            }
        };

        let unsat = self.preprocess_inner(&latched_should_stop);
        let outcome = self.classify_preprocess_outcome(unsat, &latched_should_stop);

        // Transaction boundary: no inner early return may leak a stale local
        // deadline into solver reuse or later inprocessing.
        self.cold.preprocess_deadline = None;
        outcome
    }

    pub(super) fn classify_preprocess_outcome<F>(
        &self,
        unsat: bool,
        should_stop: &F,
    ) -> PreprocessOutcome
    where
        F: Fn() -> bool + ?Sized,
    {
        if let Some(reason) = self.solve_stop_reason(should_stop) {
            PreprocessOutcome::Stopped(reason)
        } else if unsat {
            PreprocessOutcome::Unsat
        } else {
            // Deliberately excludes `preprocess_timed_out`: the local budget
            // only truncates this optional simplification phase.
            PreprocessOutcome::Complete
        }
    }
}
