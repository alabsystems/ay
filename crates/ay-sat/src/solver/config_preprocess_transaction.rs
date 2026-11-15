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
        let reason = self
            .counted_step_stop_reason()
            .or_else(|| self.solve_stop_reason(should_stop))?;
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
        let reason = self
            .counted_step_stop_reason()
            .or_else(|| self.optional_solve_stop_reason(should_stop))?;
        let result = self.declare_assume_unknown_with_reason(reason);
        self.emit_diagnostic_assumption_result(&result);
        self.trace_result(SolveOutcome::Unknown);
        self.finish_tla_trace();
        self.reset_constraint();
        Some(result)
    }

    /// True once the attached proof writer latched a write or flush failure
    /// (a full disk, a broken pipe). No certificate can be produced after
    /// that: an UNSAT is answered unknown with
    /// [`SatUnknownReason::ProofWriteFailure`] at finalization. The search goes
    /// on (owner, 2026-09-19): a SAT answer is certified by its model, not by
    /// the proof. The search after the latch is a degraded one — a proof
    /// manager that cannot write rejects the planned forward adds that carry
    /// hints, so some techniques add nothing — but it is sound, and it answers.
    /// Writer-only on purpose: an LRAT structural fail-close downgrades at
    /// finalize and must not stop search either.
    #[inline]
    pub(super) fn proof_output_failed(&self) -> bool {
        self.proof_writer().is_some_and(ProofOutput::has_io_error)
    }

    /// The proof write failure the writer latched, as a caller-facing detail
    /// (`proof write failed: <OS error>`), or `None` while the writer is
    /// healthy. A SAT answer given after it is a real answer without a proof.
    #[must_use]
    pub fn proof_write_failure(&self) -> Option<String> {
        self.proof_output_failed()
            .then(|| self.proof_write_failure_detail())
    }

    /// The unknown detail for [`SatUnknownReason::ProofWriteFailure`], naming
    /// the OS error the proof sink reported.
    pub(super) fn proof_write_failure_detail(&self) -> String {
        match self.proof_writer().and_then(ProofOutput::first_io_error) {
            Some(error) => format!("proof write failed: {error}"),
            None => "proof write failed (the writer reported no OS error)".to_string(),
        }
    }

    /// Classify a whole-solve cooperative stop in stable priority order.
    ///
    /// The shared interrupt covers both the external `Arc<AtomicBool>` and the
    /// process-memory trip wire. A real solve deadline is kept distinct from a
    /// callback stop so DPLL(T) can preserve timeout provenance.
    ///
    /// The search work made so far is reported first (`work_report.rs`), so a
    /// work ceiling that `should_stop` reads counts every conflict before it.
    #[inline]
    pub(super) fn solve_stop_reason<F>(&self, should_stop: &F) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        self.report_work_to_ledger();
        if let Some(reason) = self.counted_stop_reason() {
            Some(reason)
        } else if self.solve_deadline_expired() {
            Some(self.counted_latch_stop(SatUnknownReason::DeadlineExceeded))
        } else if self.is_interrupted() {
            Some(self.counted_latch_stop(SatUnknownReason::Interrupted))
        } else if let Some(reason) = self.counted_callback_stop(should_stop) {
            Some(reason)
        } else if self.original_ledger_replay_failed() {
            Some(SatUnknownReason::ProofFinalizationFailure)
        } else {
            self.counted_stop_reason()
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
        if let Some(reason) = self.counted_stop_reason() {
            Some(reason)
        } else if !self.is_interrupted() {
            None
        } else if self.solve_deadline_expired() {
            Some(self.counted_latch_stop(SatUnknownReason::DeadlineExceeded))
        } else {
            Some(self.counted_latch_stop(SatUnknownReason::Interrupted))
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
