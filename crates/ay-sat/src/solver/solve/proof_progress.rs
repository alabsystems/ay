// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed proof control for the scope-free bounded ResolutionDag producer.

use super::super::*;
use super::ProofProgress;
use crate::solver::backward_proof::BackwardProofFailure;

impl Solver {
    /// Keep proof cancellation separate from the composite solve stop predicate.
    /// Neither callback is stored in the solver or in the owned proof writer.
    pub(crate) fn solve_interruptible_without_artifact_with_proof_progress<F>(
        &mut self,
        should_stop: F,
        proof_keep_going: &dyn Fn() -> bool,
    ) -> SolverSatResult
    where
        F: Fn() -> bool,
    {
        // This route is constructed by the fresh bounded ResolutionDag producer.
        // A scoped solve would need proof control through assumption finalization;
        // do not silently discard it in that separate, unsupported route.
        if !self.cold.scope_selectors.is_empty() || self.cold.backward_proof_limits.is_none() {
            self.cold.last_unknown_detail = None;
            return SolverSatResult::from_solver_result(
                self.declare_unknown_with_reason(SatUnknownReason::UnsupportedConfig),
            );
        }
        let result =
            self.solve_interruptible_raw_with_proof_progress(should_stop, Some(proof_keep_going));
        SolverSatResult::from_solver_result(self.finish_counted_sat(result))
    }

    pub(super) fn poll_unsat_proof_progress(&mut self, progress: ProofProgress<'_>) -> bool {
        let Some(keep_going) = progress else {
            return true;
        };
        if self.cold.backward_proof_failure.is_some() {
            return false;
        }
        let deadline = self
            .cold
            .backward_proof_limits
            .as_ref()
            .and_then(|limits| limits.deadline);
        let failure = if deadline.is_some_and(|end| ay_core::time::Instant::now() >= end) {
            Some(BackwardProofFailure::Deadline)
        } else {
            // A callback panic caught outside this method must not revive the
            // same proof attempt. The marker is cleared only after normal return.
            self.cold.backward_proof_failure = Some(BackwardProofFailure::Cancelled);
            if !self.counted_proof_progress(keep_going) {
                Some(BackwardProofFailure::Cancelled)
            } else if deadline.is_some_and(|end| ay_core::time::Instant::now() >= end) {
                Some(BackwardProofFailure::Deadline)
            } else {
                self.cold.backward_proof_failure = None;
                None
            }
        };
        if let Some(failure) = failure {
            self.cold.backward_proof_failure = Some(failure);
            self.cold.empty_clause_in_proof = false;
            self.cold.empty_clause_lrat_id = None;
            return false;
        }
        true
    }

    pub(super) fn bounded_proof_unknown_reason(&self) -> SatUnknownReason {
        if self.cold.backward_proof_failure == Some(BackwardProofFailure::Cancelled) {
            SatUnknownReason::Interrupted
        } else {
            SatUnknownReason::ProofFinalizationFailure
        }
    }

    pub(super) fn record_bounded_emission_failure(&mut self, error: &std::io::Error) {
        if crate::proof::is_bounded_emission_cancelled(error) {
            self.cold.backward_proof_failure = Some(BackwardProofFailure::Cancelled);
        } else if error.kind() == std::io::ErrorKind::TimedOut {
            self.cold.backward_proof_failure = Some(BackwardProofFailure::Deadline);
        }
    }
}

#[cfg(test)]
mod tests;
