// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's solver calls, each charged against [`SweepLimits`] with the
//! conflicts it actually spent (`ay_sat::solve_resolution_dag_counted_local`).
//!
//! Each is a local solve under the sweep's counted envelope, so its solver
//! builds no parked support enumeration, a SAT-only probe that waits for a
//! wall-clock head start a lemma solve never reaches
//! (`ay_sat::solve_resolution_dag_counted_local`).
//!
//! Charged its cap instead, a local lemma that needs three conflicts costs
//! its whole allowance — measured 2026-09-29 on the 64-bit
//! `127 * x == (x << 7) - x`: 200 lemma calls at 1,000 conflicts each
//! exhausted the checker's 200,000 before the closing refutation started.
//!
//! A call that ends on anything but its counts, a stop or its deadline (an
//! allocation ay-sat could not make, its process-memory interrupt) is passed
//! over like an undecided lemma, and is noted so that the strict producer
//! never remembers a refusal it may have shaped
//! (`crate::bv_blast_solver::note_uncounted_failure`).

use super::*;
use ay_sat::{ResolutionValidationError, SatUnknownReason};

impl Sweep<'_, '_> {
    /// One solver call over `clauses` under at most `conflicts` conflicts,
    /// and never more than the sweep has left.
    pub(super) fn solve(
        &mut self,
        vars: usize,
        clauses: &[Vec<Literal>],
        conflicts: u64,
    ) -> Option<ResolutionSolveOutcome> {
        let cap = conflicts.min(self.conflicts_left);
        if self.stopped || cap == 0 || self.out_of_work() || Instant::now() >= self.deadline {
            return None;
        }
        let limits = ResolutionProofLimits {
            deadline: Some(self.deadline),
            max_conflicts: Some(cap),
            max_decisions: Some(cap.saturating_mul(64)),
            max_proof_output_bytes: self.proof_output_bytes,
            ..ResolutionProofLimits::default()
        };
        let keep_going = &mut *self.keep_going;
        let (outcome, spent) =
            solve_resolution_dag_counted_local(vars, clauses, &limits, keep_going);
        // A solve stopped by its cap may report just past it; the envelope
        // is spent either way.
        self.conflicts_left = self.conflicts_left.saturating_sub(spent.max(1));
        self.stopped |= matches!(outcome, Err(ResolutionProofError::Cancelled));
        if !ended_as_counted(&outcome) {
            crate::bv_blast_solver::note_uncounted_failure();
        }
        outcome.ok()
    }
}

/// Whether a solver call ended as a counted sweep accounts for: decided, on
/// one of its counts, on a stop or at its deadline. Anything else, its
/// environment may have decided.
fn ended_as_counted(outcome: &Result<ResolutionSolveOutcome, ResolutionProofError>) -> bool {
    use ResolutionProofError as E;
    use ResolutionValidationError as V;
    match outcome {
        Ok(_)
        | Err(
            E::Satisfiable
            | E::LimitExceeded { .. }
            | E::Cancelled
            | E::DeadlineExceeded { .. }
            | E::Validation(V::LimitExceeded { .. } | V::DeadlineExceeded | V::Cancelled),
        ) => true,
        Err(E::SolverUnknown { reason }) => matches!(
            reason,
            Some(SatUnknownReason::DeadlineExceeded | SatUnknownReason::ResourceBudget)
        ),
        Err(_) => false,
    }
}

#[cfg(test)]
#[path = "solve_tests.rs"]
mod tests;
