// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The counterexample replay's bounded search runs verdict-only; its
//! acceptance step does not.

use super::BmcSolver;
use crate::engine_result::ChcEngineResult;
use crate::pdr::{Counterexample, PdrConfig, PdrSolver};
use crate::smt::executor_adapter::ScopedVerdictOnlySearch;
use crate::{CancellationToken, ChcProblem};

#[cfg(test)]
thread_local! {
    /// Whether a verdict-only scope was live on this thread when the replay's
    /// acceptance step last ran (tests).
    static ACCEPTED_UNDER_VERDICT_ONLY: std::cell::Cell<Option<bool>> =
        const { std::cell::Cell::new(None) };
}

/// Whether a verdict-only scope was live on this thread when the replay's
/// acceptance step last ran; `None` when it has not run (tests).
#[cfg(test)]
pub(super) fn last_acceptance_under_verdict_only() -> Option<bool> {
    ACCEPTED_UNDER_VERDICT_ONLY.with(std::cell::Cell::get)
}

impl BmcSolver {
    /// [`Self::solve`] as the search step of
    /// `replay_confirm_unsafe_at_depth`. The executors it builds skip the
    /// proof cycle (see `smt::executor_adapter::verdict_only`).
    ///
    /// Nothing that search answers is a claim:
    ///
    /// * The replay maps Safe and Unknown to "not confirmed".
    /// * An Unsafe counts only once [`Self::confirm_replay_witness`] accepts
    ///   it, after this call returns and so outside the guard. That check
    ///   accepts only on ground evaluation of a derivation over the clauses.
    ///
    /// Each UNSAT therefore only rules out one branch of the search for a
    /// counterexample, and a certificate for it would be discarded unread.
    pub(super) fn solve_replay_search(&self) -> ChcEngineResult {
        let _verdict_only = ScopedVerdictOnlySearch::install();
        self.solve()
    }

    /// The replay's acceptance step: confirm `cex`, the bounded search's
    /// Unsafe, on `problem` (strict, no nested replay). The confirmed
    /// counterexample carries the ground derivation the verdict rests on.
    ///
    /// Called after [`Self::solve_replay_search`] has returned, so it runs in
    /// the default posture, never under the search's verdict-only scope.
    pub(super) fn confirm_replay_witness(
        problem: &ChcProblem,
        cex: Counterexample,
        verbose: bool,
        cancellation_token: Option<CancellationToken>,
    ) -> Option<Counterexample> {
        #[cfg(test)]
        ACCEPTED_UNDER_VERDICT_ONLY.with(|cell| {
            cell.set(Some(
                crate::smt::executor_adapter::verdict_only_search_active(),
            ));
        });
        let verify_config = PdrConfig {
            verbose,
            cancellation_token,
            solve_timeout: Some(std::time::Duration::from_secs(10)),
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            disable_cex_replay: true,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(problem.clone(), verify_config);
        match verifier.try_confirm_counterexample(cex) {
            Ok(Ok(confirmed)) => Some(confirmed),
            other => {
                tracing::debug!(
                    "cex-replay: witness replay on problem clauses did not verify ({other:?}); rejecting"
                );
                None
            }
        }
    }
}

#[cfg(test)]
mod tests;
