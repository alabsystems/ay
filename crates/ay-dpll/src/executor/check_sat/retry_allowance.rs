// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! How much search work one retry of the `Unknown` cascade may spend, and what
//! stands when a retry spends it without an answer.
//!
//! [`Executor::cegar_refine_solve`] answers a pass that ended `Unknown` with
//! up to two more whole solves (the deep-QE retry and the trace-armed retry).
//! Each can only turn that `Unknown` into a verdict, but nothing bounded what
//! it cost, and for a query whose pre-pass eliminates nothing both are solves
//! of the SAME problem again. Measured on program-verifier queries (mixed
//! Int/Real, a few hundred triggered axioms, proof recorder shed): the first
//! pass ends `unknown` after a median 10 CPU s; the retries then need 1.4 to 8
//! times its split-loop rounds to reach the same `unknown`, so a caller with
//! a 60 s budget never saw the answer that was ready after 10.
//!
//! A re-solve of the same problem therefore runs under a work ceiling
//! (`ay_core::resource::enter_work_ceiling`) taken from the work of the pass
//! that ended `Unknown`. The measure is a count of search steps on the solving
//! thread, not time: the same query is cut at the same step on every machine
//! and under any load.
//!
//! The re-solves are worth keeping. Of 885 measured on such queries, 10
//! turned the `unknown` into `unsat`: a second solve starts from the terms
//! the first one left and instantiates further. Those ten needed 16 to 687
//! work units, nine of them less than the pass before (0.06 to 0.89 times its
//! work) and one 1.8 times. The allowance below keeps all ten with room.
//! (Measured while ay-sat reported a solve's conflicts at its restarts only.
//! The pass and its retries now both also count the conflicts each solve
//! makes after its last restart, or without one: `ay-sat`'s
//! `solver/work_report.rs`.)

use super::*;

/// A re-solve of the same problem may spend this many times the search work
/// of what ran before it in the same check (the first pass and its CEGAR
/// rounds). Above the floor, the re-solves that paid needed at most 0.08 of
/// that work.
const RETRY_WORK_FACTOR: u64 = 2;

/// A bounded retry is never held to fewer work units than this: the pass
/// before it can end `Unknown` almost for free (a lane that declines the
/// query's shape at once) and say nothing about what the retry needs. The
/// largest re-solve that paid took 687 units after a pass of 378.
const RETRY_WORK_FLOOR: u64 = 1024;

/// Statistics key: how many retries of the last check ran out of work, each
/// leaving the `Unknown` that stood before it. Statistics only; nothing reads
/// it back.
const RETRIES_OUT_OF_WORK: &str = "unknown_retry.out_of_work";

/// The search work one retry of the `Unknown` cascade may spend, in the units
/// of `ay_core::resource::thread_work_units`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) struct RetryAllowance(Option<u64>);

impl RetryAllowance {
    /// No ceiling of its own: for a retry that solves a DIFFERENT problem
    /// than the pass before it (whose work says nothing about its own), for
    /// one that only installs a refutation already built, and for a retry
    /// entered outside the cascade.
    pub(in crate::executor) const UNBOUNDED: Self = Self(None);

    /// The allowance of a re-solve that follows `units` of search work.
    pub(in crate::executor) fn after_work_of(units: u64) -> Self {
        Self(Some(
            units
                .saturating_mul(RETRY_WORK_FACTOR)
                .max(RETRY_WORK_FLOOR),
        ))
    }

    pub(in crate::executor) fn units(self) -> Option<u64> {
        self.0
    }
}

/// The `Unknown` a pass of the cascade left standing: everything a client can
/// still read after that answer. `invalidate_last_check_result` revokes the
/// rest at the publication boundary whichever pass ran last.
struct StandingUnknown {
    reason: Option<UnknownReason>,
    origin: Option<UnknownOrigin>,
    statistics: crate::executor_types::Statistics,
    candidates: crate::executor::model::unknown_candidate::RecordedCandidates,
}

impl StandingUnknown {
    fn capture(executor: &Executor) -> Self {
        Self {
            reason: executor.last_unknown_reason,
            origin: executor.last_unknown_origin,
            statistics: executor.last_statistics.clone(),
            candidates: executor.unknown_candidate.recorded(),
        }
    }

    fn restore(self, executor: &mut Executor) {
        executor.last_result = Some(SolveResult::Unknown);
        executor.last_unknown_reason = self.reason;
        executor.last_unknown_origin = self.origin;
        executor.last_statistics = self.statistics;
        executor.unknown_candidate.restore_recorded(self.candidates);
    }
}

impl Executor {
    /// Run one retry of the `Unknown` cascade within `allowance`.
    ///
    /// A retry that answers, or ends `Unknown` by itself, is returned as it
    /// is. One that is still searching when its allowance is spent is stopped
    /// through the deadline polls, which every lane already answers with a
    /// fail-closed `Unknown`; the `Unknown` that stood before the retry is
    /// then put back, with its reason, its statistics and its candidate
    /// models, so a client reads what it would have read had the retry not
    /// run. A verdict is never produced or changed here.
    ///
    /// What is put back is the published answer, not the whole working state.
    /// The passes that follow the cascade (the counterexample-free probe, the
    /// finite-model last chance) still see what a cut retry left behind: the
    /// probe a completed retry would have re-armed stays the first pass's,
    /// and the last-chance hook runs on the cut retry's working model under
    /// the restored reason. Each of them validates its own result, so a cut
    /// retry can change which of them answers, never what is trusted.
    pub(super) fn retry_within(
        &mut self,
        allowance: RetryAllowance,
        retry: impl FnOnce(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        let Some(units) = allowance.units() else {
            return retry(self);
        };
        let standing = StandingUnknown::capture(self);
        let ceiling = ay_core::resource::enter_work_ceiling(Some(units));
        let retried = retry(self);
        let out_of_work = ceiling.spent();
        drop(ceiling);
        match retried {
            Ok(SolveResult::Unknown) if out_of_work => {
                standing.restore(self);
                let cut = self
                    .last_statistics
                    .get_int(RETRIES_OUT_OF_WORK)
                    .unwrap_or(0);
                self.last_statistics.set_int(RETRIES_OUT_OF_WORK, cut + 1);
                Ok(SolveResult::Unknown)
            }
            other => other,
        }
    }
}

#[cfg(test)]
#[path = "retry_allowance_tests.rs"]
mod tests;
