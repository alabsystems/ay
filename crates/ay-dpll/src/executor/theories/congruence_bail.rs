// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Why a BV congruence pass stopped early, and how the `unknown` it leaves is
//! published (P4a: a clock's firing is published as that stop, never as an
//! incomplete-search `unknown`).
//!
//! The EUF (BV-return) and non-BV congruence passes expand congruence into CNF
//! pair by pair, all-pairs over same-symbol applications. Either may stop
//! before the last pair. The clauses emitted are then a SUBSET of the full
//! axiomatization: an UNSAT stands, a SAT may violate an unemitted congruence
//! constraint and is degraded to `unknown`. What that `unknown` says depends
//! on what stopped the pass:
//!
//! * the pass's own count cap (clauses or literals emitted; the EUF pass's
//!   budget): a function of the query alone, the same on every host, so it is
//!   the deterministic `incomplete`;
//! * a stop seen by the pair loop's poll (every 1,024 pairs): the caller's
//!   interrupt, the deadline backstop or the process memory ceiling. Whether
//!   one fires depends on the host, so it is published as that stop
//!   (`interrupted`, `timeout`, `memout`). Before P4a it read `incomplete`,
//!   which a caller such as Trust records as a deterministic solver-incomplete
//!   stop, so a host-speed-dependent outcome masqueraded as a deterministic
//!   one.
//!
//! The non-BV pass has no count cap of its own: it ends after exactly the
//! query's own number of pairs, so the clock is only its backstop. A cap
//! derived from `:rlimit` would give `:rlimit` a second, non-SAT meaning
//! before GuardTree S6 (the development design notes), which makes it a
//! per-check tick budget that charges this work.

use std::sync::atomic::Ordering;

use crate::executor_types::{Result, SolveResult, UnknownOrigin};

use super::super::Executor;

/// Why a congruence pass stopped before it emitted every pair's axioms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CongruenceBail {
    /// The pass's own count cap: published as `incomplete`.
    Count,
    /// A stop the pair loop's poll observed: published as that stop.
    Stop(UnknownOrigin),
}

impl CongruenceBail {
    /// The cause of two bails taken together (two passes of one solve, or an
    /// incremental session's latched bail and this check-sat's). A count cap
    /// degrades a SAT on every host, so it outranks a stop; otherwise the
    /// first stop stands.
    pub(in crate::executor) fn merge(first: Option<Self>, second: Option<Self>) -> Option<Self> {
        match (first, second) {
            (Some(Self::Count), _) | (_, Some(Self::Count)) => Some(Self::Count),
            (Some(stop), _) => Some(stop),
            (None, second) => second,
        }
    }

    /// The registered origin the degraded `unknown` is published from.
    pub(in crate::executor) fn origin(self) -> UnknownOrigin {
        match self {
            Self::Count => UnknownOrigin::IncompleteSolverLane,
            Self::Stop(origin) => origin,
        }
    }
}

impl Executor {
    /// The stop an encoding-phase poll observes, if any (the congruence pair
    /// loops, the check after bit-blasting): the caller's interrupt, then the
    /// live solve deadline, then the process memory ceiling (the order
    /// `should_abort_theory_loop` reads them in). It takes `&self`, so a poll
    /// can read it while a `BvSolver` borrows the term store.
    pub(in crate::executor) fn encoding_phase_stop(&self) -> Option<UnknownOrigin> {
        if self
            .solve_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            return Some(UnknownOrigin::InterruptFlag);
        }
        if self.solve_deadline.expired() {
            return Some(UnknownOrigin::SolveDeadline);
        }
        ay_sys::process_memory_exceeded().then_some(UnknownOrigin::MemoryBudget)
    }

    /// Degrade a CDCL SAT found under a BAILED (partial) congruence
    /// axiomatization to `unknown` (item 4 Stage 2), published as what stopped
    /// the pass: `incomplete` for its count cap, the stop itself (`timeout`,
    /// `interrupted`, `memout`) for a stop.
    pub(in crate::executor) fn finalize_bv_congruence_bail(
        &mut self,
        bail: CongruenceBail,
    ) -> Result<SolveResult> {
        let origin = bail.origin();
        let reason = origin.reason();
        let detail = match bail {
            CongruenceBail::Count => {
                "a BV congruence pass reached its count cap; a SAT under the partial \
                 axiomatization is withheld (UNSAT stays valid)"
                    .to_string()
            }
            CongruenceBail::Stop(_) => format!(
                "a BV congruence pass was stopped ({reason}); a SAT under the partial \
                 axiomatization is withheld (UNSAT stays valid)"
            ),
        };
        tracing::warn!(
            reason = %reason,
            "BV congruence axiomatization bailed mid-loop; degrading CDCL SAT to Unknown \
             (partial congruence is sound for UNSAT only)"
        );
        self.last_statistics
            .set_string("unknown.reason", reason.to_string());
        self.last_statistics
            .set_string("unknown.phase", "non-bv-congruence-bail");
        self.last_statistics
            .set_string("unknown.cost_center", "bv-non-bv-congruence");
        self.last_statistics.set_string("unknown.detail", detail);
        self.last_model = None;
        self.record_unknown_from_origin(origin);
        self.last_result = Some(SolveResult::Unknown);
        Ok(SolveResult::Unknown)
    }
}

/// A forced bail of the non-BV congruence pass at pair 0, for tests
/// (`Executor::test_force_non_bv_congruence_bail`).
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TestCongruenceBail {
    /// As if a count cap cut the pass.
    CountCap,
    /// The pass's first poll runs inside a deadline share that has already
    /// passed; the share then ends and the outer deadline is put back, as the
    /// half-budget slicers do (the development design notes, GT6). The poll's own
    /// classification decides the bail, and nothing later can still see the
    /// stop, so only the bail itself can say what cut the pass.
    DeadlineShareExpires,
}

#[cfg(test)]
impl Executor {
    /// The bail the test hook forces, if any.
    pub(in crate::executor) fn test_non_bv_congruence_bail_now(&self) -> Option<CongruenceBail> {
        match self.test_force_non_bv_congruence_bail? {
            TestCongruenceBail::CountCap => Some(CongruenceBail::Count),
            TestCongruenceBail::DeadlineShareExpires => {
                let outer = self.solve_deadline.get();
                self.solve_deadline.set(Some(ay_core::time::Instant::now()));
                let stop = self.encoding_phase_stop();
                self.solve_deadline.set(outer);
                stop.map(CongruenceBail::Stop)
            }
        }
    }
}

#[cfg(test)]
#[path = "congruence_bail/tests.rs"]
mod tests;
