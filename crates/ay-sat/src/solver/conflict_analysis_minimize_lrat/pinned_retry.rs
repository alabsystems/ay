// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The pinned-slot retry of the level-0 unit materializers in a solver that
//! writes no proof (#pinned-retry-no-proof).
//!
//! `materialize_level0_unit_proofs_impl` and
//! `materialize_level0_minimize_unit_proofs` keep every root-trail slot whose
//! unit they could not materialize in a pinned list, and retry the whole list
//! on every call: at each `reduce_db` deletion (twice), at each conflict, and
//! at each level-0 garbage collection.
//!
//! In clause-trace mode (LRAT ids on, no proof manager) a materialization can
//! never succeed. `proof_emit_add_prechecked` returns the proof manager's id,
//! or 0 when there is none, so every derived unit and every trusted-transform
//! fallback comes back as 0 and the slot is pinned again. Nothing else
//! retires such a slot, so the pinned list grows to every root-trail slot
//! whose reason is not a unit clause, and every call walks all of them.
//! Measured on model-checker-consumer's `fac28` (base 086779f02): the step-(3) BV lane's
//! trace-mode search held about 1465 pinned slots, and the retries came to
//! about 4.1e8 slot visits. That was 16-18 s of the run's 56-60 s of CPU in
//! two instrumented runs, all in retries that changed nothing.
//!
//! # Why the short retry changes nothing but counters
//!
//! In such a solver a retried slot can do only three things:
//! * leave the list: its variable is no longer an unproved level-0
//!   assignment, or it has no reason;
//! * take its reason's id: the reason is a unit clause holding the unit with
//!   a visible id, the one branch that records without emitting;
//! * stay pinned. Every other branch ends that way with nothing recorded: an
//!   out-of-range reason, a reason without the unit, an invisible reason id,
//!   an incomplete chain (hidden or trusted-transform fallback), and a
//!   complete chain whose derived emission returns 0.
//!
//! [`Solver::retry_pinned_level0_unit_without_proof`] makes the full retry's
//! checks in the full retry's order and stops as soon as the outcome is
//! decided. For a reason of two or more literals every remaining branch keeps
//! the slot, so the chain walk is never needed. The pinned list, the cursor,
//! every recorded proof id and the return value are therefore exactly the
//! full retry's. So is the #A2b waste charge, which reads only the list.
//!
//! The differences are diagnostic only:
//! * `lrat_materialize[_minimize]_incomplete_chains` and the
//!   `sat.proof_adds_*` / `sat.proof_red_*` profile no longer count the
//!   repeated failed attempts;
//! * the AB triage hook sees the unit only at its first (fresh) visit;
//! * the interruptible materializer polls its stop every 64 slots, as it
//!   already does on the fresh walk, rather than at the head of every chain
//!   walk.
//!
//! A forward checker records every attempted addition, and a proof manager
//! makes a retry able to succeed. Either one keeps the full retry. The test
//! is made on every call, so a solver that gains a proof output later retries
//! in full from then on.

use super::super::*;

#[cfg(test)]
thread_local! {
    /// Test-only: force the full retry, for the differential pins.
    static FORCE_FULL_RETRY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Test-only: run `f` with the full pinned-slot retry forced on this thread.
#[cfg(test)]
pub(in crate::solver) fn with_full_pinned_retry<R>(f: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            FORCE_FULL_RETRY.with(|force| force.set(self.0));
        }
    }
    let _restore = Restore(FORCE_FULL_RETRY.with(|force| force.replace(true)));
    f()
}

impl Solver {
    /// Whether every proof addition this solver makes returns 0 and reaches
    /// no checker: no proof manager writes it and no forward checker records
    /// it (module documentation).
    #[inline]
    pub(super) fn level0_retry_writes_no_proof(&self) -> bool {
        #[cfg(test)]
        if FORCE_FULL_RETRY.with(std::cell::Cell::get) {
            return false;
        }
        self.proof_manager.is_none() && self.cold.forward_checker.is_none()
    }

    /// Retry pinned root-trail slot `i` in a solver that writes no proof
    /// ([`Self::level0_retry_writes_no_proof`]), with exactly the effect of
    /// the full retry. Returns whether the slot stays pinned.
    pub(super) fn retry_pinned_level0_unit_without_proof(&mut self, i: usize) -> bool {
        let unit_lit = self.trail[i];
        let var_idx = unit_lit.variable().index();
        if var_idx >= self.num_vars
            || self.var_data[var_idx].level != 0
            || self.level0_var_proof_id(var_idx).is_some()
        {
            return false;
        }
        let Some(reason_ref) = self.var_reason(var_idx) else {
            return false;
        };
        let clause_idx = reason_ref.0 as usize;
        if clause_idx >= self.arena.len() {
            return true;
        }
        let clause_len = self.arena.len_of(clause_idx);
        // A reason of two or more literals: every remaining branch of the
        // full retry keeps the slot (the derived emission returns 0).
        if clause_len > 1 {
            return true;
        }
        if !(0..clause_len).any(|j| self.arena.literal(clause_idx, j) == unit_lit) {
            return true;
        }
        let reason_id = self.clause_id(reason_ref);
        if reason_id == 0 || !self.lrat_hint_id_visible(reason_id) {
            return true;
        }
        self.record_level0_proof_id_for_lit(unit_lit, reason_id);
        self.record_unit_proof_id_for_lit(unit_lit, reason_id);
        false
    }
}

#[cfg(test)]
#[path = "pinned_retry_tests.rs"]
mod tests;
