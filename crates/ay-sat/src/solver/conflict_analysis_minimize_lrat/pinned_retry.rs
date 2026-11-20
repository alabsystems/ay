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
//! full retry's. The #A2b waste charge originally read only the list;
//! since DR-AY-SAT-PIN-MEMO-CHARGE-20261119 a memo-hit retry (below)
//! charges nothing, because it rescans nothing — measured on
//! cruise-control, ~275 permanent pins retried ~680 times each had
//! charged ~187k of the 250k budget for skipped work and poisoned the
//! clause trace before main search.
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
//!
//! # The stay-pinned memo
//!
//! Even the short retry is re-run for every pinned slot on every
//! materialize call, and materialize runs per clause mutation: measured
//! on cruise-control (QF_LIRA, default proof posture) at ~255k calls
//! re-walking 271 permanently pinned slots (69M slot visits in 12 s,
//! ~25% of the busy thread in the lookup accessors). A slot that stayed
//! pinned performed no writes, so its outcome is a pure function of the
//! inputs the short retry reads. Those inputs split in two kinds: the
//! variable's own proof-id state, which changes only through
//! `record_level0_proof_id_for_lit` / `record_unit_proof_id_for_lit`
//! (both clear the memo), and structural state the fingerprint below
//! reads directly (trail literal, level, assignment values, reason,
//! and the reason clause's length/id/head as consulted). Visibility is
//! not an input kind here: with no proof manager,
//! `lrat_hint_id_visible` is `id != 0`. If the fingerprint matches the
//! stored one, the retry would keep the slot again, so it is skipped.
//! A fingerprint collision can only keep a slot pinned until one of its
//! inputs changes — the same state as today — never record a wrong id:
//! the memo only ever answers "stays pinned".

use super::super::*;

#[cfg(test)]
thread_local! {
    /// Test-only: force the full retry, for the differential pins.
    static FORCE_FULL_RETRY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Test-only: disable the stay-pinned memo, for its differential pin.
    static PIN_MEMO_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Test-only: run `f` with the stay-pinned memo disabled on this thread.
#[cfg(test)]
pub(in crate::solver) fn with_pin_memo_disabled<R>(f: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            PIN_MEMO_DISABLED.with(|force| force.set(self.0));
        }
    }
    let _restore = Restore(PIN_MEMO_DISABLED.with(|force| force.replace(true)));
    f()
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

/// Outcome of one pinned-slot retry in a solver that writes no proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PinRetryOutcome {
    /// The slot stays pinned after a real rescan of its inputs.
    StaysPinned,
    /// The slot stays pinned and no rescan happened: the stay-pinned
    /// memo fingerprint matched, so the #A2b charge must skip the slot.
    StaysPinnedMemoized,
    /// The slot leaves the pinned list.
    LeavesPinned,
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

    /// Fingerprint of every structural input the short retry reads for
    /// the slot at trail position `i`, in a solver that writes no proof
    /// (so hint visibility is `id != 0` and needs no set probes). Zero
    /// means "do not memoize" (variable out of memo range).
    fn pin_retry_fingerprint(&self, i: usize) -> u64 {
        #[cfg(test)]
        if PIN_MEMO_DISABLED.with(std::cell::Cell::get) {
            return 0;
        }
        let unit_lit = self.trail[i];
        let var_idx = unit_lit.variable().index();
        if var_idx >= self.num_vars
            || var_idx >= self.cold.lrat_pin_retry_memo_fingerprint.len()
            || var_idx * 2 + 1 >= self.vals.len()
        {
            return 0;
        }
        let mut h: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut mix = |v: u64| {
            h ^= v.wrapping_add(0x9E37_79B9_7F4A_7C15);
            h = h.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            h ^= h >> 27;
        };
        mix(unit_lit.index() as u64);
        let vd = self.var_data[var_idx];
        mix(u64::from(vd.level));
        mix(u64::from(vd.reason));
        mix(u64::from(vd.flags));
        mix(self.vals[var_idx * 2] as i64 as u64);
        mix(self.vals[var_idx * 2 + 1] as i64 as u64);
        match self.var_reason(var_idx) {
            None => mix(0xA5A5_0001),
            Some(reason_ref) => {
                let clause_idx = reason_ref.0 as usize;
                if clause_idx >= self.arena.len() {
                    mix(0xA5A5_0002);
                } else {
                    let clause_len = self.arena.len_of(clause_idx);
                    mix(clause_len as u64);
                    if clause_len == 1 {
                        mix(self.arena.literal(clause_idx, 0).index() as u64);
                    }
                    mix(self.clause_id(reason_ref));
                }
            }
        }
        // Never zero: zero is the empty memo slot.
        h | 1
    }

    /// Retry pinned root-trail slot `i` in a solver that writes no proof
    /// ([`Self::level0_retry_writes_no_proof`]), with exactly the effect of
    /// the full retry. A `StaysPinnedMemoized` outcome performed no
    /// rescan: the fingerprint matched, so callers must not debit the
    /// #A2b bookkeeping budget for the slot.
    pub(super) fn retry_pinned_level0_unit_without_proof(&mut self, i: usize) -> PinRetryOutcome {
        let fingerprint = self.pin_retry_fingerprint(i);
        let var_idx = self.trail[i].variable().index();
        if fingerprint != 0
            && self
                .cold
                .lrat_pin_retry_memo_fingerprint
                .get(var_idx)
                .copied()
                == Some(fingerprint)
        {
            return PinRetryOutcome::StaysPinnedMemoized;
        }
        let stays = self.retry_pinned_level0_unit_without_proof_inner(i);
        if fingerprint != 0 {
            if let Some(memo) = self.cold.lrat_pin_retry_memo_fingerprint.get_mut(var_idx) {
                *memo = if stays { fingerprint } else { 0 };
            }
        }
        if stays {
            PinRetryOutcome::StaysPinned
        } else {
            PinRetryOutcome::LeavesPinned
        }
    }

    fn retry_pinned_level0_unit_without_proof_inner(&mut self, i: usize) -> bool {
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
