// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counted work for the decisions `--sat-deterministic-inproc` takes off the
//! clock (2026-09-14).
//!
//! The per-round inprocessing overhead of #8099 is a round's cost minus the
//! cost of its timed passes. On the wall-clock default it is measured in
//! nanoseconds, which moves with host load: a busy machine pushes a round
//! across the 1, 3 and 8 ms buckets of `adaptive_tick_scale` and the 10 and
//! 100 ms arena-compaction bias, and the search takes another path. Under the
//! flag the same definition is measured in tick equivalents (te):
//! - the BCP work every counter already sees: search, probe and vivify ticks;
//! - the maintenance scans no counter sees, priced here by closed forms in
//!   AY's BCP cost unit: one te per random dereference, or per 256 streamed
//!   bytes (64 arena words, 32 watchers, 16 variable records).
//!
//! Scans made inside timed passes or during preprocessing cancel out, because
//! a round only reads deltas. Nothing here is read or written with the flag
//! off.

use super::*;

impl Solver {
    /// Cumulative counted work (tick equivalents) of everything that can run
    /// inside an inprocessing round.
    #[inline]
    pub(in crate::solver) fn inproc_work_te(&self) -> u64 {
        self.total_search_ticks()
            .saturating_add(self.cold.probe_ticks)
            .saturating_add(self.cold.vivify_ticks)
            .saturating_add(self.cold.inproc_scan_te)
    }

    /// Charge `te` of maintenance-scan work to the round, under the flag only.
    #[inline]
    pub(in crate::solver) fn charge_inproc_scan(&mut self, te: u64) {
        if self.deterministic_inproc() {
            self.cold.inproc_scan_te = self.cold.inproc_scan_te.saturating_add(te);
        }
    }

    /// One streamed pass over the clause arena: 64 u32 words per te.
    #[inline]
    pub(in crate::solver) fn arena_scan_te(&self) -> u64 {
        (self.arena.len() as u64).div_ceil(64)
    }

    /// One streamed pass over every literal's watch list: 16 list headers per
    /// te plus 32 watchers per te, two watchers per active clause.
    #[inline]
    pub(in crate::solver) fn watch_scan_te(&self) -> u64 {
        (2 * self.num_vars as u64).div_ceil(16)
            + (2 * self.arena.active_clause_count() as u64).div_ceil(32)
    }

    /// `reconnect_bve_watches`: on the fast path only the dirty bits are
    /// cleared, one byte per literal; otherwise the Phase 1 purge dereferences
    /// every watch entry (two per active clause) from every list, and the
    /// clauses added since `arena_baseline` are attached.
    pub(in crate::solver) fn charge_reconnect_scan(&mut self, arena_baseline: usize, fast: bool) {
        let te = if fast {
            (2 * self.num_vars as u64).div_ceil(256)
        } else {
            2 * self.num_vars as u64
                + 2 * self.arena.active_clause_count() as u64
                + (self.arena.len().saturating_sub(arena_baseline) as u64).div_ceil(4)
        };
        self.charge_inproc_scan(te);
    }

    /// `clear_stale_reasons`: a full scan of the variable records, or one
    /// check per dirty entry.
    pub(in crate::solver) fn charge_stale_reason_scan(&mut self) {
        let te = if self.stale_reasons.is_empty() {
            (self.num_vars as u64).div_ceil(16)
        } else {
            self.stale_reasons.len() as u64
        };
        self.charge_inproc_scan(te);
    }

    /// `rebuild_watches`: one streamed pass over the arena and two watch
    /// attachments per active clause.
    pub(in crate::solver) fn charge_rebuild_scan(&mut self) {
        let te = self.arena_scan_te() + 2 * self.arena.active_clause_count() as u64;
        self.charge_inproc_scan(te);
    }

    /// The counted work before a timed pass, under the flag; 0 otherwise.
    #[inline]
    pub(in crate::solver) fn pass_work_baseline(&self) -> u64 {
        if self.deterministic_inproc() {
            self.inproc_work_te()
        } else {
            0
        }
    }

    /// Add a timed pass's counted work to the pass counter, under the flag
    /// only. The intree probe has no pass timer, so wall mode counts it as
    /// overhead; it is not wrapped here either.
    #[inline]
    pub(in crate::solver) fn record_pass_work(&mut self, work_before: u64) {
        if self.deterministic_inproc() {
            let work = self.inproc_work_te().saturating_sub(work_before);
            self.cold.inproc_pass_work_te = self.cold.inproc_pass_work_te.saturating_add(work);
        }
    }

    /// Whether search has reached the indep_enum head start's counted stop
    /// (`cold.search_tick_stop`, under the flag). Never set otherwise; part
    /// of `resource_budget_exhausted`.
    #[inline]
    pub(crate) fn search_tick_stop_reached(&self) -> bool {
        self.cold
            .search_tick_stop
            .is_some_and(|target| self.total_search_ticks() >= target)
    }

    /// Install (or clear, with `None`) a caller's search-tick stop (GT-G6,
    /// the development design notes DR-36): the solve loops stop with
    /// [`SatUnknownReason::ResourceBudget`] once
    /// [`Self::total_search_ticks`] reaches `target`, at the same checkpoints
    /// as the conflict budget (every conflict, and the extension loop's
    /// amortized top).
    ///
    /// `target` is compared with the search ticks counted since the last reset
    /// of the search state. The solve entries reset it;
    /// `continue_solving_with_extension` and `resume_solving_with_extension`
    /// keep counting, so a continued search shares the stop with the solve it
    /// continues. A caller that wants a budget relative to the work already
    /// done passes `Some(self.total_search_ticks() + allowance)`. Like the
    /// conflict and decision budgets, the stop is a function of the search
    /// trajectory, never of a clock: it falls at the first checkpoint at or
    /// past the target, so with [`Self::set_deterministic_inproc`] on, the
    /// same formula and seed stop at the same tick count on every host.
    ///
    /// The stop is kept in its own field, never in the one the independent-
    /// support enumeration's counted head start sets and clears, so a parked
    /// enumeration neither drops it nor runs once it is reached.
    ///
    /// [`SatUnknownReason::ResourceBudget`]: crate::SatUnknownReason::ResourceBudget
    pub fn set_search_tick_stop(&mut self, target: Option<u64>) {
        self.cold.caller_search_tick_stop = target;
    }

    /// The caller's search-tick stop, as [`Self::set_search_tick_stop`] left
    /// it: a caller that arms a solve reads it to put it back afterwards.
    #[must_use]
    pub fn caller_search_tick_stop(&self) -> Option<u64> {
        self.cold.caller_search_tick_stop
    }

    /// Whether search has reached the caller's search-tick stop
    /// ([`Self::set_search_tick_stop`]); part of `resource_budget_exhausted`.
    #[inline]
    pub(crate) fn caller_search_tick_stop_reached(&self) -> bool {
        self.cold
            .caller_search_tick_stop
            .is_some_and(|target| self.total_search_ticks() >= target)
    }

    /// Install (or clear) the whole-solve budget in milliseconds that the
    /// deadline was computed from. It changes nothing on the wall clock;
    /// under `--sat-deterministic-inproc` it sizes the parked support
    /// enumeration's head start and slice (`solver/indep_enum.rs`), a fixed
    /// input where the wall schedule reads the remaining time.
    pub fn set_solve_budget_ms(&mut self, budget_ms: Option<u64>) {
        self.cold.solve_budget_ms = budget_ms;
    }

    /// This solver's `--sat-deterministic-inproc`: with it on, every inner
    /// schedule of its solves is counted work instead of wall time (the pre-
    /// and inprocessing rounds and passes, the lucky, GF(p) and
    /// independent-support probes, the round overhead; see
    /// `crate::determinism`), so the same formula, seed and budgets take the
    /// same search however loaded the host is. Only the solve deadline and
    /// the interrupt still read a clock or a flag, and they only stop.
    ///
    /// A solver starts from the process-wide switch
    /// ([`crate::deterministic_inproc_enabled`]). A caller that needs one
    /// solve decided by its counts whatever the process runs (an SMT
    /// `:rlimit` on an embedded solver) turns it on here before solving.
    pub fn set_deterministic_inproc(&mut self, on: bool) {
        self.cold.deterministic_inproc = on;
    }

    /// Whether this solver's inner schedules are counted work
    /// ([`Self::set_deterministic_inproc`]).
    #[inline]
    #[must_use]
    pub fn deterministic_inproc(&self) -> bool {
        self.cold.deterministic_inproc
    }

    /// Whether the PREPROCESSING wall clocks are consulted: the preprocess
    /// deadline (`PreprocessPolicy::budget_secs_for_counts` plus every BVE
    /// extension of it), the fastelim / deep per-call BVE wall, the pass-1
    /// cumulative BVE wall, the 2 s gate-BVE guard, the inprocessing-BVE round
    /// wall and the instantiate wall.
    ///
    /// OFF under [`Self::deterministic_inproc`] (proof-posture-parity, site
    /// B, 2026-09-10): each of those walls sits on top of a deterministic
    /// partner that stays in force — the resolution effort caps
    /// (`FASTELIM_EFFORT` and its scaled forms), the elimination caps, the
    /// round caps and the pass schedule — so both postures admit the same BVE
    /// work. On the wall-clock default the proof posture, slower per step
    /// because it writes the proof, reached the walls earlier and searched a
    /// different formula; `PROOF_WALL_BUDGET_SCALE` (x4 under a proof) is the
    /// wall-clock lane's approximation of the same intent and stays as it is
    /// there. The outer `-t` solve deadline is never affected.
    #[inline]
    pub(crate) fn preprocess_wall_budgets_enabled(&self) -> bool {
        !self.cold.deterministic_inproc
    }

    /// The overhead of the round that began at `round_start_work` with the
    /// pass counter at `pass_work_baseline`, in the milliseconds the readers
    /// bucket.
    #[inline]
    pub(in crate::solver) fn counted_round_overhead_ms(
        &self,
        round_start_work: u64,
        pass_work_baseline: u64,
    ) -> f64 {
        let round = self.inproc_work_te().saturating_sub(round_start_work);
        let passes = self
            .cold
            .inproc_pass_work_te
            .saturating_sub(pass_work_baseline);
        crate::determinism::overhead_ms_equiv(round.saturating_sub(passes))
    }
}
