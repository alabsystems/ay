// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing maintenance: garbage drain and gate checks.

use super::super::*;

impl Solver {
    /// Delete all clauses marked as pending garbage (#4761).
    ///
    /// During probing BCP, HBR subsumption marks the subsumed original clause
    /// as pending-garbage instead of deleting inline (which caused reason-clause
    /// panics, #4719). This method drains those marks at decision level 0 with
    /// refreshed reason marks, matching CaDiCaL's probe.cpp:267-271 pattern.
    ///
    /// Called before `collect_level0_garbage()` so the fixpoint guard there
    /// doesn't need modification.
    pub(in crate::solver) fn drain_all_pending_garbage(&mut self) {
        if self.pending_garbage_count == 0 {
            return;
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: drain_all_pending_garbage at decision level {}",
            self.decision_level,
        );
        self.ensure_reason_clause_marks_current();
        self.defer_stale_reason_cleanup = true;
        let active: Vec<usize> = self.arena.active_indices().collect();
        for clause_idx in active {
            if !self.arena.is_pending_garbage(clause_idx) {
                continue;
            }
            self.drain_pending_garbage_mark(clause_idx);
            self.delete_clause_checked(clause_idx, mutate::ReasonPolicy::ClearLevel0);
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        // Any marks not consumed (e.g., already-deleted clauses) are cleared.
        self.pending_garbage_count = 0;
    }

    /// Check whether inprocessing scheduling gates pass.
    ///
    /// Returns `true` when the conflict-count limit AND the reduction
    /// gate both allow an inprocessing round. Callers use this to detect
    /// when a forced backtrack to level 0 is needed before calling
    /// `run_restart_inprocessing()`, allowing proper theory callback
    /// notification in the DPLL(T) loop.
    ///
    /// CaDiCaL equivalent: the `if (level) backtrack()` guard at the
    /// entry of `inprobe()` / `elim()` (probe.cpp, elim.cpp).
    ///
    /// CaDiCaL probe.cpp:16-26: `inprobing()` checks `lim.inprobe <= stats.conflicts`.
    /// The limit grows logarithmically: `10 * inprobeint * log10(phase + 9)` (#7135, #8466).
    #[inline]
    pub(in crate::solver) fn inprocessing_gates_pass(&self) -> bool {
        // Gate: require at least some conflicts before first inprocessing.
        // CaDiCaL's init_search_limits sets lim.probe = stats.conflicts + probeint.
        // Use total_conflicts() so threshold progresses across incremental solves (#8208).
        //
        // #8465: Check total_conflicts first (cheap field read) before
        // is_interrupted() (atomic load). The CDCL loop top already checks
        // is_interrupted() every iteration, so skipping it here when
        // total_conflicts == 0 (the dominant case early in search) saves
        // one atomic load per iteration.
        let total_conflicts = self.total_conflicts();
        if total_conflicts == 0 {
            return false;
        }
        // CaDiCaL probe.cpp:25: lim.inprobe <= stats.conflicts
        if total_conflicts < self.cold.next_inprobe_conflict {
            return false;
        }
        if self.is_interrupted() {
            return false;
        }
        if self.cold.last_inprobe_reduction > 0
            && self.cold.num_reductions == self.cold.last_inprobe_reduction
        {
            return false;
        }
        true
    }
}
