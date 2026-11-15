// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing maintenance: garbage drain, gate checks, and the search's
//! stop inside a round.

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
        // Counted work under `--sat-deterministic-inproc`: one streamed pass
        // over the arena, and a delete per pending clause.
        self.charge_inproc_scan(self.arena_scan_te() + 3 * u64::from(self.pending_garbage_count));
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

    /// One restart's inprocessing round, run under the search's stop.
    ///
    /// The passes poll the interrupt flags (`is_interrupted`), which a stop
    /// closure never raises, so the round polls `should_stop` too: on entry,
    /// at its checkpoints between passes, and before each probing candidate
    /// (`inprocessing_stop_requested`). A stop the round sees ends it at its
    /// next checkpoint. One seen while probing ends it before intree
    /// probing, congruence and decompose; any other keeps the next of the
    /// binary backbone, elimination, the bounded backbone, vivification and
    /// the subsumption after vivification from starting. Inside a
    /// pass, between intree probing, congruence and decompose (congruence's
    /// equivalences need the decompose after it), and between the last
    /// subsumption and the binary backbone that ends the round, only the
    /// interrupt flags are polled. `Some` ends the solve: Unknown when the
    /// round saw the stop fire (a stop wins over an UNSAT found after it, as
    /// in preprocessing cleanup), else the round's UNSAT.
    ///
    /// Measured 2026-10-08 in the test profile on the 1.64M-clause complete
    /// blast of a twenty-product 64-bit commuted sum, refuted by
    /// `prove_unsat_resolution_dag_until` under a 10 s stop: the first
    /// round's probing (two debug reverse watch validations of every watch
    /// list per candidate) ran past 240 s without one poll of the stop.
    pub(in crate::solver) fn run_inprocessing_round_until(
        &mut self,
        should_stop: &dyn Fn() -> bool,
        proof_progress: super::ProofProgress<'_>,
    ) -> Option<SatResult> {
        let found_unsat = self.run_restart_inprocessing_until(should_stop);
        if let Some(reason) = self.take_inprocessing_caller_stop() {
            return Some(self.declare_unknown_with_reason(reason));
        }
        found_unsat.then(|| self.declare_unsat_with_proof_progress(proof_progress))
    }

    /// The assumption solve's incremental inprocessing round
    /// (`run_incremental_inprocessing`), run under the solve's stop as
    /// `run_inprocessing_round_until` runs a restart's round: `Some` ends
    /// the solve, Unknown when the round saw the stop fire, else the round's
    /// UNSAT. Before, the round polled only the interrupt flags, so a stop
    /// that had fired before it, or fired during its subsumption, scoped BVE
    /// or transitive reduction, was first seen by the search loop's own
    /// polls after it (every 100 conflicts, 1,000 decisions or 1,024
    /// iterations), and an UNSAT the round found after the stop fired was
    /// answered. A stop that fires during vivification, the round's last
    /// pass, is still first seen by the search loop.
    pub(in crate::solver) fn run_incremental_inprocessing_round_until<F>(
        &mut self,
        should_stop: Option<&F>,
    ) -> Option<AssumeResult>
    where
        F: Fn() -> bool + ?Sized,
    {
        let stop = || should_stop.is_some_and(|stop| stop());
        let found_unsat = self.run_incremental_inprocessing(&stop);
        if let Some(reason) = self.take_inprocessing_caller_stop() {
            return Some(self.declare_assume_unknown_with_reason(reason));
        }
        found_unsat.then(|| self.declare_unsat_assume(vec![]))
    }

    /// Take the stop a round latched (`inprocessing_caller_stop`), as the
    /// Unknown reason that ends the solve: `DeadlineExceeded` once the solve
    /// deadline has passed, else `Interrupted`.
    pub(in crate::solver) fn take_inprocessing_caller_stop(&mut self) -> Option<SatUnknownReason> {
        if !std::mem::take(&mut self.cold.inprocessing_caller_stop) {
            return None;
        }
        Some(if self.solve_deadline_expired() {
            SatUnknownReason::DeadlineExceeded
        } else {
            SatUnknownReason::Interrupted
        })
    }

    /// Whether an inprocessing round must end now: an interrupt flag is
    /// raised, or `should_stop`, the search's stop, returns `true`. A fired
    /// stop is latched in `cold.inprocessing_caller_stop` for
    /// `run_inprocessing_round_until` (or, in the assumption solve's round,
    /// `run_incremental_inprocessing_round_until`), and not polled again.
    pub(in crate::solver) fn inprocessing_stop_requested(
        &mut self,
        should_stop: &dyn Fn() -> bool,
    ) -> bool {
        if self.is_interrupted() || self.cold.inprocessing_caller_stop {
            return true;
        }
        self.cold.inprocessing_caller_stop = should_stop();
        self.cold.inprocessing_caller_stop
    }
}
