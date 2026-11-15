// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause quality metrics, live database accounting, and reduction/memory triggers.

use super::*;

/// The least byte growth past what the last reduction left that re-arms the
/// byte trigger (`clause_db_byte_limit_exceeded`) before the learned count
/// reaches its floor, so a tiny limit does not reduce at every conflict.
pub(super) const CLAUSE_DB_BYTE_RETRIGGER_MIN_GROWTH: usize = 1 << 20;

/// Minimum learned-clause growth before the size cap may trigger another
/// reduction (`learned_cap_retrigger_floor`).
const LEARNED_CAP_RETRIGGER_MIN_GROWTH: usize = 256;

impl Solver {
    /// Recompute the glue (LBD) of a clause from the current assignment.
    ///
    /// Counts the number of distinct decision levels among the clause's
    /// assigned literals. Uses a stamp table for O(clause_size) performance
    /// with no clearing overhead (CaDiCaL analyze.cpp:206-219).
    pub(super) fn recompute_glue(&mut self, clause_idx: usize) -> u32 {
        self.recompute_glue_upto(clause_idx, u32::MAX)
    }

    /// `recompute_glue`, stopping once the count reaches `limit` (and then
    /// returning `limit`). `bump_clause` only asks whether the glue dropped
    /// below the stored one, so it passes that as the limit and skips the
    /// rest of a clause whose glue has not improved.
    pub(super) fn recompute_glue_upto(&mut self, clause_idx: usize, limit: u32) -> u32 {
        match self.recompute_glue_upto_admitted(
            clause_idx,
            limit,
            &conflict_analysis_minimize::admitted::Ordinary,
        ) {
            Ok(glue) => glue,
            Err(never) => match never {},
        }
    }

    pub(in crate::solver) fn recompute_glue_upto_admitted<
        P: conflict_analysis_minimize::admitted::Policy,
    >(
        &mut self,
        clause_idx: usize,
        limit: u32,
        p: &P,
    ) -> Result<u32, P::Error> {
        p.work(3)?;
        debug_assert!(
            self.arena.is_active(clause_idx),
            "BUG: recompute_glue called on inactive clause {clause_idx}"
        );

        if self.glue_stamp_counter == u32::MAX {
            p.work(self.glue_stamp.len())?;
            self.glue_stamp.fill(0);
            self.glue_stamp_counter = 0;
        }
        self.glue_stamp_counter += 1;
        let stamp = self.glue_stamp_counter;
        let mut count = 0u32;
        let clause_len = self.arena.len_of(clause_idx);
        for i in 0..clause_len {
            p.work(1)?;
            let lit = self.arena.literal(clause_idx, i);
            let var_idx = lit.variable().index();
            // CaDiCaL analyze.cpp:210: every literal must be assigned
            // during glue recomputation. An unassigned literal would
            // produce level[var] from a prior assignment, yielding a
            // wrong glue value.
            debug_assert!(
                self.var_is_assigned(var_idx),
                "BUG: recompute_glue: literal {lit:?} (var={var_idx}) in clause {clause_idx} is unassigned",
            );
            let lvl = self.var_data[var_idx].level as usize;
            // Grow stamp table if needed (can happen with added variables)
            if lvl >= self.glue_stamp.len() {
                p.glue_growth(self, lvl + 1)?;
                self.glue_stamp.resize(lvl + 1, 0);
            }
            if self.glue_stamp[lvl] != stamp {
                self.glue_stamp[lvl] = stamp;
                count += 1;
                if count >= limit {
                    return Ok(limit);
                }
            }
        }

        // LBD must be >= 1 for non-empty clauses (at least one decision level)
        // and <= clause_len (at most one distinct level per literal).
        debug_assert!(
            clause_len == 0 || (count >= 1 && count as usize <= clause_len),
            "BUG: recompute_glue returned {count} for clause {clause_idx} with {clause_len} literals"
        );

        Ok(count)
    }

    /// Estimated live heap usage attributable to the clause database.
    ///
    /// Sums every container that grows with clause or literal count:
    ///
    /// - `arena.memory_bytes()` — word buffer and shrink_map (the 32-bit
    ///   packed headers + literal words; dominates on large formulas).
    /// - `watches.heap_bytes()` — unified watcher buffers (`buf_blockers`,
    ///   `buf_clauses`, `meta`). Two watchers per non-binary learned clause,
    ///   so this scales linearly with the learned set.
    /// - `cold.clause_ids` — LRAT clause-id side vector indexed by arena
    ///   offset. Grows whenever the arena grows, only rebuilt by
    ///   compaction.
    /// - `cold.original_ledger.heap_bytes()` — immutable original-formula
    ///   literals + offsets (kept for DRAT/LRAT reconstruction).
    /// - `inproc.reconstruction.memory_bytes()` — BVE/BCE/sweep witness
    ///   stack. Grows unboundedly during inprocessing (#8672 Finding #3).
    ///
    /// This is the canonical figure for the byte-limit reduction trigger.
    /// Using only `arena.memory_bytes()` (the prior behavior) underreports
    /// actual clause-DB cost by 2x-5x in typical workloads, causing the
    /// memory-pressure path in `should_reduce_db` to fire late (#8672
    /// Finding #2).
    #[inline]
    pub(crate) fn clause_db_memory_bytes(&self) -> usize {
        use std::mem::size_of;
        // `clause_ids` defers its construction reservation to the first
        // write (`ColdState::clause_ids_grow_for`). While unallocated, bill
        // the deferred hint as a phantom charge: the historical trigger basis
        // included the eager `with_capacity(clauses_capacity)` reservation,
        // and dropping it would move WHEN reduction fires — the same
        // exposure `load_slack_reclaimed_bytes` below compensates for. Once
        // the first write lands, the real capacity equals the hint and takes
        // over seamlessly.
        let clause_ids_cap = match self.cold.clause_ids.capacity() {
            0 => self.cold.clause_ids_reserve_hint,
            cap => cap,
        };
        self.arena.memory_bytes()
            + self.watches.heap_bytes()
            + clause_ids_cap * size_of::<u64>()
            + self.cold.original_ledger.heap_bytes()
            // Load-time slack reclamation shrank the two REAL-capacity terms
            // above; add back what it handed off so this trigger stays on its
            // pre-shrink basis and the reduction cadence — hence the search —
            // does not move. See `ColdState::load_slack_reclaimed_bytes`.
            + self.cold.load_slack_reclaimed_bytes
            + self.inproc.reconstruction.memory_bytes()
    }

    /// Whether the configured learned-clause cap is exceeded by active
    /// redundant clauses.
    ///
    /// `arena.num_clauses()` is a historical allocation count until compaction
    /// and includes deleted slots. Using the active redundant counter keeps
    /// the reduction trigger tied to live learned-clause pressure.
    #[inline]
    pub(super) fn learned_clause_limit_exceeded(&self) -> bool {
        if let Some(limit) = self.cold.max_learned_clauses {
            let redundant = self.arena.redundant_count();
            // Not again until the count has grown past what the last
            // reduction left (see `learned_cap_retrigger_floor`).
            redundant > limit && redundant >= self.cold.learned_cap_retrigger_floor
        } else {
            false
        }
    }

    /// Whether the clause DB is over its byte limit
    /// (`set_max_clause_db_bytes`) with learned clauses a reduction can
    /// delete.
    ///
    /// The limit counts irredundant clauses too, which no reduction deletes,
    /// and the arena's accounted capacity, which only compaction gives back.
    /// So, like the learned-clause cap, the trigger waits until the learned
    /// count has grown past what the last reduction left
    /// (`learned_cap_retrigger_floor`). Without that floor a formula whose
    /// irredundant part alone is over the limit reduced at every conflict.
    /// The floor counts clauses, not bytes, so the trigger also fires once
    /// the bytes have grown a tenth of the limit (at least 1 MiB) past what
    /// the last reduction left (`clause_db_bytes_after_reduction`): long
    /// learned clauses cannot carry the DB far past its limit. Measured
    /// 2026-10-08 on Circuit_multiplier22 with a limit 1 MB over its initial
    /// size: the count floor alone peaked 23-40% over the old 6.78 MB.
    /// Measured 2026-10-08 in the test profile on the 1.64M-clause complete
    /// blast of a twenty-product 64-bit commuted sum: 378 MB against the
    /// resolution-DAG producer's 256 MB, 199 reductions in 199 conflicts at
    /// 20-60 ms each. The solve polls its stop every 100 conflicts, so those
    /// polls came 2.3-2.6 s apart, and a stop that had already fired was
    /// seen 1.6-2.2 s late.
    #[inline]
    pub(super) fn clause_db_byte_limit_exceeded(&self) -> bool {
        self.cold.max_clause_db_bytes.is_some_and(|limit| {
            let bytes = self.clause_db_memory_bytes();
            bytes > limit
                && (self.arena.redundant_count() >= self.cold.learned_cap_retrigger_floor
                    || bytes.saturating_sub(self.cold.clause_db_bytes_after_reduction)
                        > (limit / 10).max(CLAUSE_DB_BYTE_RETRIGGER_MIN_GROWTH))
        })
    }

    /// The learned count the cap and byte triggers wait for after a
    /// reduction that left the current learned clauses: those plus a tenth,
    /// at least `LEARNED_CAP_RETRIGGER_MIN_GROWTH` more.
    fn learned_retrigger_floor_for_remaining(&self) -> usize {
        let remaining = self.arena.redundant_count();
        remaining.saturating_add((remaining / 10).max(LEARNED_CAP_RETRIGGER_MIN_GROWTH))
    }

    /// Record what a reduction left for the cap and byte triggers: the
    /// learned-count floor (`learned_cap_retrigger_floor`) and, with a byte
    /// limit set, the clause DB's bytes (`clause_db_bytes_after_reduction`).
    pub(super) fn record_reduction_retrigger_points(&mut self) {
        self.cold.learned_cap_retrigger_floor = self.learned_retrigger_floor_for_remaining();
        if self.cold.max_clause_db_bytes.is_some() {
            self.cold.clause_db_bytes_after_reduction = self.clause_db_memory_bytes();
        }
    }

    /// Lower the cap and byte triggers' retrigger points to what is left,
    /// after learned clauses were deleted outside `reduce_db`
    /// (`clear_learned_clauses`, a popped scope's clauses, a between-solve
    /// reduction, the #8399 flush of `continue_solving_with_extension`, the
    /// incremental arena rebuild). Both points are what the last reduction
    /// left; deleting learned clauses afterwards leaves them above the DB, so
    /// the cap trigger waited for the learned count to regrow past a floor
    /// that can be any multiple of the cap. For example, a reduction that
    /// cannot get under a 10,000 cap and leaves 50,000 protected clauses sets
    /// the floor to 55,000; after `clear_learned_clauses` the cap was then
    /// not enforced again until the count was back at 55,000. Only ever
    /// lowers, so a trigger never fires later than it did.
    pub(super) fn lower_reduction_retrigger_points(&mut self) {
        let floor = self.learned_retrigger_floor_for_remaining();
        self.cold.learned_cap_retrigger_floor = self.cold.learned_cap_retrigger_floor.min(floor);
        self.lower_clause_db_bytes_after_reduction();
    }

    /// Lower the byte trigger's reference (`clause_db_bytes_after_reduction`)
    /// to the clause DB's bytes, which an arena compaction just shrank.
    /// `reduce_db` defers its compaction to the search's next quiescent
    /// point (`run_deferred_arena_compaction`), after it recorded the
    /// reference, so the reference kept the pre-compaction bytes, dead
    /// clauses included, and the DB could fill all the space the compaction
    /// gave back, plus the tenth of the limit, before the byte growth arm
    /// fired again. Only ever lowers: growth since the reduction stays
    /// counted.
    pub(super) fn lower_clause_db_bytes_after_reduction(&mut self) {
        if self.cold.max_clause_db_bytes.is_some() {
            let bytes = self.clause_db_memory_bytes();
            self.cold.clause_db_bytes_after_reduction =
                self.cold.clause_db_bytes_after_reduction.min(bytes);
        }
    }

    /// Check if we should reduce the clause database
    pub(super) fn should_reduce_db(&self) -> bool {
        // A queued theory conflict owns its ClauseRef until the solve loop
        // consumes it. Besides avoiding O(candidates × queued) ownership
        // scans, deferring reduction prevents any deletion/compaction pass
        // from invalidating a later conflict in the same callback batch.
        if !self.pending_theory_conflicts.is_empty() {
            return false;
        }
        // Suppressed during backbone probing (#7929): prevent clause deletion
        // from invalidating the DRAT proof chain for backbone units.
        if self.suppress_reduce_db {
            return false;
        }
        // Regular interval-based reduction
        if self.num_conflicts >= self.cold.next_reduce_db {
            return true;
        }
        // Aggressive reduction if clause limit exceeded (#1609)
        if self.learned_clause_limit_exceeded() {
            return true;
        }
        // Aggressive reduction if clause DB byte limit exceeded (#1609, #8672).
        //
        // Uses the composite `clause_db_memory_bytes` so the trigger reflects
        // arena + watchers + LRAT clause-ids + reconstruction stack +
        // original-ledger, not just the arena word buffer. The prior arena-only
        // check underreported actual clause-DB memory by 2x-5x and caused this
        // branch to fire late under real memory pressure.
        self.clause_db_byte_limit_exceeded()
    }

    /// Poll the process-wide memory limit on the shared conflict cadence.
    ///
    /// This reuses the solver's interrupt path so long-running SAT search can
    /// stop cleanly with `Unknown` once the shared ay-core memory gate trips (#6552).
    #[inline]
    pub(super) fn poll_process_memory_limit(&mut self) {
        if self.cold.process_memory_interrupt {
            return;
        }
        if !self
            .num_conflicts
            .is_multiple_of(PROCESS_MEMORY_CHECK_INTERVAL)
        {
            return;
        }
        self.confirm_or_arm_memory_interrupt();
    }

    /// Poll the process-wide memory limit NOW, ignoring the conflict cadence.
    ///
    /// The conflict-cadence poll above never fires in a zero-conflict regime —
    /// exactly the theory-propagation spin where an in-process solve can grow
    /// the host without bound (the large-workload / compiler_consumer 300 GB incident). The
    /// CDCL loop tops call this on their existing 1024-iteration amortized
    /// branch, so the cost is one `getrusage`/`task_info` pair per ~1024
    /// iterations regardless of conflict activity.
    #[inline]
    pub(super) fn poll_process_memory_limit_now(&mut self) {
        if self.cold.process_memory_interrupt {
            return;
        }
        self.confirm_or_arm_memory_interrupt();
    }

    /// Two-poll confirmation for the process memory gate (#sparse-gap
    /// Cluster A). A single positive reading only ARMS the pending flag; the
    /// interrupt latches when a SECOND consecutive poll confirms the gate is
    /// still exceeded. Rationale: the gate reads live allocator/footprint
    /// ledgers, and a transient spike (e.g. realloc-grow of a 63M-clause
    /// arena during parse, while peak RSS sat at 65% of the limit) previously
    /// latched `process_memory_interrupt` permanently — `is_interrupted()`
    /// consumes it at the very next loop top and the whole solve degraded to
    /// Unknown at exactly 1024 decisions (2 verified main-track instances
    /// flipped back to `s SATISFIABLE` once un-poisoned). Genuine OOM
    /// pressure persists across polls (~1024 loop iterations apart), so the
    /// fail-closed protection is preserved; a transient clears the pending
    /// flag on the confirming poll instead of poisoning the run.
    #[inline]
    fn confirm_or_arm_memory_interrupt(&mut self) {
        // Time-based confirmation window: iteration-cadence polls land
        // microseconds apart in a zero-conflict spin, so an
        // iterations-based double-check confirms the SAME transient. A
        // genuine runaway sustains pressure across a real time window
        // (the 263 GB incident grew over minutes); a parse/realloc
        // transient decays. 500ms inside the 95%-of-limit headroom.
        const MEMORY_CONFIRM_WINDOW_MS: u64 = 500;
        let exceeded = ay_core::term::TermStore::global_memory_exceeded();
        if !exceeded {
            self.cold.process_memory_interrupt_pending = false;
            self.cold.process_memory_armed_at = None;
            return;
        }
        match self.cold.process_memory_armed_at {
            Some(armed) if armed.elapsed().as_millis() as u64 >= MEMORY_CONFIRM_WINDOW_MS => {
                self.cold.process_memory_interrupt = true;
            }
            Some(_) => {} // still inside the window — keep waiting
            None => {
                self.cold.process_memory_interrupt_pending = true;
                self.cold.process_memory_armed_at = Some(ay_core::time::Instant::now());
            }
        }
    }
}
