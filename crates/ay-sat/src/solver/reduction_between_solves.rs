// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Between-solve learned clause reduction for incremental solving (#8435).
//!
//! IC3/PDR engines make thousands of short incremental SAT queries. Each
//! query learns a few clauses (typically 5-50) but finishes before the
//! 300-conflict `reduce_db` threshold fires. Over thousands of queries,
//! learned clauses accumulate unboundedly, degrading propagation speed
//! (more watch entries per literal), increasing memory pressure, and
//! slowing conflict analysis (more antecedents to resolve).
//!
//! This module provides `between_solve_reduce()` which runs during
//! `reset_search_state()` — between incremental solve calls — to manage
//! learned clauses accumulated across prior solves.
//!
//! In normal incremental mode it prunes low-quality learned clauses.
//! In IC3 mode it uses a conservative GC (#8672) that only prunes
//! high-LBD unused clauses when the learned count is very high,
//! preserving the vast majority of useful learned clauses while
//! preventing unbounded growth.
//!
//! ## Design
//!
//! The reduction uses a lightweight version of `reduce_db` that:
//! 1. Decays `used` flags so stale clauses lose their protection (#8435)
//! 2. Skips reason clause checks (trail is empty between solves)
//! 3. Sorts learned clauses by (LBD desc, size desc) — same as reduce_db
//! 4. In normal mode, deletes the bottom BETWEEN_SOLVE_REDUCE_FRACTION% of candidates
//! 5. In IC3 mode, conservatively prunes only high-LBD unused clauses (#8672)
//! 6. Flushes affected watch entries and shrinks watch lists when deletions occur
//!
//! Note: VSIDS activity rescaling was moved to `reset_search_state()`
//! (#8470) so it fires unconditionally between incremental solves,
//! regardless of whether the clause reduction threshold is met.
//!
//! ## Reference
//!
//! GipSAT (rIC3): Uses arena allocator with activity-based cleanup on
//! every solve call. CaDiCaL: No explicit between-solve cleanup, but its
//! incremental mode typically runs reduce_db within each long solve.
//! AY's approach is a middle ground: cleanup fires periodically based
//! on accumulated conflicts, not on every solve call (which would be
//! overhead for trivially short queries).

use super::*;

/// Sort clause indices by (LBD descending, size descending) — worst clauses first.
///
/// This is the standard CaDiCaL `reduce_less_useful` comparator (reduce.cpp:74-82)
/// used across all reduction paths: normal reduce_db, between-solve reduction,
/// IC3 conservative GC, and IC3 learned cap enforcement.
fn sort_clauses_by_lbd_desc(candidates: &mut [usize], arena: &ClauseArena) {
    candidates.sort_by(|&a, &b| {
        let a_glue = arena.lbd(a);
        let b_glue = arena.lbd(b);
        match b_glue.cmp(&a_glue) {
            std::cmp::Ordering::Equal => {
                let a_size = arena.len_of(a) as u32;
                let b_size = arena.len_of(b) as u32;
                b_size.cmp(&a_size)
            }
            other => other,
        }
    });
}

impl Solver {
    /// Manage accumulated learned clauses between incremental solve calls (#8435).
    ///
    /// Called by `reset_search_state()` when the solver is in incremental mode.
    /// Only fires when:
    /// - Enough lifetime conflicts have passed since the last cleanup
    /// - Learned clause count exceeds a threshold relative to the original formula
    ///
    /// The trail is empty between solves, so no reason clause protection is
    /// needed. This simplifies the reduction compared to in-solve `reduce_db`.
    ///
    /// In IC3 mode, delegates to `ic3_between_solve_gc()` (#8672) which uses
    /// a much more conservative reduction that only prunes high-LBD unused
    /// clauses when the learned count exceeds 10x the irredundant count.
    pub(super) fn between_solve_reduce(&mut self) {
        if self.cold.ic3_mode {
            // IC3 conservative GC (#8672): IC3/PDR depends on learned clauses
            // persisting across incremental queries (#8643), but without any
            // GC, learned clauses accumulate unboundedly over 10K+ queries.
            // Use a much more conservative GC that only prunes high-LBD,
            // unused learned clauses when the count is very high.
            self.ic3_between_solve_gc();
            return;
        }

        // Decay `used` flags on learned clauses periodically (#8435).
        // In IC3 workloads, reduce_db rarely fires, so clauses bumped during
        // conflict analysis retain used=MAX_USED indefinitely, permanently
        // protecting stale clauses from deletion. Periodic decay mimics the
        // used-flag decrement that reduce_db performs in long-running solves.
        if self.cold.incremental_solve_count > 0
            && self
                .cold
                .incremental_solve_count
                .is_multiple_of(BETWEEN_SOLVE_USED_DECAY_INTERVAL)
        {
            self.decay_used_flags_between_solves();
        }

        let total_conflicts = self
            .cold
            .lifetime_conflicts
            .saturating_add(self.num_conflicts);

        // Gate: minimum conflict interval between cleanups.
        if total_conflicts.saturating_sub(self.cold.last_between_solve_reduce_conflicts)
            < BETWEEN_SOLVE_REDUCE_CONFLICT_INTERVAL
        {
            return;
        }

        // Gate: only reduce when learned clauses have accumulated significantly.
        let active_count = self.arena.active_clause_count();
        let irredundant_count = self.arena.irredundant_count();
        let learned_count = active_count.saturating_sub(irredundant_count);
        let threshold = irredundant_count
            .saturating_mul(BETWEEN_SOLVE_LEARNED_FACTOR)
            .max(100);
        if learned_count < threshold {
            return;
        }

        // Collect all learned clause indices sorted by (LBD desc, size desc).
        // Between solves the trail is empty, so no reason clause protection
        // is needed. The normal path may delete these clauses; the IC3 path
        // ages them in place instead.
        if !self.trail.is_empty() {
            return;
        }
        debug_assert!(
            self.trail.is_empty(),
            "BUG: between_solve_reduce called with non-empty trail (len={})",
            self.trail.len(),
        );

        let mut candidates: Vec<usize> = self
            .arena
            .active_indices()
            .filter(|&idx| self.arena.is_learned(idx))
            .collect();

        if candidates.is_empty() {
            return;
        }

        sort_clauses_by_lbd_desc(&mut candidates, &self.arena);

        // Protect core clauses (LBD <= 2) — these are always valuable.
        // Delete BETWEEN_SOLVE_REDUCE_FRACTION% of the remaining candidates.
        let protectable = candidates
            .iter()
            .position(|&idx| self.arena.lbd(idx) <= CORE_LBD)
            .unwrap_or(candidates.len());
        let deletable = &candidates[..protectable];

        let num_to_delete = (deletable.len() * BETWEEN_SOLVE_REDUCE_FRACTION).saturating_div(100);

        if num_to_delete == 0 {
            return;
        }

        let deleted = self.delete_learned_clause_batch(deletable, num_to_delete);
        if deleted == 0 {
            return;
        }

        // Update bookkeeping (total_conflicts computed above, unchanged).
        self.cold.last_between_solve_reduce_conflicts = total_conflicts;
        self.stats.between_solve_reductions += 1;
        self.stats.between_solve_clauses_deleted += deleted;

        tracing::debug!(
            deleted,
            remaining = self.arena.active_clause_count(),
            irredundant = self.arena.irredundant_count(),
            solve_count = self.cold.incremental_solve_count,
            "between-solve reduction: pruned accumulated learned clauses (#8435)"
        );
    }

    /// Enforce a hard cap on learned clause count for IC3 mode (#8672).
    ///
    /// Called after each IC3 solve completes (from `solve_incremental_ic3`).
    /// Checks every IC3_LEARNED_CAP_CHECK_INTERVAL solves whether the
    /// learned clause count exceeds the cap:
    ///   cap = max(IC3_MAX_LEARNED_FACTOR * irredundant, IC3_MIN_LEARNED_CAP)
    ///
    /// When the cap is exceeded, runs a targeted reduction that:
    /// 1. Protects IC3 lemmas (IC3_LEMMA_BIT set) -- these are blocking
    ///    clauses critical for IC3 correctness
    /// 2. Protects core clauses (LBD <= CORE_LBD=2) -- high-quality learned
    ///    clauses that are almost always useful
    /// 3. Targets remaining learned clauses sorted by (LBD desc, size desc),
    ///    preferring unused clauses (used=0) over recently-used ones
    /// 4. Deletes enough clauses to bring count down to 75% of the cap
    ///
    /// This is a tighter bound than `ic3_between_solve_gc` (which uses 10x
    /// the irredundant count). The cap ensures a hard memory limit regardless
    /// of how many queries run.
    pub(super) fn ic3_enforce_learned_cap(&mut self) {
        // Only check periodically to amortize the scan cost.
        if !self
            .cold
            .incremental_solve_count
            .is_multiple_of(IC3_LEARNED_CAP_CHECK_INTERVAL)
        {
            return;
        }

        let irredundant_count = self.arena.irredundant_count();
        let active_count = self.arena.active_clause_count();
        let learned_count = active_count.saturating_sub(irredundant_count);

        let cap =
            (irredundant_count.saturating_mul(IC3_MAX_LEARNED_FACTOR)).max(IC3_MIN_LEARNED_CAP);

        if learned_count <= cap {
            return;
        }

        // Target: reduce to 75% of the cap to avoid re-triggering immediately.
        let target = cap * 3 / 4;
        let excess = learned_count.saturating_sub(target);

        // Invariant: between IC3 solves the solver is at decision level 0,
        // but the trail is generally NOT empty — the root-level trail persists
        // across incremental queries by design (reset_search_state_incremental
        // preserves it; solve_incremental_ic3 backtracks to level 0, not to an
        // empty trail, before invoking reduction). Level-0 literals may have
        // learned reason clauses; those are protected from deletion by the
        // reason-mark guard in delete_learned_clause_batch.
        self.debug_assert_root_level_trail_for_between_solve_reduction("ic3_enforce_learned_cap");

        // Collect eligible candidates: learned, not IC3 lemma, not core LBD.
        // Partition into unused (used=0) and used, so we delete unused first.
        let mut unused_candidates: Vec<usize> = Vec::new();
        let mut used_candidates: Vec<usize> = Vec::new();

        for idx in self.arena.active_indices() {
            if !self.arena.is_learned(idx) {
                continue;
            }
            // Protect IC3 lemmas unconditionally.
            if self.arena.is_ic3_lemma(idx) {
                continue;
            }
            // Protect core clauses (LBD <= 2).
            if self.arena.lbd(idx) <= CORE_LBD {
                continue;
            }
            if self.arena.used(idx) == 0 {
                unused_candidates.push(idx);
            } else {
                used_candidates.push(idx);
            }
        }

        // Sort both pools by (LBD descending, size descending) — worst first.
        sort_clauses_by_lbd_desc(&mut unused_candidates, &self.arena);
        sort_clauses_by_lbd_desc(&mut used_candidates, &self.arena);

        // Delete unused first, then used if needed.
        let from_unused = excess.min(unused_candidates.len());
        let deleted_unused = if from_unused > 0 {
            self.delete_learned_clause_batch(&unused_candidates, from_unused)
        } else {
            0
        };

        let remaining_excess = excess.saturating_sub(deleted_unused as usize);
        let from_used = remaining_excess.min(used_candidates.len());
        let deleted_used = if from_used > 0 {
            self.delete_learned_clause_batch(&used_candidates, from_used)
        } else {
            0
        };

        let total_deleted = deleted_unused + deleted_used;
        if total_deleted > 0 {
            self.stats.between_solve_reductions += 1;
            self.stats.between_solve_clauses_deleted += total_deleted;

            tracing::debug!(
                deleted = total_deleted,
                deleted_unused,
                deleted_used,
                cap,
                learned_before = learned_count,
                learned_after = active_count
                    .saturating_sub(irredundant_count)
                    .saturating_sub(total_deleted as usize),
                irredundant = irredundant_count,
                solve_count = self.cold.incremental_solve_count,
                "IC3 learned cap enforcement: reduced clause DB (#8672)"
            );
        }
    }

    /// Conservative GC for IC3 mode (#8672).
    ///
    /// IC3/PDR depends on learned clauses persisting across queries (#8643).
    /// However, over 10K+ short queries, each learning 5-50 clauses, the
    /// learned clause DB grows without bound, degrading propagation speed
    /// and increasing memory pressure.
    ///
    /// This conservative GC:
    /// 1. Only fires after IC3_GC_MIN_SOLVES (500) incremental solves
    /// 2. Only fires when learned count exceeds IC3_GC_LEARNED_FACTOR (10x)
    ///    times the irredundant count
    /// 3. Only targets high-LBD (>IC3_GC_MIN_LBD=6) learned clauses with
    ///    used=0 (not recently useful)
    /// 4. Deletes only IC3_GC_FRACTION (25%) of eligible candidates
    /// 5. Blocking clauses (added as irredundant via add_clause_global) are
    ///    never touched — they are not learned clauses
    ///
    /// Decay of `used` flags still fires periodically so stale clauses
    /// eventually become eligible for GC.
    fn ic3_between_solve_gc(&mut self) {
        // Decay used flags periodically, same as normal mode.
        if self.cold.incremental_solve_count > 0
            && self
                .cold
                .incremental_solve_count
                .is_multiple_of(BETWEEN_SOLVE_USED_DECAY_INTERVAL)
        {
            self.decay_used_flags_between_solves();
        }

        // Gate: don't GC during initial ramp-up.
        if self.cold.incremental_solve_count < IC3_GC_MIN_SOLVES {
            return;
        }

        // Gate: only GC when learned clauses have accumulated significantly.
        let irredundant_count = self.arena.irredundant_count();
        let active_count = self.arena.active_clause_count();
        let learned_count = active_count.saturating_sub(irredundant_count);
        let threshold = irredundant_count
            .saturating_mul(IC3_GC_LEARNED_FACTOR)
            .max(1000);
        if learned_count < threshold {
            return;
        }

        // #lra-inc-engine S4 (#8078-class dangling-reason fix): this GC can run
        // during the incremental reset with a PRESERVED non-empty level-0 trail
        // — the inc-engine keeps the level-0 trail across check-sats (and so does
        // CHC/PDR). The normal between_solve path bails when the trail is
        // non-empty (reduction_between_solves.rs:135); this ic3 path did not, and
        // previously only had a debug_assert (stripped in release) asserting an
        // empty trail. `delete_learned_clause_batch` -> `compact_arena_locality`
        // REMAPS surviving reason clauses but REQUIRES that reason clauses were
        // protected from deletion (arena_gc.rs:85; a deleted assigned-variable
        // reason panics in debug / clears the reason to NO_REASON in release,
        // producing an unsound resolvent -> false UNSAT). Refresh the reason marks
        // for the current trail and exclude currently-reason clauses from the
        // deletion candidates — matching in-solve reduce_db's locked-clause
        // discipline. With an empty trail this is a cheap no-op (no trail reasons
        // to mark), so CHC behavior on empty-trail resets is unchanged. This is
        // the guard that makes dropping the inc-engine Unsat re-verify sound.
        self.refresh_reason_clause_marks();

        // Collect only high-LBD, unused, NON-REASON learned clauses — the
        // conservative candidate set. Low-LBD, recently-used, and current reason
        // clauses (protecting the preserved trail's reason chain) are retained.
        let mut candidates: Vec<usize> = self
            .arena
            .active_indices()
            .filter(|&idx| {
                self.arena.is_learned(idx)
                    && !self.arena.is_ic3_lemma(idx)
                    && self.arena.lbd(idx) > IC3_GC_MIN_LBD
                    && self.arena.used(idx) == 0
                    && !self.is_reason_clause_marked(idx)
            })
            .collect();

        if candidates.is_empty() {
            return;
        }

        sort_clauses_by_lbd_desc(&mut candidates, &self.arena);

        let num_to_delete = (candidates.len() * IC3_GC_FRACTION).saturating_div(100);
        if num_to_delete == 0 {
            return;
        }

        let deleted = self.delete_learned_clause_batch(&candidates, num_to_delete);
        if deleted == 0 {
            return;
        }

        self.stats.between_solve_reductions += 1;
        self.stats.between_solve_clauses_deleted += deleted;

        tracing::debug!(
            deleted,
            learned_remaining = self
                .arena
                .active_clause_count()
                .saturating_sub(self.arena.irredundant_count()),
            irredundant = irredundant_count,
            solve_count = self.cold.incremental_solve_count,
            "IC3 between-solve GC: pruned high-LBD unused learned clauses (#8672)"
        );
    }

    /// Memory-proportional learned clause reduction for IC3 mode (#8673).
    ///
    /// Complements the count-based `ic3_enforce_learned_cap` with an arena
    /// memory-proportional check. The cap enforcer limits the *number* of
    /// learned clauses but doesn't account for clause *size* — many medium-
    /// length clauses (10-20 literals each) can stay under the count cap
    /// while consuming significant arena memory.
    ///
    /// This method fires when:
    /// 1. `ic3_baseline_arena_words > 0` (baseline has been captured)
    /// 2. `arena.len() > IC3_MEMORY_PRESSURE_ARENA_FACTOR * baseline`
    /// 3. `arena.len() > IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS`
    ///
    /// When triggered, it aggressively reduces learned clauses:
    /// - First pass: delete unused (used=0) non-core, non-IC3-lemma learned
    ///   clauses, sorted worst-first (high LBD, large size)
    /// - Second pass: if still above threshold, delete used clauses too
    /// - Target: reduce until arena word count would drop below the pressure
    ///   threshold (estimated from clause count reduction)
    ///
    /// After reduction, the baseline is updated to the post-reduction arena
    /// size to prevent re-triggering every check interval.
    pub(super) fn ic3_memory_pressure_reduce(&mut self) {
        // Only check periodically to amortize cost.
        if !self
            .cold
            .incremental_solve_count
            .is_multiple_of(IC3_MEMORY_PRESSURE_CHECK_INTERVAL)
        {
            return;
        }

        let arena_words = self.arena.len();

        // Capture baseline on first check if not yet set.
        if self.cold.ic3_baseline_arena_words == 0 {
            if arena_words > 0 {
                self.cold.ic3_baseline_arena_words = arena_words;
            }
            return;
        }

        // Gate: arena must be above minimum size.
        if arena_words < IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS {
            return;
        }

        let baseline = self.cold.ic3_baseline_arena_words;
        let threshold = baseline.saturating_mul(IC3_MEMORY_PRESSURE_ARENA_FACTOR);

        // Gate: arena must exceed the pressure threshold.
        if arena_words <= threshold {
            return;
        }

        // Invariant: root-level trail only — see ic3_enforce_learned_cap.
        // Reason clauses of level-0 literals are protected from deletion by
        // the reason-mark guard in delete_learned_clause_batch.
        self.debug_assert_root_level_trail_for_between_solve_reduction(
            "ic3_memory_pressure_reduce",
        );

        // Collect eligible candidates: learned, not IC3 lemma, not core LBD.
        // Partition into unused and used pools for priority-based deletion.
        let mut unused_candidates: Vec<usize> = Vec::new();
        let mut used_candidates: Vec<usize> = Vec::new();

        for idx in self.arena.active_indices() {
            if !self.arena.is_learned(idx) {
                continue;
            }
            if self.arena.is_ic3_lemma(idx) {
                continue;
            }
            if self.arena.lbd(idx) <= CORE_LBD {
                continue;
            }
            if self.arena.used(idx) == 0 {
                unused_candidates.push(idx);
            } else {
                used_candidates.push(idx);
            }
        }

        let total_eligible = unused_candidates.len() + used_candidates.len();
        if total_eligible == 0 {
            // All learned clauses are protected (IC3 lemmas or core).
            // Update baseline to prevent re-triggering.
            self.cold.ic3_baseline_arena_words = arena_words;
            return;
        }

        // Sort both pools worst-first.
        sort_clauses_by_lbd_desc(&mut unused_candidates, &self.arena);
        sort_clauses_by_lbd_desc(&mut used_candidates, &self.arena);

        // Delete IC3_MEMORY_PRESSURE_DELETE_FRACTION% of eligible candidates.
        // Delete unused first, then used if needed.
        let total_to_delete = (total_eligible * IC3_MEMORY_PRESSURE_DELETE_FRACTION)
            .saturating_div(100)
            .max(1);

        let from_unused = total_to_delete.min(unused_candidates.len());
        let deleted_unused = if from_unused > 0 {
            self.delete_learned_clause_batch(&unused_candidates, from_unused)
        } else {
            0
        };

        let remaining_to_delete = total_to_delete.saturating_sub(deleted_unused as usize);
        let from_used = remaining_to_delete.min(used_candidates.len());
        let deleted_used = if from_used > 0 {
            self.delete_learned_clause_batch(&used_candidates, from_used)
        } else {
            0
        };

        let total_deleted = deleted_unused + deleted_used;
        if total_deleted > 0 {
            self.stats.between_solve_reductions += 1;
            self.stats.between_solve_clauses_deleted += total_deleted;
            self.stats.ic3_memory_pressure_reduces += 1;

            // Update baseline to post-reduction arena size to prevent
            // re-triggering every check interval. The arena may still be
            // above the original baseline due to irredundant clause growth,
            // but that's expected — the important thing is that learned
            // clause memory was freed.
            self.cold.ic3_baseline_arena_words = self.arena.len();

            tracing::debug!(
                total_deleted,
                deleted_unused,
                deleted_used,
                arena_words_before = arena_words,
                arena_words_after = self.arena.len(),
                baseline,
                threshold,
                solve_count = self.cold.incremental_solve_count,
                "IC3 memory pressure reduce: arena exceeded {}x baseline (#8673)",
                IC3_MEMORY_PRESSURE_ARENA_FACTOR,
            );
        }
    }

    /// Debug-check the between-solve reduction invariant for the IC3 fast
    /// path: the solver must be at decision level 0 and every trail literal
    /// must be a root-level assignment. The trail need NOT be empty — IC3
    /// incremental solving preserves the level-0 trail across queries
    /// (that non-empty root-level trail previously tripped a wrong
    /// `trail.is_empty()` assertion here, panicking the model-checker-consumer → ay-chc
    /// IC3 lane mid-`solve_incremental_ic3`).
    fn debug_assert_root_level_trail_for_between_solve_reduction(&self, context: &str) {
        debug_assert_eq!(
            self.decision_level,
            0,
            "BUG: {context} called above decision level 0 (trail len={})",
            self.trail.len(),
        );
        #[cfg(debug_assertions)]
        for &lit in &self.trail {
            debug_assert_eq!(
                self.var_data[lit.variable().index()].level,
                0,
                "BUG: {context} called with non-root literal {lit:?} on trail",
            );
        }
    }

    /// Delete up to `max_delete` learned clauses from the sorted candidate list.
    ///
    /// Shared by both normal and IC3 between-solve reduction paths.
    /// Returns the number of clauses actually deleted.
    ///
    /// Reason-clause protection: on the non-IC3 path the trail is empty here
    /// (`reset_search_state` clears it before `between_solve_reduce`), but the
    /// IC3 fast path (`solve_incremental_ic3`) preserves the ROOT-LEVEL trail
    /// across queries (`reset_search_state_incremental` / `backtrack_ic3(0)`),
    /// and a learned clause can be the reason for a level-0 trail literal
    /// (`analyze_and_backtrack_ic3` enqueues the UIP with the freshly learned
    /// clause as reason after backtracking to level 0). Deleting such a clause
    /// leaves `var_data[v].reason` dangling; the next `compact_arena_locality`
    /// would then leave the assigned variable pointing at freed/aliased arena
    /// data (see arena_gc.rs step 5, which asserts exactly this invariant).
    /// Mirror in-solve `reduce_db`: rebuild reason marks (O(trail_len); no-op
    /// when the trail is empty) and never delete a marked clause.
    fn delete_learned_clause_batch(&mut self, candidates: &[usize], max_delete: usize) -> u64 {
        self.ensure_reason_clause_marks_current();
        let mut deleted = 0u64;
        for &idx in candidates.iter().take(max_delete) {
            if !self.arena.is_active(idx) {
                continue;
            }

            // Guard: only delete learned clauses.
            if !self.arena.is_learned(idx) {
                continue;
            }

            // Guard: never delete a clause that is the reason for a trail
            // literal (see doc comment above).
            if self.is_reason_clause_marked(idx) {
                continue;
            }

            // Between solves, watches may or may not be connected depending
            // on whether the arena was rebuilt. Mark watched literals dirty
            // for lazy flush. If watches are disconnected, this is a no-op.
            if !self.watches_disconnected {
                let clause_len = self.arena.len_of(idx);
                if clause_len > 2 {
                    let (w0, w1) = self.arena.watched_literals(idx);
                    if w0.index() < self.dirty_watches.len() {
                        self.dirty_watches[w0.index()] = true;
                    }
                    if w1.index() < self.dirty_watches.len() {
                        self.dirty_watches[w1.index()] = true;
                    }
                }
                self.delete_binary_clause_watches(idx);
            }

            // Occ list maintenance.
            if let Some(ref mut gc_occ) = self.gc_occ {
                let lits = self.arena.literals(idx);
                gc_occ.remove_clause(idx, lits);
            }

            // Delete from arena. Between solves, proof emission is not active,
            // so skip proof-related hooks.
            self.stats.clear_bcp_learned_1963_blocker_cert(idx);
            self.arena.delete(idx);
            self.cold.clause_db_changes += 1;
            deleted += 1;
        }

        if deleted > 0 {
            // Flush stale watch entries for deleted clauses.
            if !self.watches_disconnected {
                self.flush_watches();
                self.stats.watches_shrunk += self.watches.shrink_watch_lists();
            }

            // Arena compaction if dead space is significant.
            if self.should_compact_arena() {
                if self.vsids.vmtf_is_deferred() {
                    self.vsids.rebuild_vmtf_from_bump_order(&self.vals);
                }
                self.compact_arena_locality();
            }
        }

        deleted
    }

    /// Decay `used` flags on all learned clauses between incremental solves (#8435).
    ///
    /// CaDiCaL decrements `used` on every `reduce_db` pass (reduce.cpp:109-111).
    /// In IC3 workloads with many short queries, reduce_db fires infrequently,
    /// so clauses bumped during conflict analysis retain `used=MAX_USED`
    /// indefinitely. This protects them from deletion even when they haven't
    /// been useful for hundreds of queries.
    ///
    /// Between-solve decay mirrors CaDiCaL's in-solve decay: decrement `used`
    /// by 1 for all learned clauses. After MAX_USED (31) decay passes without
    /// being bumped, a clause loses all protection and becomes eligible for
    /// deletion. Core clauses (LBD<=2) are decayed but still protected from
    /// deletion by the core guard in `between_solve_reduce()`.
    ///
    /// Cost: O(learned_clauses) — iterates active arena once. Runs every
    /// BETWEEN_SOLVE_USED_DECAY_INTERVAL solves (100), so amortized overhead
    /// is negligible for IC3 workloads.
    fn decay_used_flags_between_solves(&mut self) {
        let mut decayed = 0u64;
        let indices: Vec<_> = self.arena.active_indices().collect();
        for idx in indices {
            if self.arena.is_learned(idx) && self.arena.used(idx) > 0 {
                self.arena.decay_used(idx);
                decayed += 1;
            }
        }
        self.stats.between_solve_used_decays += decayed;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count_active_learned_clauses(solver: &Solver) -> usize {
        solver
            .arena
            .indices()
            .filter(|&idx| solver.arena.is_active(idx) && solver.arena.is_learned(idx))
            .count()
    }

    /// IC3 mode retains all learned clauses when below the conservative
    /// GC threshold (#8643, #8672). With only 100 learned clauses and
    /// incremental_solve_count=1, IC3 GC does not fire.
    #[test]
    fn between_solve_reduce_ic3_retains_below_threshold() {
        let mut solver = Solver::new(128);
        solver.set_ic3_mode();

        let mut learned = Vec::new();
        for i in 0..100u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i))], true);
            let glue = 5 + (i % 3);
            solver.arena.set_lbd(idx, glue);
            learned.push((idx, glue));
        }

        solver.num_conflicts = BETWEEN_SOLVE_REDUCE_CONFLICT_INTERVAL;
        solver.cold.incremental_solve_count = 1;

        solver.between_solve_reduce();

        // IC3 mode below threshold: all learned clauses retained, no deletion.
        assert_eq!(
            count_active_learned_clauses(&solver),
            learned.len(),
            "IC3 between-solve GC must retain all clauses below threshold"
        );
        for (idx, old_glue) in learned {
            assert!(
                solver.arena.is_active(idx),
                "learned clause {idx} must remain active in IC3 mode below threshold"
            );
            assert_eq!(
                solver.arena.lbd(idx),
                old_glue,
                "learned clause {idx} LBD must be unchanged below threshold"
            );
        }
        // No reduction stats should be recorded.
        assert_eq!(solver.stats.between_solve_reductions, 0);
        assert_eq!(solver.stats.between_solve_clauses_deleted, 0);
    }

    /// IC3 GC fires when learned count exceeds the conservative threshold
    /// and prunes only high-LBD unused clauses (#8672).
    #[test]
    fn ic3_gc_prunes_high_lbd_unused_clauses() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add some irredundant clauses to establish a base.
        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }
        let irredundant_before = solver.arena.irredundant_count();
        assert!(irredundant_before >= 10);

        // IC3_GC threshold = max(irredundant * 10, 1000). With 10 irredundant,
        // threshold = 1000. Add 1100 high-LBD learned clauses to exceed it.
        let mut high_lbd_count = 0usize;
        let mut low_lbd_count = 0usize;
        for i in 20..1120u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            if i % 5 == 0 {
                // ~20% are core/tier1 (LBD <= 6) — should be retained
                solver.arena.set_lbd(idx, 2);
                low_lbd_count += 1;
            } else {
                // ~80% are high-LBD (> 6) — candidates for GC
                solver.arena.set_lbd(idx, 10 + (i % 8));
                // Ensure used=0 so they're eligible for GC
                while solver.arena.used(idx) > 0 {
                    solver.arena.decay_used(idx);
                }
                high_lbd_count += 1;
            }
        }

        let total_learned_before = count_active_learned_clauses(&solver);
        assert_eq!(total_learned_before, 1100);

        // Set conditions for IC3 GC to fire.
        solver.cold.incremental_solve_count = IC3_GC_MIN_SOLVES;

        solver.between_solve_reduce();

        let total_learned_after = count_active_learned_clauses(&solver);

        // Should have deleted some clauses (IC3_GC_FRACTION=25% of high-LBD unused).
        assert!(
            total_learned_after < total_learned_before,
            "IC3 GC should have pruned clauses: before={total_learned_before}, after={total_learned_after}"
        );

        // Low-LBD clauses (LBD<=6) must all be retained.
        let remaining_low_lbd = solver
            .arena
            .indices()
            .filter(|&idx| {
                solver.arena.is_active(idx)
                    && solver.arena.is_learned(idx)
                    && solver.arena.lbd(idx) <= IC3_GC_MIN_LBD
            })
            .count();
        assert_eq!(
            remaining_low_lbd, low_lbd_count,
            "IC3 GC must retain all low-LBD (<=6) clauses"
        );

        // Should have deleted ~25% of high-LBD clauses.
        let deleted = total_learned_before - total_learned_after;
        let expected_max_deleted = (high_lbd_count * IC3_GC_FRACTION) / 100 + 1;
        assert!(
            deleted <= expected_max_deleted,
            "IC3 GC deleted too many: {deleted} > expected max {expected_max_deleted}"
        );
        assert!(deleted > 0, "IC3 GC should have deleted at least 1 clause");

        // Stats should reflect the GC.
        assert_eq!(solver.stats.between_solve_reductions, 1);
        assert!(solver.stats.between_solve_clauses_deleted > 0);

        // Irredundant clauses must be untouched.
        assert_eq!(
            solver.arena.irredundant_count(),
            irredundant_before,
            "IC3 GC must never touch irredundant (blocking) clauses"
        );
    }

    /// IC3 GC does not fire before IC3_GC_MIN_SOLVES even with many learned clauses.
    #[test]
    fn ic3_gc_respects_min_solves_ramp() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add enough learned clauses to exceed any threshold.
        for i in 0..2000u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 15);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        // Set solve count just below the minimum.
        solver.cold.incremental_solve_count = IC3_GC_MIN_SOLVES - 1;

        solver.between_solve_reduce();

        // No GC should have fired.
        assert_eq!(
            count_active_learned_clauses(&solver),
            2000,
            "IC3 GC must not fire before IC3_GC_MIN_SOLVES"
        );
        assert_eq!(solver.stats.between_solve_reductions, 0);
    }

    /// IC3 GC (ic3_between_solve_gc) must protect IC3 lemmas even when
    /// they have high LBD and used=0 (#8673).
    #[test]
    fn ic3_gc_preserves_ic3_lemmas() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }

        let mut ic3_lemma_offsets = Vec::new();
        for i in 20..1120u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 12);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
            if i % 10 == 0 {
                solver.arena.set_ic3_lemma(idx, true);
                ic3_lemma_offsets.push(idx);
            }
        }

        assert!(!ic3_lemma_offsets.is_empty());
        let before = count_active_learned_clauses(&solver);

        solver.cold.incremental_solve_count = IC3_GC_MIN_SOLVES;
        solver.between_solve_reduce();

        assert!(
            solver.stats.between_solve_clauses_deleted > 0,
            "should have pruned some clauses"
        );
        assert!(
            count_active_learned_clauses(&solver) < before,
            "learned count should decrease"
        );

        for &offset in &ic3_lemma_offsets {
            assert!(
                solver.arena.is_active(offset),
                "IC3 lemma at offset {offset} was deleted by ic3_between_solve_gc"
            );
            assert!(
                solver.arena.is_ic3_lemma(offset),
                "IC3 lemma flag cleared at offset {offset}"
            );
        }
    }

    // ═══════════════════════════════════════════════════════════════════
    // Tests for ic3_enforce_learned_cap (#8672)
    // ═══════════════════════════════════════════════════════════════════

    fn count_active_ic3_lemmas(solver: &Solver) -> usize {
        solver
            .arena
            .indices()
            .filter(|&idx| {
                solver.arena.is_active(idx)
                    && solver.arena.is_learned(idx)
                    && solver.arena.is_ic3_lemma(idx)
            })
            .count()
    }

    fn count_active_core_learned(solver: &Solver) -> usize {
        solver
            .arena
            .indices()
            .filter(|&idx| {
                solver.arena.is_active(idx)
                    && solver.arena.is_learned(idx)
                    && solver.arena.lbd(idx) <= CORE_LBD
            })
            .count()
    }

    /// ic3_enforce_learned_cap does not fire when below the cap.
    #[test]
    fn test_ic3_learned_cap_below_threshold_no_reduction() {
        let mut solver = Solver::new(128);
        solver.set_ic3_mode();

        // Add irredundant clauses.
        for i in 0..20u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }

        // Add fewer learned clauses than the cap.
        // cap = max(20 * 5, 2000) = 2000. Add 100 learned clauses.
        for i in 0..100u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 128))], true);
            solver.arena.set_lbd(idx, 8);
        }

        let before = count_active_learned_clauses(&solver);
        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        solver.ic3_enforce_learned_cap();
        let after = count_active_learned_clauses(&solver);

        assert_eq!(
            before, after,
            "cap enforcement must not reduce below threshold"
        );
        assert_eq!(solver.stats.between_solve_reductions, 0);
    }

    /// ic3_enforce_learned_cap only fires on interval-aligned solve counts.
    #[test]
    fn test_ic3_learned_cap_respects_check_interval() {
        let mut solver = Solver::new(128);
        solver.set_ic3_mode();

        // Add enough learned clauses to exceed the min cap (2000).
        for i in 0..3000u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 128))], true);
            solver.arena.set_lbd(idx, 10);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        let before = count_active_learned_clauses(&solver);
        assert!(before >= 3000);

        // Set solve count to a non-aligned value.
        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL + 1;
        solver.ic3_enforce_learned_cap();
        let after = count_active_learned_clauses(&solver);

        assert_eq!(
            before, after,
            "cap enforcement must not fire on non-aligned solve count"
        );
    }

    /// ic3_enforce_learned_cap reduces learned clauses when above cap.
    #[test]
    fn test_ic3_learned_cap_reduces_above_threshold() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add irredundant clauses.
        for i in 0..50u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }
        let irredundant = solver.arena.irredundant_count();

        // cap = max(irredundant * 5, 2000) = max(250, 2000) = 2000
        // Add 3000 learned clauses to exceed the cap.
        for i in 0..3000u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 10 + (i % 5));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        let before = count_active_learned_clauses(&solver);
        assert!(
            before >= 3000,
            "precondition: learned count should be >= 3000"
        );

        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        solver.ic3_enforce_learned_cap();

        let after = count_active_learned_clauses(&solver);
        let cap = irredundant
            .saturating_mul(IC3_MAX_LEARNED_FACTOR)
            .max(IC3_MIN_LEARNED_CAP);

        assert!(
            after < before,
            "cap enforcement must reduce clause count: before={before}, after={after}"
        );
        // After reduction, count should be at or below the cap.
        // Target is 75% of cap, but we may not hit exactly due to protected clauses.
        assert!(
            after <= cap,
            "after reduction, learned count {after} should be at or below cap {cap}"
        );
        assert!(solver.stats.between_solve_reductions > 0);
        assert!(solver.stats.between_solve_clauses_deleted > 0);

        // Irredundant clauses must be untouched.
        assert_eq!(
            solver.arena.irredundant_count(),
            irredundant,
            "cap enforcement must never touch irredundant clauses"
        );
    }

    /// ic3_enforce_learned_cap protects IC3 lemmas from deletion.
    #[test]
    fn test_ic3_learned_cap_protects_ic3_lemmas() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add irredundant base.
        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }

        // Add IC3 lemma clauses (with IC3_LEMMA_BIT set).
        let mut ic3_lemma_count = 0usize;
        for i in 0..500u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 8);
            solver.arena.set_ic3_lemma(idx, true);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
            ic3_lemma_count += 1;
        }

        // Add non-lemma learned clauses to push above cap.
        for i in 0..3000u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 12 + (i % 4));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        let before_lemmas = count_active_ic3_lemmas(&solver);
        assert_eq!(before_lemmas, ic3_lemma_count);

        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        solver.ic3_enforce_learned_cap();

        let after_lemmas = count_active_ic3_lemmas(&solver);
        assert_eq!(
            after_lemmas, before_lemmas,
            "IC3 lemmas must be protected from cap enforcement: \
             before={before_lemmas}, after={after_lemmas}"
        );
    }

    /// ic3_enforce_learned_cap protects core clauses (LBD <= 2).
    #[test]
    fn test_ic3_learned_cap_protects_core_clauses() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add irredundant base.
        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }

        // Add core learned clauses (LBD = 2).
        let mut core_count = 0usize;
        for i in 0..500u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 2);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
            core_count += 1;
        }

        // Add high-LBD learned clauses to push above cap.
        for i in 0..3000u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 15 + (i % 3));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        let before_core = count_active_core_learned(&solver);
        assert_eq!(before_core, core_count);

        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        solver.ic3_enforce_learned_cap();

        let after_core = count_active_core_learned(&solver);
        assert_eq!(
            after_core, before_core,
            "core clauses (LBD<=2) must be protected from cap enforcement: \
             before={before_core}, after={after_core}"
        );
    }

    /// ic3_enforce_learned_cap prefers deleting unused clauses over used ones.
    #[test]
    fn test_ic3_learned_cap_prefers_unused_deletion() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add irredundant base.
        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }

        // Add 1500 "used" learned clauses (used > 0).
        let mut used_indices = Vec::new();
        for i in 0..1500u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 8);
            // Keep used > 0 (default after add_clause_db).
            used_indices.push(idx);
        }

        // Add 1500 "unused" learned clauses (used = 0).
        for i in 0..1500u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 256))], true);
            solver.arena.set_lbd(idx, 8);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        // 3000 total learned, cap = 2000, need to delete ~1500 (to 75% of cap = 1500).
        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        solver.ic3_enforce_learned_cap();

        // Used clauses should survive because unused clauses (1500) should be
        // deleted first, bringing us to 1500 which is already at the 75% target.
        let remaining_used = used_indices
            .iter()
            .filter(|&&idx| solver.arena.is_active(idx))
            .count();
        assert!(
            remaining_used >= 1400,
            "used clauses should mostly survive: {remaining_used}/1500 remain"
        );
    }

    /// ic3_enforce_learned_cap holds the bound across simulated 1000+ queries.
    ///
    /// Simulates a long IC3 workload by repeatedly adding learned clauses
    /// and calling ic3_enforce_learned_cap at regular intervals. Verifies
    /// that the learned clause count never grows beyond the cap + one
    /// interval's worth of new clauses.
    #[test]
    fn test_ic3_learned_cap_holds_across_1000_queries() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        // Add irredundant base.
        for i in 0..50u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }
        let irredundant = solver.arena.irredundant_count();
        let cap = irredundant
            .saturating_mul(IC3_MAX_LEARNED_FACTOR)
            .max(IC3_MIN_LEARNED_CAP);

        // Simulate 2000 IC3 queries, each learning 10 clauses.
        let clauses_per_query = 10u32;
        let total_queries = 2000u64;
        let mut max_learned = 0usize;

        for q in 1..=total_queries {
            // Simulate learned clauses from this query.
            for j in 0..clauses_per_query {
                let v = (q as u32 * clauses_per_query + j) % 256;
                let idx = solver.add_clause_db(&[Literal::positive(Variable(v))], true);
                solver.arena.set_lbd(idx, 5 + (j % 10));
                // Decay used to make some clauses eligible for GC.
                if j % 3 == 0 {
                    while solver.arena.used(idx) > 0 {
                        solver.arena.decay_used(idx);
                    }
                }
            }

            solver.cold.incremental_solve_count = q;
            solver.ic3_enforce_learned_cap();

            let current_learned = count_active_learned_clauses(&solver);
            if current_learned > max_learned {
                max_learned = current_learned;
            }
        }

        let final_learned = count_active_learned_clauses(&solver);

        // The cap enforcement fires every IC3_LEARNED_CAP_CHECK_INTERVAL (50)
        // queries. Between firings, up to 50 * 10 = 500 clauses accumulate.
        // So the peak should be at most cap + 500.
        let max_expected =
            cap + (IC3_LEARNED_CAP_CHECK_INTERVAL as usize * clauses_per_query as usize);
        assert!(
            max_learned <= max_expected,
            "peak learned clause count {max_learned} exceeds expected max {max_expected} \
             (cap={cap}, check_interval={IC3_LEARNED_CAP_CHECK_INTERVAL})"
        );

        // Final count must be at or below cap + one interval's worth.
        assert!(
            final_learned <= max_expected,
            "final learned clause count {final_learned} exceeds expected max {max_expected}"
        );

        // Without the cap, 2000 queries * 10 clauses = 20000 learned clauses
        // would accumulate. The cap should keep it well below that.
        assert!(
            final_learned < 20000,
            "final learned count {final_learned} suggests cap is not working"
        );

        // Irredundant clauses must be untouched throughout.
        assert_eq!(
            solver.arena.irredundant_count(),
            irredundant,
            "irredundant clauses must survive cap enforcement"
        );
    }

    // ═══════════════════════════════════════════════════════════════════
    // Tests for ic3_memory_pressure_reduce (#8673)
    // ═══════════════════════════════════════════════════════════════════

    /// Memory pressure reduce does not fire when arena is below threshold.
    #[test]
    fn test_ic3_memory_pressure_below_threshold_no_reduction() {
        let mut solver = Solver::new(128);
        solver.set_ic3_mode();

        // Add a moderate number of irredundant clauses to establish baseline.
        for i in 0..100u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable((i + 1) % 128)),
                ],
                false,
            );
        }

        // Capture baseline now.
        solver.cold.ic3_baseline_arena_words = solver.arena.len();
        let baseline = solver.cold.ic3_baseline_arena_words;
        assert!(baseline > 0);

        // Add some learned clauses — but not enough to exceed 8x baseline.
        for i in 0..50u32 {
            let idx = solver.add_clause_db(&[Literal::positive(Variable(i % 128))], true);
            solver.arena.set_lbd(idx, 8);
        }

        let before = count_active_learned_clauses(&solver);
        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL;
        solver.ic3_memory_pressure_reduce();
        let after = count_active_learned_clauses(&solver);

        assert_eq!(
            before, after,
            "memory pressure reduce must not fire below threshold"
        );
        assert_eq!(solver.stats.ic3_memory_pressure_reduces, 0);
    }

    /// Memory pressure reduce fires when arena exceeds threshold and deletes clauses.
    #[test]
    fn test_ic3_memory_pressure_fires_above_threshold() {
        // Use enough variables to create a realistic arena that exceeds
        // IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS (50K words = 200KB).
        let num_vars = 4096;
        let mut solver = Solver::new(num_vars);
        solver.set_ic3_mode();

        // Add irredundant base clauses to establish a moderate baseline.
        // ~500 clauses * 12 words = ~6000 words.
        let mut lits_buf = Vec::new();
        for i in 0..500u32 {
            lits_buf.clear();
            for j in 0..7u32 {
                lits_buf.push(Literal::positive(Variable((i * 7 + j) % num_vars as u32)));
            }
            solver.add_clause_db(&lits_buf, false);
        }

        // Capture baseline before learned clauses.
        solver.cold.ic3_baseline_arena_words = solver.arena.len();
        let baseline = solver.cold.ic3_baseline_arena_words;
        assert!(baseline > 0, "baseline must be > 0 after adding clauses");

        // Add many learned clauses with 10+ literals to exceed both:
        // 1. IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS (50K words)
        // 2. IC3_MEMORY_PRESSURE_ARENA_FACTOR * baseline (8x)
        //
        // Each 10-literal clause = 15 words. Need ~4000 clauses to reach 60K words.
        // baseline ~6000 words, threshold = 48K words. 4000 * 15 = 60K > 48K.
        for i in 0..4000u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable((i * 10 + j) % num_vars as u32)));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 8 + (i % 6));
            // Make half unused so they're eligible for deletion.
            if i % 2 == 0 {
                while solver.arena.used(idx) > 0 {
                    solver.arena.decay_used(idx);
                }
            }
        }

        // Verify arena has grown past both thresholds.
        let arena_words = solver.arena.len();
        let threshold = baseline.saturating_mul(IC3_MEMORY_PRESSURE_ARENA_FACTOR);
        assert!(
            arena_words > IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS,
            "precondition: arena words {arena_words} must exceed min {IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS}"
        );
        assert!(
            arena_words > threshold,
            "precondition: arena words {arena_words} must exceed threshold {threshold}"
        );

        let before = count_active_learned_clauses(&solver);
        assert!(
            before >= 4000,
            "precondition: learned count {before} must be >= 4000"
        );

        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL;
        solver.ic3_memory_pressure_reduce();

        let after = count_active_learned_clauses(&solver);
        assert!(
            after < before,
            "memory pressure reduce must delete clauses: before={before}, after={after}"
        );
        assert!(
            solver.stats.ic3_memory_pressure_reduces > 0,
            "memory pressure stat must be incremented"
        );
        assert!(
            solver.stats.between_solve_clauses_deleted > 0,
            "between_solve_clauses_deleted must be incremented"
        );
    }

    /// Memory pressure reduce protects IC3 lemmas and core clauses.
    #[test]
    fn test_ic3_memory_pressure_protects_lemmas_and_core() {
        let num_vars = 4096;
        let mut solver = Solver::new(num_vars);
        solver.set_ic3_mode();

        // Irredundant base: ~500 clauses to establish a meaningful baseline.
        let mut lits_buf = Vec::new();
        for i in 0..500u32 {
            lits_buf.clear();
            for j in 0..7u32 {
                lits_buf.push(Literal::positive(Variable((i * 7 + j) % num_vars as u32)));
            }
            solver.add_clause_db(&lits_buf, false);
        }
        solver.cold.ic3_baseline_arena_words = solver.arena.len();

        // Add IC3 lemmas (should be protected).
        let mut ic3_lemma_offsets = Vec::new();
        for i in 0..100u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable((i * 10 + j) % num_vars as u32)));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 8);
            solver.arena.set_ic3_lemma(idx, true);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
            ic3_lemma_offsets.push(idx);
        }

        // Add core clauses (LBD <= 2, should be protected).
        let mut core_offsets = Vec::new();
        for i in 0..100u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable(
                    ((i + 100) * 10 + j) % num_vars as u32,
                )));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 2);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
            core_offsets.push(idx);
        }

        // Add deletable clauses (high LBD, unused) to exceed arena threshold.
        for i in 0..4000u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable(
                    ((i + 200) * 10 + j) % num_vars as u32,
                )));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 12 + (i % 4));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL;
        solver.ic3_memory_pressure_reduce();

        // IC3 lemmas must survive.
        for &offset in &ic3_lemma_offsets {
            assert!(
                solver.arena.is_active(offset),
                "IC3 lemma at offset {offset} was deleted by memory pressure reduce"
            );
        }

        // Core clauses must survive.
        for &offset in &core_offsets {
            assert!(
                solver.arena.is_active(offset),
                "core clause at offset {offset} was deleted by memory pressure reduce"
            );
        }
    }

    /// Memory pressure reduce respects check interval.
    #[test]
    fn test_ic3_memory_pressure_respects_check_interval() {
        let mut solver = Solver::new(256);
        solver.set_ic3_mode();

        for i in 0..10u32 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::negative(Variable(i + 1)),
                ],
                false,
            );
        }
        solver.cold.ic3_baseline_arena_words = solver.arena.len();

        // Add many learned clauses to exceed threshold.
        let mut lits_buf = Vec::new();
        for i in 0..300u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable((i * 10 + j) % 256)));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 10);
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        let before = count_active_learned_clauses(&solver);

        // Set solve count to non-aligned value.
        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL + 1;
        solver.ic3_memory_pressure_reduce();
        let after = count_active_learned_clauses(&solver);

        assert_eq!(
            before, after,
            "memory pressure reduce must not fire on non-aligned solve count"
        );
    }

    /// Memory pressure reduce updates baseline after reduction.
    #[test]
    fn test_ic3_memory_pressure_updates_baseline() {
        let num_vars = 4096;
        let mut solver = Solver::new(num_vars);
        solver.set_ic3_mode();

        // Irredundant base.
        let mut lits_buf = Vec::new();
        for i in 0..500u32 {
            lits_buf.clear();
            for j in 0..7u32 {
                lits_buf.push(Literal::positive(Variable((i * 7 + j) % num_vars as u32)));
            }
            solver.add_clause_db(&lits_buf, false);
        }
        solver.cold.ic3_baseline_arena_words = solver.arena.len();
        let original_baseline = solver.cold.ic3_baseline_arena_words;

        // Add enough clauses to trigger memory pressure.
        for i in 0..4000u32 {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable((i * 10 + j) % num_vars as u32)));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 10 + (i % 5));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL;
        solver.ic3_memory_pressure_reduce();

        // Baseline should be updated to post-reduction arena size.
        assert!(
            solver.stats.ic3_memory_pressure_reduces > 0,
            "precondition: memory pressure reduce must have fired"
        );
        assert!(
            solver.cold.ic3_baseline_arena_words > original_baseline,
            "baseline should be updated to post-reduction arena size: \
             original={original_baseline}, updated={}",
            solver.cold.ic3_baseline_arena_words
        );
    }

    // ═══════════════════════════════════════════════════════════════════
    // Regression tests: between-solve reduction with a persistent
    // ROOT-LEVEL trail (IC3 incremental path). A learned clause can be the
    // reason for a level-0 trail literal (analyze_and_backtrack_ic3
    // enqueues the UIP with the learned clause as reason after
    // backtracking to level 0), and the level-0 trail persists across
    // incremental IC3 solves. The old code debug_assert'ed trail.is_empty()
    // — panicking the model-checker-consumer → ay-chc IC3 lane — and, absent the assert,
    // would delete the reason clause, leaving var_data[v].reason dangling.
    // ═══════════════════════════════════════════════════════════════════

    /// Shared setup: solver under memory pressure with one level-0 trail
    /// literal whose reason is the WORST-ranked learned clause (highest
    /// LBD, largest, unused) — i.e. the first deletion candidate absent
    /// reason protection. Returns (solver, trail_lit).
    fn solver_with_root_level_trail_under_pressure(num_learned: u32) -> (Solver, Literal) {
        let num_vars = 4096;
        let mut solver = Solver::new(num_vars);
        solver.set_ic3_mode();

        // Irredundant base to establish a moderate baseline.
        let mut lits_buf = Vec::new();
        for i in 0..500u32 {
            lits_buf.clear();
            for j in 0..7u32 {
                lits_buf.push(Literal::positive(Variable((i * 7 + j) % num_vars as u32)));
            }
            solver.add_clause_db(&lits_buf, false);
        }
        solver.cold.ic3_baseline_arena_words = solver.arena.len();

        // The reason clause: learned, worst-ranked (LBD 30, 12 literals,
        // unused) so it sorts FIRST in the unused deletion pool.
        lits_buf.clear();
        for j in 0..12u32 {
            lits_buf.push(Literal::positive(Variable(j)));
        }
        let reason_idx = solver.add_clause_db(&lits_buf, true);
        solver.arena.set_lbd(reason_idx, 30);
        while solver.arena.used(reason_idx) > 0 {
            solver.arena.decay_used(reason_idx);
        }

        // Bulk learned clauses (LBD 8-13, 10 literals, unused) to exceed
        // the reduction gates.
        for i in 0..num_learned {
            lits_buf.clear();
            for j in 0..10u32 {
                lits_buf.push(Literal::positive(Variable(
                    ((i + 2) * 10 + j) % num_vars as u32,
                )));
            }
            let idx = solver.add_clause_db(&lits_buf, true);
            solver.arena.set_lbd(idx, 8 + (i % 6));
            while solver.arena.used(idx) > 0 {
                solver.arena.decay_used(idx);
            }
        }

        // Root-level assignment whose reason is the worst-ranked learned
        // clause — exactly what analyze_and_backtrack_ic3 produces when a
        // conflict backtracks to level 0 and the UIP is enqueued with the
        // freshly learned clause as reason. The level-0 trail persists
        // across incremental IC3 solves.
        assert_eq!(solver.decision_level, 0);
        let trail_lit = Literal::positive(Variable(0));
        solver.enqueue(trail_lit, Some(ClauseRef(reason_idx as u32)));
        assert_eq!(solver.trail.len(), 1);

        (solver, trail_lit)
    }

    /// Assert the trail literal is still assigned at level 0 and its reason
    /// points at an ACTIVE arena clause whose first literal is the trail
    /// literal (robust under arena compaction, which remaps reason offsets).
    fn assert_trail_reason_intact(solver: &Solver, trail_lit: Literal) {
        assert_eq!(solver.trail.len(), 1, "level-0 trail must persist");
        assert_eq!(solver.trail[0], trail_lit);
        let vd = solver.var_data[trail_lit.variable().index()];
        assert_eq!(vd.level, 0);
        assert!(
            is_clause_reason(vd.reason),
            "level-0 literal must keep its clause reason"
        );
        let reason_now = vd.reason as usize;
        assert!(
            solver.arena.is_active(reason_now),
            "reason clause of level-0 trail literal was deleted by between-solve reduction"
        );
        assert_eq!(
            solver.arena.literals(reason_now)[0],
            trail_lit,
            "reason offset points at a different clause (dangling/aliased reason)"
        );
    }

    /// ic3_memory_pressure_reduce with a persistent root-level trail must
    /// not panic, must still reduce, and must not delete the trail
    /// literal's reason clause.
    #[test]
    fn test_ic3_memory_pressure_reduce_with_root_level_trail_protects_reason() {
        let (mut solver, trail_lit) = solver_with_root_level_trail_under_pressure(4000);

        // Precondition: arena exceeds both memory-pressure gates.
        let threshold = solver
            .cold
            .ic3_baseline_arena_words
            .saturating_mul(IC3_MEMORY_PRESSURE_ARENA_FACTOR);
        assert!(solver.arena.len() > IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS);
        assert!(solver.arena.len() > threshold);

        solver.cold.incremental_solve_count = IC3_MEMORY_PRESSURE_CHECK_INTERVAL;
        // Old code: debug_assert!(trail.is_empty()) panicked here
        // ("BUG: ic3_memory_pressure_reduce called with non-empty trail").
        solver.ic3_memory_pressure_reduce();

        assert!(
            solver.stats.ic3_memory_pressure_reduces > 0,
            "memory pressure reduce must still fire with a root-level trail"
        );
        assert!(
            solver.stats.between_solve_clauses_deleted > 0,
            "reduction must still delete unprotected clauses"
        );
        assert_trail_reason_intact(&solver, trail_lit);
    }

    /// ic3_enforce_learned_cap with a persistent root-level trail must not
    /// panic and must not delete the trail literal's reason clause.
    #[test]
    fn test_ic3_learned_cap_with_root_level_trail_protects_reason() {
        // 500 irredundant → cap = max(5*500, 2000) = 2500; 2600+1 learned
        // exceeds it; excess = 2601 - 1875 = 726 worst-first deletions,
        // which absent protection would include the worst-ranked reason
        // clause at the front of the unused pool.
        let (mut solver, trail_lit) = solver_with_root_level_trail_under_pressure(2600);

        solver.cold.incremental_solve_count = IC3_LEARNED_CAP_CHECK_INTERVAL;
        // Old code: debug_assert!(trail.is_empty()) panicked here.
        solver.ic3_enforce_learned_cap();

        assert!(
            solver.stats.between_solve_clauses_deleted > 0,
            "cap enforcement must still delete unprotected clauses"
        );
        assert_trail_reason_intact(&solver, trail_lit);
    }
}
