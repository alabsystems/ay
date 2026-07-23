// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arena locality compaction (CaDiCaL arenatype=3, #8030).
//!
//! After `reduce_db()` deletes learned clauses, reorder remaining clauses
//! in the arena by VMTF decision-queue order so clauses watched by the
//! same literal are contiguous in memory. This improves L1/L2 cache hit
//! rates during BCP.
//!
//! Algorithm: iterate VMTF queue (vmtf_last -> vmtf_prev), for each
//! variable visit both-polarity watch lists (likely_phase first), copy
//! referenced clauses to fresh arena. Sweep remaining live clauses.
//! Remap clause refs in-place in existing watch lists (preserving BCP
//! traversal order). Remap trail reasons and LRAT clause_ids.
//!
//! Reference: CaDiCaL collect.cpp:385-399, Kissat collect.c:213-275.

use super::*;
use crate::vsids::INVALID_VAR;

impl Solver {
    /// Returns true when dead arena words exceed the adaptive compaction
    /// threshold (#8102).
    ///
    /// The threshold scales with formula size (25% for small arenas, up to 50%
    /// for large arenas) and biases upward when recent inprocessing overhead
    /// indicates compaction is expensive. This reduces compaction frequency on
    /// large formulas where the O(clauses + watches + vars) cost is high.
    ///
    /// The VMTF queue is now maintained in both focused and stable modes
    /// (#8036), matching CaDiCaL's `bump_variable_queue` which runs
    /// unconditionally. Arena compaction can run in either mode.
    ///
    /// Uses layout-invariant accounting units (`accounting_len` /
    /// `accounting_dead_words`, legacy 5-word-header equivalents) so the R2
    /// clause-header slimming — a pure layout change — reproduces the exact
    /// pre-R2 compaction cadence and search trajectory.
    pub(super) fn should_compact_arena(&self) -> bool {
        let threshold_pct = self.adaptive_compaction_threshold_pct();
        self.arena.accounting_dead_words()
            > self.arena.accounting_len().saturating_mul(threshold_pct) / 100
    }

    /// Computes the adaptive arena compaction threshold percentage in `[25, 50]`.
    ///
    /// - Small arenas (<= 100K words): 25% (compact aggressively).
    /// - Large arenas (>= 10M words): 50% (tolerate more fragmentation).
    /// - Linear interpolation in between.
    /// - Overhead bias: +5% when last inprocessing overhead was 10-100ms,
    ///   +10% when > 100ms. Clamped to the [25, 50] range.
    fn adaptive_compaction_threshold_pct(&self) -> usize {
        const MIN_THRESHOLD_PCT: usize = 25;
        const MAX_THRESHOLD_PCT: usize = 50;
        const SMALL_ARENA_WORDS: usize = 100_000;
        const LARGE_ARENA_WORDS: usize = 10_000_000;

        // Legacy 5-word-header accounting units — see `should_compact_arena`.
        let arena_words = self.arena.accounting_len();
        let base_pct = if arena_words <= SMALL_ARENA_WORDS {
            MIN_THRESHOLD_PCT
        } else if arena_words >= LARGE_ARENA_WORDS {
            MAX_THRESHOLD_PCT
        } else {
            // Linear interpolation: 25% at 100K words → 50% at 10M words.
            let span = LARGE_ARENA_WORDS - SMALL_ARENA_WORDS;
            let growth = arena_words - SMALL_ARENA_WORDS;
            MIN_THRESHOLD_PCT + growth.saturating_mul(MAX_THRESHOLD_PCT - MIN_THRESHOLD_PCT) / span
        };

        // Bias upward when compaction overhead is high (#8099 provides the metric).
        let overhead_bias = if self.cold.last_inprocessing_overhead_ms > 100.0 {
            10
        } else if self.cold.last_inprocessing_overhead_ms >= 10.0 {
            5
        } else {
            0
        };

        (base_pct + overhead_bias).clamp(MIN_THRESHOLD_PCT, MAX_THRESHOLD_PCT)
    }

    /// Compact the clause arena in VMTF decision-queue order for cache locality.
    /// Reference: CaDiCaL collect.cpp:385-399 (arenatype=3).
    pub(super) fn compact_arena_locality(&mut self) {
        // Structural invariants: compaction requires a quiescent solver state.
        // Skip compaction (rather than panic) when BCP has pending work — this
        // can happen legitimately during reduce_db since learned clause deletion
        // doesn't drain the propagation queue.
        if self.qhead < self.trail.len() || !self.pending_theory_conflicts.is_empty() {
            return;
        }

        // 1. Build clause visit order from VMTF queue + watch lists.
        let arena_len = self.arena.len();
        let mut ordered: Vec<u32> = Vec::new();
        // Reuse persistent bitmap to avoid arena-proportional allocation (#8602).
        self.cold.gc_seen_buf.resize(arena_len, false);
        self.cold.gc_seen_buf.fill(false);

        // Walk VMTF queue: most-recently-bumped first, likely_phase first per variable.
        let mut var = self.vsids.vmtf_last();
        while var != INVALID_VAR {
            let var_idx = var as usize;
            // Two phases: likely first, then unlikely.
            let positive = self.phase.get(var_idx).copied().is_some_and(|p| p > 0);
            for &use_positive in &[true, false] {
                let phase = if use_positive { positive } else { !positive };
                let lit = if phase {
                    Literal::positive(Variable(var))
                } else {
                    Literal::negative(Variable(var))
                };
                let wl = self.watches.get_watches(lit);
                for i in 0..wl.len() {
                    if !wl.is_binary(i) {
                        let offset = wl.clause_ref(i).index();
                        if offset < arena_len
                            && !self.cold.gc_seen_buf[offset]
                            && self.arena.is_active(offset)
                        {
                            self.cold.gc_seen_buf[offset] = true;
                            ordered.push(offset as u32);
                        }
                    }
                }
            }
            var = self.vsids.vmtf_prev_of(var);
        }

        // 2. Sweep remaining live clauses not reached via any watch list.
        for offset in self.arena.active_indices() {
            if !self.cold.gc_seen_buf[offset] {
                ordered.push(offset as u32);
            }
        }

        if ordered.is_empty() {
            return;
        }

        self.cold.num_arena_compactions += 1;

        // 2b. Reattach JIT-detached watches BEFORE compaction (#8356).

        // 3. Compact arena in computed order.
        let remap = self.arena.compact_reorder(&ordered);

        // 4. Remap clause refs in-place in existing watch lists.
        // Critical: this preserves watch list ordering, which determines BCP
        // traversal order and search trajectory. The previous clear-and-rebuild
        // approach destroyed this ordering, causing >6x regressions on some
        // benchmarks (Battleship-14-26: 3s → 20s+ timeout).
        // Reference: CaDiCaL collect.cpp:216-262 flush_watches().
        self.watches.remap_clause_refs(&remap);

        // Binary-first invariant is maintained incrementally by remap_clause_refs.
        self.watches.debug_assert_binary_first();

        // 4b. Refresh blocker literals to current watched literal.
        // After arena compaction, clause literals may have been reordered by
        // replace() or other inprocessing, making cached blockers stale. Stale
        // blockers cause unnecessary slow-path clause reads in BCP (the blocker
        // check fails, forcing the solver to load clause data from the arena).
        // CaDiCaL flush_watches() (collect.cpp:238-242) refreshes blockers here.
        self.refresh_blocker_literals();

        // 5. Remap trail reasons.
        // Assigned variables with reason clauses must have valid remapped offsets
        // (reason clauses are protected from deletion by reason_clause_marks).
        // Unassigned variables may have stale reason fields from backtrack-store
        // elimination (#6991) — clear these to NO_REASON to prevent stale offsets
        // from aliasing new clauses in the compacted arena.
        for (var_idx, vd) in self.var_data.iter_mut().enumerate() {
            // #8373: Skip lazy theory reasons — their `reason` field is a table
            // index, not an arena clause offset. Remapping or clearing it would
            // corrupt the lazy reason lookup, causing conflict analysis failures.
            if is_clause_reason(vd.reason) && !vd.is_lazy_theory_reason() {
                let old = vd.reason as usize;
                if old < remap.len() && remap[old] != u32::MAX {
                    vd.reason = remap[old];
                } else if ay_prefetch::val_at(&self.vals, var_idx * 2) != 0 {
                    // Assigned variable with a deleted reason — this is a bug.
                    debug_assert!(
                        false,
                        "BUG: assigned variable {var_idx} has reason at deleted clause offset {old}"
                    );
                } else {
                    // Unassigned variable with stale reason — clear it.
                    vd.reason = NO_REASON;
                }
            }
        }

        // 6. Remap LRAT clause_ids side vector.
        if !self.cold.clause_ids.is_empty() {
            let old_ids = std::mem::take(&mut self.cold.clause_ids);
            let new_arena_len = self.arena.len();
            let mut new_ids = vec![0u64; new_arena_len];
            for &old_off in &ordered {
                let old_idx = old_off as usize;
                let new_off = remap[old_idx];
                if new_off != u32::MAX && old_idx < old_ids.len() {
                    let new_off_usize = new_off as usize;
                    if new_off_usize < new_ids.len() {
                        new_ids[new_off_usize] = old_ids[old_idx];
                    }
                }
            }
            self.cold.clause_ids = new_ids;
        }
        if !self.cold.bcp_learned_clause_birth_conflicts.is_empty() {
            let old_birth_conflicts =
                std::mem::take(&mut self.cold.bcp_learned_clause_birth_conflicts);
            let new_arena_len = self.arena.len();
            let mut new_birth_conflicts = vec![0u64; new_arena_len];
            for &old_off in &ordered {
                let old_idx = old_off as usize;
                let new_off = remap[old_idx];
                if new_off != u32::MAX && old_idx < old_birth_conflicts.len() {
                    let new_off_usize = new_off as usize;
                    if new_off_usize < new_birth_conflicts.len() {
                        new_birth_conflicts[new_off_usize] = old_birth_conflicts[old_idx];
                    }
                }
            }
            self.cold.bcp_learned_clause_birth_conflicts = new_birth_conflicts;
        }
        self.stats.remap_bcp_learned_1963_blocker_certs(&remap);

        // 7. Invalidate reason_clause_marks (#8100).
        // After remapping var_data[].reason (step 5), all arena offsets changed
        // so incremental marks are indexed by stale pre-compaction offsets.
        // Force a full rebuild on next ensure_reason_clause_marks_current().
        self.invalidate_reason_clause_marks();

        // 8. Remap LSCB lambda vector (arena offsets for reimplication).
        // Lambda stores ClauseRef values (arena offsets) for lazy reimplication
        // during backtracking. After arena compaction, these offsets are stale
        // and could alias different clauses in the compacted arena, causing
        // silent corruption during chronological backtrack (#8485).
        for entry in self.lambda.iter_mut() {
            if let Some(ref mut clause_ref) = entry {
                let old = clause_ref.index();
                if old < remap.len() && remap[old] != u32::MAX {
                    *clause_ref = ClauseRef(remap[old]);
                } else {
                    // Clause was deleted or offset is invalid — clear the entry.
                    // Backtrack will handle missing lambda entries gracefully
                    // by falling back to normal reimplication.
                    *entry = None;
                }
            }
        }

        // 9. Remap learned_clause_trail (arena offsets for eager subsumption).
        self.cold.learned_clause_trail.retain_mut(|off| {
            let old = *off;
            if old < remap.len() && remap[old] != u32::MAX {
                *off = remap[old] as usize;
                true
            } else {
                false
            }
        });

        // 9b. Remap IC3 constrained-clause offsets (husk adjudication #2).
        // `ic3_constrained_offsets` (pushed by add_constrained_clause) are raw
        // arena offsets. Without remapping, post-compaction stale offsets
        // alias arbitrary live clauses and cleanup_constrained_clauses would
        // arena.delete() unrelated transition-relation/lemma clauses — the
        // only validity check there is is_active(). Deleted/dropped entries
        // are removed (their clauses no longer exist).
        self.cold.ic3_constrained_offsets.retain_mut(|off| {
            let old = *off;
            if old < remap.len() && remap[old] != u32::MAX {
                *off = remap[old] as usize;
                true
            } else {
                false
            }
        });

        // 10. Remap original_clause_boundary.
        // After locality-aware reordering, original and learned clauses are
        // interleaved by VMTF order, so the single-offset boundary between
        // "all original below, all learned above" no longer holds. Set to
        // new arena length so the `idx >= boundary` guard in transred passes
        // all clauses through to the is_learned() check (always correct).
        self.cold.original_clause_boundary = self.arena.len();

        // 11. Invalidate gc_occ — arena offsets changed (#8078).
        // Without this, gc_occ contains pre-compaction clause offsets that
        // alias random positions in the compacted arena, causing garbage
        // literals to be read and OOB accesses / SIGBUS in BCP.
        self.gc_occ = None;
        // Drop the reuse scratch too (stale clause indices; cleared before
        // every reuse, so hygiene rather than correctness).
        self.gc_occ_scratch = None;
        self.cold.last_collect_trail_pos = 0;

        // 11b. Invalidate BVE occ lists — arena offsets changed (#8473).
        // BVE occ lists store clause arena offsets. After locality-aware
        // reordering, all offsets are remapped. Force a full rebuild on
        // the next BVE round (refresh_incremental or rebuild_with_vals).
        self.inproc.bve.invalidate_occ_lists();

        // 12. Invalidate JIT compiled formula — embedded arena offsets are stale.
        // JIT watch reattachment done in step 2b before compaction (#8356).
        //
        // Post-GC code recovery (#8523): instead of dropping the stash entirely,
        // stash the compiled formula (preserving code_snapshot and per_lit_code)
        // and mark all variables dirty. The next delta recompile regenerates all
        // functions with correct new clause IDs while preserving the JIT compilation
        // infrastructure. This avoids the complete JIT teardown that previously
        // forced a full recompile from scratch after every arena compaction.

        // 13. Shrink watch list capacities.
        self.watches.shrink_capacity();
    }

    /// Refresh blocker literals in all watch lists to match current watched
    /// literals in the arena.
    ///
    /// For each non-binary watcher in the watch list for literal `lit`, the
    /// blocker should be the OTHER watched literal of the clause (i.e., the
    /// one that is not `lit`). After inprocessing (vivification, subsumption,
    /// etc.) may have reordered clause literals, the cached blocker can become
    /// stale, causing unnecessary slow-path clause reads in BCP.
    ///
    /// Reference: CaDiCaL collect.cpp:238-242 (flush_watches blocker refresh).
    fn refresh_blocker_literals(&mut self) {
        for lit_idx in 0..self.watches.num_lists() {
            let lit = Literal::from_index(lit_idx);
            let mut wl = self.watches.get_watches_mut(lit);
            for i in 0..wl.len() {
                if wl.is_binary(i) {
                    continue;
                }
                let offset = wl.clause_ref(i).index();
                let clause_raw = wl.clause_raw(i);
                let (w0, w1) = self.arena.watched_literals(offset);
                // The blocker is the watched literal that is NOT this list's literal.
                let new_blocker = if w0 == lit { w1 } else { w0 };
                wl.set_entry(i, new_blocker.raw(), clause_raw);
            }
        }
    }
}
