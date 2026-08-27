// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backtracking with chronological reimplication and phase saving.

use super::*;

mod ic3;

impl Solver {
    /// Backtrack to the given level with phase saving and target/best updates.
    ///
    /// Implements lazy reimplication for chronological backtracking:
    /// - Literals at levels <= target_level are kept on the trail (out of order)
    /// - Only literals at levels > target_level are unassigned
    /// - Phase saving: when a variable is unassigned, we save its polarity
    /// - Target/best phase saving: if we reached a longer trail, save the phases
    ///
    /// REQUIRES: target_level <= decision_level (or no-op)
    /// ENSURES: decision_level == target_level, trail_lim.len() == target_level,
    ///          no variable assigned at level > target_level,
    ///          qhead <= trail.len(), no_conflict_until <= trail.len()
    pub(super) fn backtrack(&mut self, target_level: u32) {
        self.backtrack_core(target_level, true);
    }

    /// Backtrack to the given level without updating phase saving.
    ///
    /// Used during vivification where decisions are artificial and should not
    /// corrupt the phase heuristic. Same as `backtrack()` but skips:
    /// - Phase saving (no `self.phase[...] = ...`)
    /// - Target/best phase updates
    pub(super) fn backtrack_without_phase_saving(&mut self, target_level: u32) {
        self.backtrack_core(target_level, false);
    }

    /// Core backtracking: compact the trail, unassign variables above target_level.
    ///
    /// When `save_phases` is true (normal CDCL), captures target/best phases and
    /// saves each unassigned variable's polarity. When false (vivification),
    /// skips both to avoid corrupting heuristics with artificial decisions.
    ///
    /// Uses chronological backtracking with lazy reimplication: out-of-order
    /// literals at levels <= target are kept on the trail.
    ///
    /// LSCB (#8442): variables with lambda entries (MLI clauses) are checked
    /// during unassignment. If the lambda clause is unit at the target level
    /// (all other literals falsified at levels <= target), the variable is
    /// reimplied at the lower assertion level instead of being unassigned.
    fn backtrack_core(&mut self, target_level: u32, save_phases: bool) {
        // REQUIRES: target_level <= decision_level (callers must not request
        // backtrack to a level above the current one).
        debug_assert!(
            target_level <= self.decision_level,
            "BUG: backtrack to level {target_level} > decision_level {}",
            self.decision_level
        );

        if save_phases {
            self.update_target_and_best_phases();
        }

        if self.decision_level <= target_level {
            return;
        }

        // #relevancy-frontier-incremental: the incremental relevancy frontier
        // folds a PREFIX of the trail into its counters. Backtracking both
        // unassigns literals and COMPACTS the trail (chrono keeps out-of-order
        // lower-level literals), so this pass does two things for it: fold out
        // every literal that was folded in and is now unassigned, and count how
        // many folded literals SURVIVE. Compaction preserves trail order, so
        // the survivors are exactly the new folded prefix.
        //
        // `begin_unassign_fold` — NOT a bare `synced_len` read — is what opens
        // the fold: the frontier's occurrence lists are keyed by arena WORD
        // OFFSET, and an epoch-bumping clause-DB mutation (reduce_db deletion,
        // `replace` strengthening, and above all `compact_arena_locality`,
        // which rewrites the arena SHORTER with every offset moved) can land
        // between the query that synced the cache and this backtrack. It
        // re-checks the epoch and the arena watermarks exactly as `sync` does
        // and returns `None` — having dropped the cache, so the next query
        // rebuilds — rather than let the fold walk offsets that no longer
        // denote the clauses they were recorded for. `None` is also the usual
        // case (relevancy is off by default), and costs one load.
        let frontier_open = self.relevancy_frontier.begin_unassign_fold(
            self.arena.formula_epoch(),
            self.arena.len(),
            self.arena.num_clauses(),
        );
        // Whether the fold ran at all — i.e. whether there is incremental state
        // for the exactness pin at the bottom of this function to check.
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        let frontier_folded = frontier_open.is_some();
        let frontier_synced = frontier_open.unwrap_or(0);
        // Seeded below from `assigned_limit`: the compaction loop starts there,
        // so every folded trail entry BELOW it survives untouched.
        let mut frontier_kept;
        let mut frontier =
            (frontier_synced > 0).then(|| std::mem::take(&mut self.relevancy_frontier));

        let assigned_limit = if target_level == 0 {
            0
        } else {
            self.trail_lim[target_level as usize - 1]
        };
        frontier_kept = frontier_synced.min(assigned_limit);
        // CaDiCaL backtrack.cpp:52: assigned_limit within trail bounds
        debug_assert!(
            assigned_limit <= self.trail.len(),
            "BUG: assigned_limit ({assigned_limit}) > trail.len() ({})",
            self.trail.len(),
        );

        // CaDiCaL clips propagated to control[new_level+1].trail = start of
        // the level ABOVE target. In-order target_level literals don't need
        // re-propagation; only out-of-order compacted literals from higher
        // levels do. Save this before trail_lim truncation (#6931).
        let next_level_start = self.trail_lim[target_level as usize];
        let old_lrat_level0_unit_materialize_cursor = self.cold.lrat_level0_unit_materialize_cursor;
        let old_root_prefix_end = if target_level == 0 {
            next_level_start
        } else {
            0
        };
        let mut lrat_root_prefix_unchanged =
            target_level == 0 && old_root_prefix_end <= self.trail.len();

        let mut write_pos = assigned_limit;
        let mut read_pos = assigned_limit;

        while read_pos < self.trail.len() {
            let lit = self.trail[read_pos];
            let var = lit.variable();
            let var_level = self.var_data[var.index()].level;
            if target_level == 0
                && read_pos < old_root_prefix_end
                && (var_level != 0 || write_pos != read_pos)
            {
                lrat_root_prefix_unchanged = false;
            }

            if var_level > target_level {
                // CaDiCaL backtrack.cpp:11: trail literal must be true before unassign.
                debug_assert!(
                    self.var_lifecycle.is_removed(var.index())
                        || ay_prefetch::val_at(&self.vals, lit.index()) > 0,
                    "BUG: unassigning non-true {lit:?} (var={}, var_level={var_level}, target={target_level}, \
                     removed={}, trail_pos={})",
                    var.index(),
                    self.var_lifecycle.is_removed(var.index()),
                    self.var_data[var.index()].trail_pos,
                );

                // LSCB (#8442): check for lazy reimplication via lambda vector.
                // If this variable has an MLI clause that is unit at target_level,
                // reimply it at the lower assertion level instead of unassigning.
                // Reference: Coutelier et al., Algorithm 3 (SAT 2024).
                let reimplied = if self.chrono_enabled {
                    if let Some(lambda_ref) = self.lambda[var.index()] {
                        // Check if the lambda clause is still active and makes
                        // the literal unit at target_level.
                        if self.arena.is_active(lambda_ref.0 as usize) {
                            let clause_off = lambda_ref.0 as usize;
                            let clause_len = self.arena.len_of(clause_off);
                            // Compute the assertion level of the lambda clause
                            // at the current backtrack state. We need all other
                            // literals in the clause to be falsified at levels
                            // <= target_level.
                            let mut assert_level = 0u32;
                            let mut all_others_false = true;
                            for k in 0..clause_len {
                                let lk = self.arena.literal(clause_off, k);
                                if lk.variable() == var {
                                    continue; // Skip the implied literal itself
                                }
                                let lk_val = ay_prefetch::val_at(&self.vals, lk.index());
                                if lk_val >= 0 {
                                    // This literal is not falsified — clause is
                                    // not unit, cannot reimply.
                                    all_others_false = false;
                                    break;
                                }
                                let lk_level = self.var_data[lk.variable().index()].level;
                                if lk_level > target_level {
                                    // This literal will be unassigned during
                                    // this backtrack — clause won't be unit.
                                    all_others_false = false;
                                    break;
                                }
                                if lk_level > assert_level {
                                    assert_level = lk_level;
                                }
                            }
                            if all_others_false && assert_level <= target_level {
                                // Reimply: update level and reason, keep on trail.
                                let preserved_flags =
                                    self.var_data[var.index()].flags & VarData::FLAG_SEEN_PUB;
                                self.var_data[var.index()] = VarData {
                                    level: assert_level,
                                    trail_pos: write_pos as u32,
                                    reason: lambda_ref.0,
                                    flags: preserved_flags,
                                    _pad: [0; 3],
                                };
                                if is_clause_reason(lambda_ref.0) {
                                    self.mark_reason_clause(lambda_ref.0 as usize);
                                }
                                self.lambda[var.index()] = None;
                                self.stats.mli_reimplied += 1;
                                // Keep the literal on the trail at write_pos.
                                if write_pos != read_pos {
                                    self.trail[write_pos] = lit;
                                }
                                if read_pos < frontier_synced {
                                    frontier_kept += 1;
                                }
                                write_pos += 1;
                                true
                            } else {
                                false
                            }
                        } else {
                            // Lambda clause was garbage collected; clear lambda.
                            self.lambda[var.index()] = None;
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !reimplied {
                    if save_phases {
                        // CaDiCaL backtrack.cpp:14: phases.saved[idx] = sign(lit)
                        // Use trail literal polarity directly — the literal on the
                        // trail IS the assigned polarity, so a vals[] read is
                        // redundant (#3758).
                        self.phase[var.index()] = lit.sign_i8();
                    }
                    // Clear both vals entries. Use var index arithmetic directly
                    // to avoid Literal construction overhead (#3758).
                    let base = var.index() * 2;
                    ay_prefetch::val_set(&mut self.vals, base, 0);
                    ay_prefetch::val_set(&mut self.vals, base + 1, 0);
                    // Fold the unassignment out of the incremental relevancy
                    // frontier AFTER vals[] is cleared, so the variable reads as
                    // unassigned when it re-enters the frontier.
                    if read_pos < frontier_synced {
                        if let Some(frontier) = frontier.as_mut() {
                            frontier.fold_unassign(self, lit);
                        }
                    }
                    // CaDiCaL backtrack.cpp:10-30: unassign() only clears vals,
                    // pushes to VSIDS heap, and updates VMTF queue. It does NOT
                    // clear reason, trail_pos, or unit_proof_id. Stale values for
                    // unassigned variables are never read — all reads go through
                    // enqueue() which unconditionally sets fresh values.
                    // probe_parent is probe-round metadata, not trail state.
                    // probe() disables probing_mode before calling backtrack(0),
                    // and the next probe round overwrites parents for every
                    // implied literal it visits. Per-unassign clearing here is
                    // dead release-mode work in the hot loop.
                    // Clear lambda for unassigned variables.
                    self.lambda[var.index()] = None;
                    // (#8482, #8496) Removed variables can appear on the
                    // trail if a stale learned clause (not yet flushed)
                    // propagated them, or if BVE marked them eliminated
                    // without removing from trail (CaDiCaL flags.cpp:34).
                    // Skip VSIDS/VMTF reinsertion so they are never
                    // re-decided. Primary fix: flush_learned_with_eliminated_vars()
                    // in config_preprocess_bve.rs; this guard is defense-in-depth.
                    if self.var_lifecycle.is_removed(var.index()) {
                        read_pos += 1;
                        continue;
                    }
                    self.vsids.insert_into_heap(var);
                    self.vsids.vmtf_on_unassign(var);
                    // Bucket-queue reinsertion (#8476): when the bucket queue
                    // is active and this variable is in the domain, reinsert it
                    // so it is available for future decisions.
                    if self.bucket_queue_active && !self.vsids.bucket_queue_contains(var) {
                        if let Some(ref domain) = self.active_domain {
                            if var.index() < domain.len() && domain[var.index()] {
                                self.vsids.bucket_queue_insert(var);
                            }
                        }
                    }
                }
            } else {
                if write_pos != read_pos {
                    self.trail[write_pos] = lit;
                }
                self.var_data[var.index()].trail_pos = write_pos as u32;
                if read_pos < frontier_synced {
                    frontier_kept += 1;
                }
                write_pos += 1;
            }
            read_pos += 1;
        }

        if let Some(mut frontier) = frontier {
            frontier.set_synced_len(frontier_kept);
            self.relevancy_frontier = frontier;
        }
        self.trail.truncate(write_pos);
        self.trail_lim.truncate(target_level as usize);
        self.decision_level = target_level;
        if target_level == 0 {
            if lrat_root_prefix_unchanged {
                self.cold.lrat_level0_unit_materialize_cursor =
                    old_lrat_level0_unit_materialize_cursor;
                self.clamp_lrat_level0_unit_materialize_cursor(old_root_prefix_end);
            } else {
                self.cold.lrat_level0_unit_materialize_cursor = 0;
                self.cold.lrat_level0_unit_materialize_pinned.clear();
            }
        }

        // Re-propagate out-of-order literals from chrono BT compaction.
        // CaDiCaL backtrack.cpp:152-155 clips propagated/propagated2 to
        // control[new_level+1].trail (= next_level_start), which is the
        // start of the compacted out-of-order region in the trail.
        // Previously clipped to write_pos, skipping re-propagation (#6931).
        //
        // #8496: Clamp next_level_start to write_pos. When removed
        // (eliminated/substituted) variables are skipped during trail
        // compaction, write_pos may be less than the original
        // next_level_start. Without clamping, qhead could exceed
        // trail.len() after truncation, causing BCP to read stale
        // trail entries (false UNSAT in release builds).
        let next_level_start = next_level_start.min(write_pos);
        self.qhead = self.qhead.min(next_level_start);
        self.no_conflict_until = self.no_conflict_until.min(next_level_start);
        // Invalidate reason marks: multiple variables can share one reason
        // clause, so per-variable unmark_reason_clause() during backtrack is
        // unsound (it would clear marks for clauses still needed by surviving
        // trail variables). A full rebuild on the next ensure() is correct and
        // cheap since backtrack is not on the BCP hot path (#8100).
        self.invalidate_reason_clause_marks();
        self.debug_assert_backtrack_postconditions(target_level);
        // #relevancy-frontier-incremental: EXACTNESS PIN, at the one moment a
        // fold-time desync is still observable. `sync()` rebuilds from scratch
        // on any epoch move, so a query-time check alone cannot see corruption
        // an unassignment fold inflicted after a clause-DB mutation — the
        // rebuild erases it first. This runs between the fold and any rebuild.
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        if frontier_folded {
            self.debug_assert_relevancy_frontier_exact_after_fold();
        }
    }

    /// ENSURES: backtrack postconditions (TLA+ TypeInvariant mirror).
    #[inline]
    fn debug_assert_backtrack_postconditions(&self, target_level: u32) {
        debug_assert_eq!(
            self.decision_level, target_level,
            "backtrack: decision_level must equal target_level"
        );
        debug_assert_eq!(
            self.trail_lim.len(),
            target_level as usize,
            "backtrack: trail_lim.len() must equal target_level"
        );
        let trail_len = self.trail.len();
        debug_assert!(
            self.qhead <= trail_len,
            "backtrack: qhead ({}) > trail.len() ({trail_len})",
            self.qhead
        );
        debug_assert!(
            self.no_conflict_until <= trail_len,
            "backtrack: no_conflict_until ({}) > trail.len() ({trail_len})",
            self.no_conflict_until
        );
        // CaDiCaL backtrack.cpp:174: post-backtrack assigned count == trail length.
        // Sampled every 1024 conflicts: the O(num_vars) scan is too expensive to
        // run on every backtrack (caused 50x debug slowdown on schup-l2s, #4967).
        // After #3758 Phase 3, count assigned from vals[] (positive literal slots).
        #[cfg(debug_assertions)]
        if self.num_conflicts & 0x3ff == 0 {
            let assigned_count = (0..self.num_vars)
                .filter(|&v| self.vals[v * 2] != 0)
                .count();
            debug_assert_eq!(
                assigned_count, trail_len,
                "backtrack: post assigned count != trail.len()",
            );
        }
        // trail_lim monotonicity: entries must be strictly non-decreasing.
        // Violation indicates a bug in chronological backtracking or decision logic
        // that left trail_lim in an inconsistent state (#4172).
        #[cfg(debug_assertions)]
        for w in self.trail_lim.windows(2) {
            debug_assert!(
                w[0] <= w[1],
                "BUG: trail_lim not monotonic: trail_lim[..] contains {} > {}",
                w[0],
                w[1]
            );
        }
        // CaDiCaL backtrack.cpp:176: trail level bounds + active reason refs.
        #[cfg(debug_assertions)]
        {
            let check_reasons = trail_len <= 256 || self.num_conflicts & 0x3ff == 0;
            for &lit in &self.trail {
                let vi = lit.variable().index();
                let vd = self.var_data[vi];
                debug_assert!(
                    vd.level <= target_level,
                    "backtrack: trail lit {lit:?} at level {} > target {target_level}",
                    vd.level
                );
                // Skip level-0 literals: their reasons are never traversed
                // by conflict analysis (level-0 assignments are permanent root
                // causes, not derived facts). Stale reasons at level 0 are
                // benign — the assignment is correct even if the originating
                // clause was garbage-collected. The root cause (GC reclaiming
                // JIT-compiled reasons) is tracked in #8397.
                if check_reasons
                    && is_clause_reason(vd.reason)
                    && !vd.is_lazy_theory_reason()
                    && vd.level > 0
                {
                    let r = ClauseRef(vd.reason);
                    debug_assert!(
                        self.arena.is_active(r.0 as usize),
                        "BUG: trail lit {lit:?} has stale reason ClauseRef({}) at level {} \
                         target_level={target_level} conflicts={} — \
                         JIT stale-reason safety net in batch_enqueue_from_jit should have \
                         prevented this (#8397)",
                        r.0,
                        vd.level,
                        self.num_conflicts,
                    );
                }
            }
        }
    }
}
