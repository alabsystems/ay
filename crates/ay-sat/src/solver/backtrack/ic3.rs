// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The IC3 backtrack lane.
//!
//! `backtrack_core` (the parent) is the general path: phase saving, chrono
//! backtracking, LSCB lambda reimplication. IC3 needs none of that — it uses
//! FORCED phases and runs with chrono disabled — so it has its own lane rather
//! than paying for branches that are statically dead in that mode. That is the
//! whole boundary this file draws: same job, IC3's assumptions baked in.
//!
//! Visibility note: `backtrack_ic3` is `pub(in crate::solver)` because it is
//! driven from `solve::ic3`, `solve::analyze` and `preprocess_reset` — the same
//! reach it had as `pub(super)` when it lived in the parent module.

use super::*;
use crate::solver::relevancy_frontier::RelevancyFrontier;

impl Solver {
    /// IC3-optimized backtrack (#8569): stripped-down backtrack for IC3 mode.
    ///
    /// Compared to the standard `backtrack()`, this version skips:
    /// - Target/best phase updates (IC3 uses forced phases via set_phase;
    ///   target/best phases are never consumed by pick_phase)
    /// - Phase saving per variable (IC3 uses forced phases)
    /// - LSCB lambda reimplication (chrono is disabled in IC3 mode)
    /// - VMTF on-unassign updates (IC3 uses VSIDS/bucket queue only)
    ///
    /// Keeps: vals[] clearing, VSIDS heap reinsertion, bucket queue
    /// reinsertion for domain variables, trail compaction, reason mark
    /// invalidation, postcondition checks.
    ///
    /// REQUIRES: ic3_mode is set, chrono_enabled is false
    /// ENSURES: same postconditions as backtrack()
    pub(in crate::solver) fn backtrack_ic3(&mut self, target_level: u32) {
        self.debug_assert_ic3_backtrack_preconditions(target_level);

        // No target/best phase updates: IC3 uses forced phases.

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
        debug_assert!(
            assigned_limit <= self.trail.len(),
            "BUG: assigned_limit ({assigned_limit}) > trail.len() ({})",
            self.trail.len(),
        );

        let next_level_start = self.trail_lim[target_level as usize];
        let write_pos = self.compact_trail_ic3(
            target_level,
            assigned_limit,
            frontier_synced,
            &mut frontier,
            &mut frontier_kept,
        );

        if let Some(mut frontier) = frontier {
            frontier.set_synced_len(frontier_kept);
            self.relevancy_frontier = frontier;
        }
        self.trail.truncate(write_pos);
        self.trail_lim.truncate(target_level as usize);
        self.decision_level = target_level;

        let next_level_start = next_level_start.min(write_pos);
        self.qhead = self.qhead.min(next_level_start);
        self.no_conflict_until = self.no_conflict_until.min(next_level_start);
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

    /// Compact the trail in place, unassigning everything above
    /// `target_level` and keeping the survivors in order.
    ///
    /// Extracted from [`Solver::backtrack_ic3`] because it is the only part of
    /// that function which walks PER LITERAL: the caller decides the levels and
    /// owns the frontier fold's lifetime, this does the O(trail) work. Returns
    /// the new trail length, and reports through `frontier_kept` how many of
    /// the frontier's folded prefix survived — compaction preserves trail
    /// order, so the survivors ARE the new folded prefix.
    ///
    /// `frontier` is threaded as a parameter rather than read back off `self`
    /// because the caller has already `mem::take`n it out, which is exactly
    /// what lets `fold_unassign` borrow `self` immutably while the trail is
    /// being mutated.
    fn compact_trail_ic3(
        &mut self,
        target_level: u32,
        assigned_limit: usize,
        frontier_synced: usize,
        frontier: &mut Option<RelevancyFrontier>,
        frontier_kept: &mut usize,
    ) -> usize {
        let mut write_pos = assigned_limit;
        let mut read_pos = assigned_limit;

        while read_pos < self.trail.len() {
            let lit = self.trail[read_pos];
            let var = lit.variable();
            let var_level = self.var_data[var.index()].level;

            if var_level > target_level {
                // No phase saving: IC3 uses forced phases.
                // No LSCB lambda reimplication: chrono disabled.

                // Clear vals[].
                let base = var.index() * 2;
                ay_prefetch::val_set(&mut self.vals, base, 0);
                ay_prefetch::val_set(&mut self.vals, base + 1, 0);
                // See `backtrack_core`: fold the unassignment out of the
                // incremental relevancy frontier once vals[] reads unassigned.
                if read_pos < frontier_synced {
                    if let Some(frontier) = frontier.as_mut() {
                        frontier.fold_unassign(self, lit);
                    }
                }
                // Clear lambda (defense-in-depth; always None when chrono off).
                self.lambda[var.index()] = None;

                if self.var_lifecycle.is_removed(var.index()) {
                    read_pos += 1;
                    continue;
                }

                // VSIDS heap reinsertion (needed for decision making).
                self.vsids.insert_into_heap(var);
                // No vmtf_on_unassign: IC3 uses VSIDS/bucket queue only.

                // Bucket-queue reinsertion for domain variables (#8476).
                if self.bucket_queue_active && !self.vsids.bucket_queue_contains(var) {
                    if let Some(ref domain) = self.active_domain {
                        if var.index() < domain.len() && domain[var.index()] {
                            self.vsids.bucket_queue_insert(var);
                        }
                    }
                }
            } else {
                if write_pos != read_pos {
                    self.trail[write_pos] = lit;
                }
                self.var_data[var.index()].trail_pos = write_pos as u32;
                if read_pos < frontier_synced {
                    *frontier_kept += 1;
                }
                write_pos += 1;
            }
            read_pos += 1;
        }
        write_pos
    }

    /// REQUIRES, for [`Solver::backtrack_ic3`]: IC3 mode is on, chrono is off,
    /// and the target level is reachable. Split out so the lane's entry point
    /// reads as the algorithm rather than as its contract; all three are the
    /// assumptions that let this lane skip phase saving and reimplication.
    #[inline]
    fn debug_assert_ic3_backtrack_preconditions(&self, target_level: u32) {
        debug_assert!(
            self.cold.ic3_mode,
            "BUG: backtrack_ic3 called without ic3_mode"
        );
        debug_assert!(
            !self.chrono_enabled,
            "BUG: backtrack_ic3 called with chrono_enabled"
        );
        debug_assert!(
            target_level <= self.decision_level,
            "BUG: backtrack_ic3 to level {target_level} > decision_level {}",
            self.decision_level
        );
    }
}
