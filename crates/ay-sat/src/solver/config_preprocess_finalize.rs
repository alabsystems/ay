// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::mutate::{DeleteResult, ReasonPolicy};
use super::*;

impl Solver {
    #[allow(clippy::too_many_arguments, unused_variables)]
    pub(super) fn emit_preprocess_summary(
        &self,
        preprocess_start: ay_core::time::Instant,
        t1_cong: u128,
        t2_bb: u128,
        t3_decomp: u128,
        t4_factor: u128,
        t5_bve: u128,
        t6_probe: u128,
    ) {
        #[cfg(ay_logging)]
        {
            let fixed = self.count_fixed_vars();
            let eliminated = self.inproc.bve.stats().vars_eliminated;
            let substituted = self.decompose_stats().substituted;
            let factored = self.cold.factor_factored_total;
            let active = self.num_vars - fixed - self.var_lifecycle.count_removed();
            let clauses = self.arena.active_clause_count();
            let preprocess_ms = preprocess_start.elapsed().as_millis();
            eprintln!(
                "c preprocess: fixed={fixed} eliminated={eliminated} \
                 substituted={substituted} factored={factored} \
                 active={active} clauses={clauses} time={preprocess_ms}ms \
                 [cong={t1_cong} bb={t2_bb} decomp={t3_decomp} factor={t4_factor} bve={t5_bve} probe={t6_probe}]"
            );
        }
    }

    /// Remove all active clauses that reference eliminated or substituted
    /// variables (#7083, #8496).
    ///
    /// Called from `solve_no_assumptions` after `preprocess()` returns, to
    /// ensure cleanup runs regardless of how preprocessing exited (normal
    /// completion, timeout, or interrupt). Also called at the end of
    /// `preprocess()` itself for the normal-completion path.
    ///
    /// Skips dead clauses (garbage-bit or pending-garbage) since they are
    /// already logically deleted and will be reclaimed by arena compaction.
    /// Returns `true` if any clauses were deleted during cleanup.
    /// The caller should force a full watch rebuild when this returns true,
    /// because `arena.delete()` on pending-garbage clauses does not remove
    /// their stale watch entries (#8496).
    pub(super) fn finalize_preprocess_clause_cleanup(&mut self) -> bool {
        // Skip the O(clauses * avg_len) scan when no variables were removed.
        // This happens on large dense formulas where BVE and decompose are
        // both skipped (#8136). On shuffling-2 (4.7M clauses), this avoids
        // ~200ms of pointless iteration.
        let removed_count = self.var_lifecycle.count_removed();
        if removed_count == 0 {
            return false;
        }
        self.defer_stale_reason_cleanup = true;
        // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
        self.cold.reduce_indices_buf.clear();
        self.cold.reduce_indices_buf.extend(self.arena.indices());
        let mut deleted_any = false;
        for i in 0..self.cold.reduce_indices_buf.len() {
            let idx = self.cold.reduce_indices_buf[i];
            let len = self.arena.len_of(idx);
            if len == 0 {
                // Fully deleted (lit_len zeroed) — skip.
                continue;
            }
            // #8496: Check BOTH active and pending-garbage clauses.
            // Pending-garbage clauses (PENDING_GARBAGE_BIT set) have non-zero
            // lit_len and retain their watch entries. If such a clause contains
            // an eliminated variable, BCP will propagate through it during
            // CDCL search, causing eliminated variables to appear on the trail
            // at decision levels > 0 (false UNSAT in release builds).
            // For pending-garbage clauses, call arena.delete() directly to
            // zero lit_len and set GARBAGE_BIT, preventing BCP from seeing them.
            // For active clauses, use the full delete_clause_checked path.
            let is_pending_garbage = self.arena.is_dead(idx) && len > 0;
            let has_removed = self
                .arena
                .literals(idx)
                .iter()
                .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
            if has_removed {
                if is_pending_garbage {
                    // Pending-garbage: force-delete by zeroing lit_len.
                    // The clause is already logically dead; we just need to
                    // ensure BCP cannot traverse it via stale watch entries.
                    self.stats.clear_bcp_learned_1963_blocker_cert(idx);
                    self.arena.delete(idx);
                    deleted_any = true;
                } else {
                    // This is mandatory correctness cleanup, not an optional
                    // inprocessing mutation. Start in stop-immune mode so LRAT
                    // unit materialization cannot partially advance and then
                    // leave an active clause containing a removed variable.
                    let result =
                        self.delete_clause_checked_required_cleanup(idx, ReasonPolicy::ClearLevel0);
                    assert_eq!(
                        result,
                        DeleteResult::Deleted,
                        "BUG: mandatory preprocessing cleanup retained active clause {idx} containing a removed variable",
                    );
                    assert!(
                        !self.arena.is_active(idx),
                        "BUG: mandatory preprocessing cleanup reported deletion but clause {idx} remains active",
                    );
                    deleted_any = true;
                }
            }
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        deleted_any
    }

    /// Restore a search-safe clause/watch state after initial preprocessing.
    ///
    /// This is deliberately unconditional with respect to the preprocessing
    /// outcome. A cooperative stop can arrive after a destructive pass, so an
    /// `Unknown` caller must perform the same dead-clause purge, watch rebuild,
    /// root re-propagation, and one-shot disarm as a completed phase. Returns
    /// whether cleanup propagation discovered a level-0 conflict.
    pub(super) fn finish_initial_preprocessing(&mut self) -> bool {
        if self.finalize_preprocess_clause_cleanup() {
            self.cold.preprocess_watches_valid = false;
        }
        if !self.cold.preprocess_watches_valid {
            self.watches.clear();
            self.initialize_watches();
        }

        // Every current root assignment must be reconsidered against the
        // rebuilt clause database, including units added by a partial pass.
        self.qhead = 0;
        let trail_before = self.trail.len();
        let conflict = if self.has_empty_clause {
            // Preprocessing may already have recorded the terminal conflict.
            // BCP requires `has_empty_clause == false`; there is nothing left
            // to propagate once the empty clause is known.
            self.qhead = self.trail.len();
            true
        } else if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            true
        } else {
            if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
                self.tla_trace_step(
                    CdclTraceState::Propagating,
                    Some(CdclTraceAction::Propagate),
                );
            }
            false
        };

        self.cold.preprocess_enabled = false;
        self.num_original_clauses = self.arena.active_clause_count();
        conflict
    }
}
