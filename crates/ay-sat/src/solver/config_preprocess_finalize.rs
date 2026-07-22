// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::mutate::ReasonPolicy;
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
                deleted_any = true;
                if is_pending_garbage {
                    // Pending-garbage: force-delete by zeroing lit_len.
                    // The clause is already logically dead; we just need to
                    // ensure BCP cannot traverse it via stale watch entries.
                    self.stats.clear_bcp_learned_1963_blocker_cert(idx);
                    self.arena.delete(idx);
                } else {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        deleted_any
    }
}
