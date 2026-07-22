// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::kani_compat::det_hash_set_with_capacity;

impl Solver {
    pub(super) fn finalize_conflict_analysis(
        &mut self,
        uip: Literal,
        mut lrat_level0_vars: Vec<usize>,
    ) -> ConflictResult {
        self.conflict.set_asserting_literal(uip);
        self.update_bumpreason_decision_rate();

        // Compute LBD from the levels already tracked during analysis
        // (CaDiCaL analyze.cpp:1193: glue = levels.size() - 1).
        // level_seen_to_clear contains ALL distinct non-zero levels encountered
        // during 1UIP resolution. CaDiCaL subtracts 1 to exclude the conflict
        // level (which is always present). This is O(1) vs the O(clause_size)
        // compute_lbd() which re-iterates the learned clause (#8569).
        let lbd = (self.min.level_seen_to_clear.len() as u32).saturating_sub(1);
        let pre_min_clause_size = self.conflict.learned_count() + 1;
        let learned_count = pre_min_clause_size.saturating_sub(1);
        debug_assert!(
            (lbd as usize) < pre_min_clause_size || pre_min_clause_size <= 1,
            "BUG: LBD ({lbd}) >= pre-minimization clause size ({pre_min_clause_size}) — CaDiCaL invariant: glue < size",
        );

        // Snapshot the direct 1UIP resolution chain before LRAT-only proof
        // augmentation. Minimize chains and level-0 unit chains are valid LRAT
        // hints, but they are not the conflict-resolution skeleton from which
        // McMillan IBCL extracts pivots (#8269).
        let ibcl_core_chain_len = if self.cold.lrat_enabled {
            self.conflict.resolution_chain_len()
        } else {
            0
        };

        // If shrink mode can only see singleton non-UIP levels, it will keep
        // the clause unchanged. Check this before the LRAT snapshot so that
        // proof mode does not copy a clause whose minimize-chain is impossible.
        //
        // Fold (#8790): the repeated-non-UIP-level bit is derived incrementally
        // by track_level_seen during the 1UIP loop, replacing the O(clause_len)
        // learned_clause_has_repeated_non_uip_level prescan. When analysis
        // started with dirty level_seen counters (rare ghost-drop bailout skips
        // clear_level_seen), the incremental bit is unreliable and we fall back
        // to the exact prescan.
        let shrink_has_repeated_non_uip_level = self.shrink_enabled
            && pre_min_clause_size > 2
            && if self.min.level_seen_flag_valid {
                let repeated = self.min.level_seen_repeated_non_uip;
                #[cfg(debug_assertions)]
                {
                    let prescan = self.learned_clause_has_repeated_non_uip_level(learned_count);
                    debug_assert_eq!(
                        prescan, repeated,
                        "BUG(#8790): incremental repeated-non-UIP-level bit diverges \
                         from learned_clause_has_repeated_non_uip_level prescan",
                    );
                }
                repeated
            } else {
                self.learned_clause_has_repeated_non_uip_level(learned_count)
            };
        let shrink_singleton_fast_path =
            self.shrink_enabled && pre_min_clause_size > 2 && !shrink_has_repeated_non_uip_level;
        if shrink_singleton_fast_path {
            self.stats.shrink_singleton_fast_path_skips += 1;
            if self.cold.lrat_enabled {
                self.stats.lrat_original_learned_snapshot_singleton_skips += 1;
            }
        }

        // Collect literals actually removed by shrink/minimize for LRAT chain
        // computation. Unit/binary learned clauses skip minimization below, so
        // no literals can be removed and the removed-literal chain is empty.
        // In shrink mode, all-singleton non-UIP levels also skip all shrink and
        // minimize work, so no removed-literal LRAT chain can exist.
        let mut removed_learned_buf: Option<Vec<Literal>> = if self
            .should_snapshot_lrat_original_learned(
                pre_min_clause_size,
                shrink_has_repeated_non_uip_level,
            ) {
            let mut removed_learned = std::mem::take(&mut self.min.lrat_original_learned_buf);
            removed_learned.clear();
            Some(removed_learned)
        } else {
            None
        };

        // CaDiCaL analyze.cpp:1211: skip minimization for unit clauses (size <= 1).
        // For binary clauses (size == 2), minimization can only remove the single
        // non-UIP literal, which would make it a unit — skip to save the overhead
        // of sorting, flag setup, and recursive redundancy checking (#8569).
        if pre_min_clause_size > 2 {
            if self.shrink_enabled {
                if shrink_has_repeated_non_uip_level {
                    self.shrink_and_minimize_repeated_level_learned_clause_collect_removed(
                        learned_count,
                        removed_learned_buf.as_mut(),
                    );
                }
            } else {
                self.minimize_learned_clause_collect_removed(removed_learned_buf.as_mut());
            }
        }

        self.clear_level_seen();
        self.bump_reason_literals();
        self.bump_analyzed_variables();

        // Forward LRAT chain computation: add reason chains for literals
        // removed during minimization and level-0 unit proof IDs.
        // CaDiCaL: calculate_minimize_chain() in minimize.cpp:155-199,
        // then unit_chain in analyze.cpp:1240-1246.
        if let Some(removed_learned) = removed_learned_buf.as_deref() {
            if !removed_learned.is_empty() {
                self.stats.lrat_original_learned_snapshot_copies += 1;
                self.stats.lrat_original_learned_snapshot_literals += removed_learned.len() as u64;
                let minimize_level0 = self.compute_lrat_chain_for_removed_literals(removed_learned);
                lrat_level0_vars.extend(minimize_level0);
            }
        }
        if let Some(mut removed_learned) = removed_learned_buf.take() {
            removed_learned.clear();
            self.min.lrat_original_learned_buf = removed_learned;
        }

        if self.cold.lrat_enabled && !lrat_level0_vars.is_empty() {
            self.materialize_level0_unit_proofs();
            let mut rup_satisfied = det_hash_set_with_capacity(1 + self.conflict.learned_count());
            rup_satisfied.insert(uip.negated());
            for i in 0..self.conflict.learned_count() {
                rup_satisfied.insert(self.conflict.learned_at(i).negated());
            }
            self.append_lrat_unit_chain(&lrat_level0_vars, &rup_satisfied);
        }
        // Return the LRAT level-0 vars buffer to cold state for reuse (#8603).
        lrat_level0_vars.clear();
        self.cold.lrat_level0_vars_buf = lrat_level0_vars;

        // IBCL pass (#8269): interpolation-based clause learning.
        //
        // When LRAT proof mode is active, we have the core resolution chain:
        // clause IDs plus per-step pivot literals for reason clauses. A full
        // IBCL implementation would compute a Craig interpolant from this
        // proof, potentially yielding a shorter auxiliary learned constraint.
        //
        // Current status: stats-only infrastructure. The full interpolation
        // engine requires:
        // 1. A resolution proof DAG (the core chain is now pivot-annotated,
        //    but still linear and excludes minimization/unit-chain LRAT hints)
        // 2. A partition of variables into A-local, B-local, and shared sets
        //    — the natural partition uses decision level: variables decided
        //    before vs after the conflict as the A/B split
        // 3. An interpolation algorithm (McMillan 2003, Pudlak 1997, or
        //    Huang 2010 for size-optimal interpolants)
        //
        // For now, we record when the IBCL pass would attempt interpolation,
        // when the resolution chain is too short to benefit, and when proof
        // skeleton metadata is still insufficient. This data informs whether
        // investing in the full proof DAG is worthwhile.
        if self.cold.lrat_enabled && !self.should_prune_conflict_analysis_experiments() {
            let chain_len = ibcl_core_chain_len;
            let clause_size = self.conflict.learned_count() + 1; // +1 for UIP
            if chain_len < 3 || clause_size <= 2 {
                // Resolution chains shorter than 3 steps produce interpolants
                // that are at best equal to the 1UIP clause. Unit or binary
                // learned clauses are already minimal.
                self.stats.ibcl_skipped_short_chain += 1;
            } else if !self.conflict.resolution_chain_prefix_has_pivots(chain_len) {
                // Future extraction must fail closed unless every direct 1UIP
                // reason step has both a non-zero clause ID and a pivot literal.
                self.stats.ibcl_skipped_missing_pivots += 1;
            } else {
                self.stats.ibcl_attempts += 1;
                // Future: compute interpolant here and compare size.
                // if interpolant_clause.len() < clause_size {
                //     self.stats.ibcl_improvements += 1;
                //     // Replace learned clause with interpolant
                // }
            }
        }

        // Fold (#8790): compute the backtrack level and the reorder-for-watches
        // swap source in one pass (or O(1) from 1UIP-loop tracking when the
        // learned clause was untouched by shrink/minimize), replacing the
        // compute_backtrack_level rescan plus the reorder_for_watches scan.
        let (backtrack_level, swap_learned_idx) =
            self.conflict.backtrack_level_and_watch_swap(&self.var_data);
        debug_assert_eq!(
            backtrack_level,
            self.conflict.compute_backtrack_level(&self.var_data),
            "BUG(#8790): fused backtrack level diverges from compute_backtrack_level",
        );
        let mut result = self.conflict.get_result(backtrack_level, lbd);

        #[cfg(debug_assertions)]
        let reorder_reference = {
            let mut reference = result.learned_clause.clone();
            crate::conflict::reorder_for_watches(&mut reference, &self.var_data, backtrack_level);
            reference
        };
        if swap_learned_idx != usize::MAX {
            // Learned index j maps to clause index j + 1 after the UIP
            // prepend; this is the exact swap reorder_for_watches performed.
            result.learned_clause.swap(1, swap_learned_idx + 1);
        }
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            result.learned_clause, reorder_reference,
            "BUG(#8790): fused watch swap diverges from reorder_for_watches",
        );

        self.debug_assert_learned_clause_invariants(uip, backtrack_level, &result.learned_clause);
        result
    }

    #[inline(always)]
    pub(super) fn should_snapshot_lrat_original_learned(
        &self,
        pre_min_clause_size: usize,
        shrink_has_repeated_non_uip_level: bool,
    ) -> bool {
        self.cold.lrat_enabled
            && pre_min_clause_size > 2
            && (!self.shrink_enabled || shrink_has_repeated_non_uip_level)
    }
}
