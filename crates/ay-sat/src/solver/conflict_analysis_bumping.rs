// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-analysis variable bumping for VSIDS/VMTF activity management.
//!
//! Separated from the 1UIP analysis loop to keep the hot conflict-analysis
//! path focused on resolution, while activity updates write to VSIDS/VMTF
//! data structures in a separate cache-friendly pass.

use super::*;
use crate::literal::{Literal, Variable};

/// Optional override for reason-side bump recursion depth, read once from
/// `AY_BUMPREASON_DEPTH` (#678 branching A/B). `None` = CaDiCaL default
/// (2 stable / 1 focused); `Some(0)` = disable reason-side bumping entirely
/// (Kissat-like analyzed-only bump); `Some(d)` = cap depth at `d`.
fn bumpreason_depth_override() -> Option<u32> {
    use std::sync::OnceLock;
    static OVERRIDE: OnceLock<Option<u32>> = OnceLock::new();
    *OVERRIDE.get_or_init(|| {
        std::env::var("AY_BUMPREASON_DEPTH")
            .ok()
            .and_then(|s| s.trim().parse::<u32>().ok())
    })
}

impl Solver {
    /// Update the EMA of decisions-per-conflict for bumpreason rate limiting.
    /// CaDiCaL analyze.cpp:924-929: tracks how many decisions occurred between
    /// consecutive conflicts. High decision rates mean the solver is exploring
    /// widely, and reason bumping adds VSIDS noise rather than focus.
    pub(super) fn update_bumpreason_decision_rate(&mut self) {
        let decisions_this_conflict = self
            .num_decisions
            .saturating_sub(self.cold.bumpreason_saved_decisions);
        self.cold.bumpreason_saved_decisions = self.num_decisions;
        // EMA with alpha = 2/(1e5+1) = 0.00002, matching CaDiCaL emadecisions=1e5.
        const ALPHA: f64 = 2.0 / 100_001.0;
        self.cold.bumpreason_decision_rate +=
            ALPHA * (decisions_this_conflict as f64 - self.cold.bumpreason_decision_rate);
    }

    /// Bump all analyzed variables after the analysis loop.
    ///
    /// Deferring bumps from the analysis loop to a separate pass improves
    /// cache behavior: the analysis loop reads trail/reason data, while
    /// bumping writes to VSIDS/VMTF data structures. Separating these
    /// avoids cache pollution during the latency-sensitive analysis loop.
    ///
    /// CHB score updates are only performed when the MAB selector is active
    /// (`MabUcb1`) or CHB is the fixed heuristic. In `LegacyCoupled` mode
    /// (EVSIDS+VMTF only, the default for single-thread search), CHB
    /// updates are skipped entirely to eliminate per-conflict floating-point
    /// overhead and L1 cache pollution from scattered `chb_scores` writes.
    pub(super) fn bump_analyzed_variables(&mut self) {
        let analyzed = self.conflict.analyzed_vars();

        // CHB score updates: only when the active route can consult CHB.
        // Main/LRAT MAB is stable-mode-only; focused mode keeps legacy VMTF
        // branching and must not pay CHB floating-point/bookkeeping cost on
        // every conflict.
        let chb_active = matches!(
            self.cold.branch_selector_mode,
            BranchSelectorMode::MabUcb1 if self.stable_mode
        ) || matches!(
            self.cold.branch_selector_mode,
            BranchSelectorMode::Fixed(BranchHeuristic::Chb)
        );
        if chb_active {
            self.vsids.chb_bump_batch(analyzed);
            self.vsids.chb_on_conflict();
        }

        match self.active_branch_heuristic {
            BranchHeuristic::Evsids => {
                // Batch bump: increments all activities in one pass, then
                // restores the heap with Floyd's O(n) heapify for large
                // batches instead of k individual O(log n) sift-ups (#8350).
                self.vsids.batch_bump(analyzed, &self.vals, true);
            }
            BranchHeuristic::Chb => {
                // CHB is active and the heap already orders by CHB scores
                // (swapped into activities). Keep dormant EVSIDS scores warm
                // so MAB switching does not start from stale data.
                //
                // Also maintain VMTF bump_order so arena compaction and
                // mode-switch rebuilds use current ordering. CHB is only
                // active in stable mode (MabUcb1 gate), so the deferred
                // VMTF path applies: bump_order updates are O(1) writes
                // without linked-list manipulation.
                self.vsids.bump_evsids_score_dormant_batch(analyzed);
                for &idx in analyzed {
                    self.vsids
                        .bump_vmtf_order_only(Variable(idx as u32), &self.vals);
                }
            }
            BranchHeuristic::Vmtf => {
                // VMTF mode: sort by bump_order first so variables are
                // inserted into the VMTF queue in correct recency order
                // (CaDiCaL analyze.cpp:189-194), then bump each variable in
                // that order. The sorted pair buffer is consumed directly;
                // the former copy into a plain index buffer was pure overhead
                // (instruction-shave #4). bump_order values are unique
                // (monotone counter), so the sorted order is total and the
                // resulting queue order is unchanged.
                self.bump_order_sort_buf.clear();
                self.bump_order_sort_buf.extend(
                    analyzed
                        .iter()
                        .map(|&idx| (self.vsids.bump_order(Variable(idx as u32)), idx)),
                );
                self.bump_order_sort_buf
                    .sort_unstable_by_key(|&(order, _)| order);
                self.vsids
                    .batch_bump_queue_sorted(&self.bump_order_sort_buf, &self.vals);
            }
        }
    }

    /// Bump reason literals for improved VSIDS focus (CaDiCaL's bumpreason).
    ///
    /// This bumps variables in the reason clauses of the literals in the learned
    /// clause. The intuition is that these variables are "important" because they
    /// contributed to the conflict, even if they're not directly in the learned clause.
    ///
    /// Gated by CaDiCaL's adaptive rate-limiting (analyze.cpp:384-424):
    /// 1. Decision rate guard: skip if decisions/conflict EMA > 100
    /// 2. Adaptive delay: when bumping wastes work, delay re-enabling
    ///
    /// Parameters (from CaDiCaL):
    /// - Depth limit: 1 (focused) or 2 (stable) - how deep to recurse into reasons
    /// - Analyzed limit: 10x the number of analyzed literals - prevent blowup
    pub(super) fn bump_reason_literals(&mut self) {
        // AY_BUMPREASON_DEPTH=0 disables reason-side bumping entirely (matching
        // Kissat's analyzed-only bump). On gate-heavy formulas CaDiCaL-style reason
        // bumping inflates gate-internal/auxiliary variable activity and flattens
        // the EVSIDS order; this env toggle makes the effect A/B-measurable (#678).
        if bumpreason_depth_override() == Some(0) {
            return;
        }
        // CaDiCaL analyze.cpp:388: rate limit -- skip when decision rate is too high.
        // bumpreasonrate default = 100 (options.hpp:42).
        const BUMPREASON_RATE_LIMIT: f64 = 100.0;
        if self.cold.bumpreason_decision_rate > BUMPREASON_RATE_LIMIT {
            return;
        }

        // CaDiCaL analyze.cpp:393-398: adaptive delay -- skip while delay counter > 0.
        // Per-mode indexing matches CaDiCaL's delay[stable].bumpreasons.
        let mode = usize::from(self.stable_mode);
        if self.cold.bumpreason_delay_remaining[mode] > 0 {
            self.cold.bumpreason_delay_remaining[mode] -= 1;
            return;
        }

        // Get literals in the learned clause (including UIP)
        let uip = self.conflict.asserting_literal();
        // Use index-based access to avoid allocation from to_vec()
        let learned_count = self.conflict.learned_count();

        // CaDiCaL analyze.cpp:399-400: depth limit must be positive.
        // CaDiCaL: bumpreasondepth(1) + stable -> 1 (focused), 2 (stable).
        let depth_limit =
            bumpreason_depth_override().unwrap_or(if self.stable_mode { 2 } else { 1 });
        debug_assert!(depth_limit > 0, "BUG: bump reason depth limit is 0");

        // CaDiCaL analyze.cpp:401-402: save analyzed size before reason bumping.
        // Reason-side variables are added to the analyzed list (seen_to_clear) via
        // mark_seen(), then bumped together with all other analyzed variables in
        // bump_analyzed_variables(). We do NOT bump VSIDS directly here -- that
        // would cause double-bumping since bump_analyzed_variables iterates the
        // same seen_to_clear list.
        let saved_analyzed = self.conflict.analyzed_vars().len();
        let analyzed_limit = saved_analyzed * 10;
        let mut extra_added = 0;

        // Add reason-side variables for UIP first
        self.add_reason_literals_to_analyzed(
            uip.negated(),
            depth_limit,
            &mut extra_added,
            analyzed_limit,
        );

        // Add reason literals for each literal in the learned clause
        for i in 0..learned_count {
            if extra_added >= analyzed_limit {
                break;
            }
            let lit = self.conflict.learned_at(i);
            self.add_reason_literals_to_analyzed(
                lit.negated(),
                depth_limit,
                &mut extra_added,
                analyzed_limit,
            );
        }

        // CaDiCaL analyze.cpp:408-423: adaptive delay hysteresis + rollback.
        let limit_exceeded = extra_added >= analyzed_limit;
        if limit_exceeded {
            // Rollback: clear seen flags for all reason-side variables added
            // and truncate the analyzed list back to its saved size.
            // CaDiCaL analyze.cpp:410-417: clears f.seen and resizes analyzed.
            self.conflict
                .rollback_analyzed(saved_analyzed, &mut self.var_data);
            self.cold.bumpreason_delay_interval[mode] += 1;
        } else {
            self.cold.bumpreason_delay_interval[mode] /= 2;
        }
        self.cold.bumpreason_delay_remaining[mode] = self.cold.bumpreason_delay_interval[mode];
    }

    /// Add reason-side literals to the analyzed set for later bumping.
    ///
    /// CaDiCaL analyze.cpp:342-381 (bump_also_reason_literal + bump_also_reason_literals).
    /// Variables are marked as seen (added to analyzed_vars) but NOT bumped directly.
    /// The actual VSIDS/VMTF bump happens in bump_analyzed_variables() which processes
    /// the full analyzed list with correct sort ordering.
    pub(super) fn add_reason_literals_to_analyzed(
        &mut self,
        lit: Literal,
        depth: u32,
        extra_added: &mut usize,
        limit: usize,
    ) {
        if depth == 0 || *extra_added >= limit {
            return;
        }

        let var_idx = lit.variable().index();

        // Guard (#8434): after chrono-BT, reason clause literals from levels
        // above the backtrack point may be unassigned. Bumping unassigned
        // variables is harmless but their stale reason pointers could reference
        // deleted clauses. Skip them.
        if !self.var_is_assigned(var_idx) {
            return;
        }

        // Get the reason clause for this literal
        let Some(reason_ref) = self.var_reason(var_idx) else {
            return; // Decision or unit - no reason clause
        };

        // Traverse reason clause and add unseen variables to analyzed list
        let clause_idx = reason_ref.0 as usize;

        // CaDiCaL analyze.cpp:370: charge one search tick per reason clause traversal
        self.search_ticks[usize::from(self.stable_mode)] += 1;

        if depth == 1 {
            // Leaf traversal (instruction-shave #4): no recursion can occur,
            // so the loop body only touches vals/var_data/conflict and the
            // reason clause can be walked as a slice (one bounds check per
            // clause instead of one per literal; CaDiCaL's pointer walk over
            // `*reason`). Disjoint field borrows make this safe without any
            // borrow-conflict copy. Semantics are identical to the general
            // loop below with `depth > 1` statically false — note the marking
            // itself is NOT limit-gated (matching CaDiCaL, which never breaks
            // mid-clause on the analyzed limit at depth 1).
            let Self {
                ref arena,
                ref mut conflict,
                ref mut var_data,
                ref vals,
                ..
            } = *self;
            for &reason_lit in arena.literals(clause_idx) {
                if reason_lit == lit {
                    continue; // Skip the propagated literal itself
                }

                // Guard (#8434): skip unassigned ghost literals (see below).
                // CaDiCaL analyze.cpp:344: reason literal must be assigned
                // false; the guard subsumes the debug assertion.
                if ay_prefetch::val_at(vals, reason_lit.index()) >= 0 {
                    continue;
                }

                let reason_var_idx = reason_lit.variable().index();

                // CaDiCaL analyze.cpp:346-351: skip if already seen or level 0.
                // Single 16-byte VarData load for both tests (#6994 layout).
                let vd = var_data[reason_var_idx];
                if vd.is_seen() || vd.level == 0 {
                    continue;
                }

                // Mark as seen -- adds to analyzed_vars (seen_to_clear) for
                // later bumping in bump_analyzed_variables().
                conflict.mark_seen(reason_var_idx, var_data);
                *extra_added += 1;
            }
            return;
        }

        let clause_len = self.arena.len_of(clause_idx);
        for i in 0..clause_len {
            let reason_lit = self.arena.literal(clause_idx, i);
            if reason_lit == lit {
                continue; // Skip the propagated literal itself
            }

            // Guard (#8434): skip unassigned ghost literals in reason clauses
            // after chrono-BT find_conflict_level backtrack. Stale var_data.level
            // and reason pointers for these literals could cause incorrect bumping
            // or recursion into deleted clauses.
            if self.lit_val(reason_lit) >= 0 {
                continue;
            }

            let reason_var_idx = reason_lit.variable().index();

            // CaDiCaL analyze.cpp:346-351: skip if already seen or level 0.
            // Single VarData load for both tests (#6994 layout).
            let vd = self.var_data[reason_var_idx];
            if vd.is_seen() || vd.level == 0 {
                continue;
            }

            // Mark as seen -- adds to analyzed_vars (seen_to_clear) for later
            // bumping in bump_analyzed_variables(). No direct VSIDS bump here.
            self.conflict.mark_seen(reason_var_idx, &mut self.var_data);
            *extra_added += 1;

            // Recurse if we have depth remaining
            if *extra_added < limit {
                self.add_reason_literals_to_analyzed(
                    reason_lit.negated(),
                    depth - 1,
                    extra_added,
                    limit,
                );
            }
        }
    }
}
