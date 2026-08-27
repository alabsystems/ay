// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause database reduction and activity management.

use super::*;

// Clause deletion scoring removed in favor of CaDiCaL's pure (glue, size)
// comparator (#5132). Activity plays no role in deletion decisions -- only LBD
// and clause size determine usefulness, per Audemard & Simon (IJCAI'09).
// Reference: CaDiCaL reduce.cpp:74-82 `reduce_less_useful`.

/// Effective small-formula reduce-interval cap multiplier for non-dense
/// small formulas (#8135 follow-up).
///
/// Defaults to `SMALL_FORMULA_REDUCE_CAP_MULT`. The A/B knob
/// `AY_SMALL_REDUCE_CAP_MULT` overrides it in [0, 64]; a value of `0` means
/// "uncapped" (remove the small-formula cap entirely for non-dense formulas).
/// Cached per process (each solver run is a fresh process).
#[inline]
pub(super) fn small_formula_reduce_cap_mult() -> u64 {
    // B4: the AY_SMALL_REDUCE_CAP_MULT env override is deleted.
    SMALL_FORMULA_REDUCE_CAP_MULT
}

impl Solver {
    /// Classify a clause using the current dynamic tier boundaries.
    #[inline]
    pub(super) fn clause_tier(&self, clause_idx: usize) -> ClauseTier {
        let lbd = self.arena.lbd(clause_idx);
        // CaDiCaL reduce.cpp:97-98: always use focused-mode boundaries (index 0)
        // for clause tier classification, regardless of current mode.
        if lbd <= self.tiers.tier1_lbd[0] {
            ClauseTier::Core
        } else if lbd <= self.tiers.tier2_lbd[0] {
            ClauseTier::Tier1
        } else {
            ClauseTier::Tier2
        }
    }

    /// Predict whether a clause will survive the next `reduce_db`.
    ///
    /// Ports CaDiCaL `likely_to_be_kept_clause` (internal.hpp:1059-1069).
    /// Irredundant clauses are always kept. Learned clauses in tier1/tier2
    /// (glue <= tier2_lbd) are always kept. Tier3 clauses are kept only if
    /// their glue and size are within the thresholds from the last reduction.
    ///
    /// Used to gate `subsume_dirty` marking (#3727): variables in clauses
    /// that won't survive reduce_db should not trigger subsumption work.
    #[inline]
    pub(super) fn likely_to_be_kept(&self, clause_idx: usize) -> bool {
        if !self.arena.is_learned(clause_idx) {
            return true;
        }
        let lbd = self.arena.lbd(clause_idx);
        if lbd <= self.tiers.tier2_lbd[0] {
            return true;
        }
        lbd <= self.tiers.kept_glue
            && (self.arena.len_of(clause_idx) as u32) <= self.tiers.kept_size
    }

    /// Whether small-dense learned-clause reduction should use the denser
    /// reduce target and tighter interval cap.
    ///
    /// This is deliberately disabled for IC3: transition-relation queries can
    /// look dense, and their learned clauses need the conservative IC3
    /// retention policy below.
    #[inline]
    pub(super) fn small_dense_learned_reduce_policy(&self) -> bool {
        !self.cold.ic3_mode
            && self.num_vars > 0
            && self.num_vars < 1000
            && self.num_original_clauses > self.num_vars.max(1).saturating_mul(10)
    }

    #[inline]
    pub(super) fn reduce_permanent_protect_lbd(&self) -> u32 {
        if self.cold.ic3_mode {
            CORE_LBD
        } else {
            // Main-track search keeps only LBD-1 clauses permanently. Stale
            // LBD-2 clauses fall through to the used-gated Core tier so recent
            // conflict-analysis use still protects them.
            //
            // A/B knob (campaign): AY_REDUCE_PROTECT_LBD overrides this. Glucose/
            // CaDiCaL/Kissat treat glue<=2 (CORE_LBD) as the permanent core set
            // (Audemard-Simon); protecting lbd<=2 may retain higher-value clauses
            // across reduce cycles. (B4: the AY_REDUCE_PROTECT_LBD env
            // override is deleted; the shipped value 1 stands.)
            1
        }
    }

    #[inline]
    pub(super) fn small_formula_reduce_interval_cap(&self) -> Option<u64> {
        if self.num_original_clauses > SMALL_FORMULA_REDUCE_CAP_THRESHOLD {
            return None;
        }
        let multiplier = if self.small_dense_learned_reduce_policy() {
            SMALL_DENSE_REDUCE_CAP_MULT
        } else {
            small_formula_reduce_cap_mult()
        };
        // multiplier == 0 => uncapped (remove the small-formula cap entirely).
        if multiplier == 0 {
            return None;
        }
        Some((multiplier * self.num_original_clauses as u64).max(FIRST_REDUCE_DB))
    }

    /// Mark variables in a clause as subsume-dirty if the clause is likely to
    /// survive the next `reduce_db`.
    ///
    /// CaDiCaL clause.cpp:140: `if (likely_to_be_kept_clause(c)) mark_added(c)`.
    /// Must be called AFTER `set_lbd()` for learned clauses — the predicate
    /// depends on the actual LBD, not the arena default of 0 (#3727).
    #[inline]
    pub(super) fn mark_subsume_dirty_if_kept(&mut self, clause_idx: usize) {
        if !self.likely_to_be_kept(clause_idx) {
            return;
        }
        for &lit in self.arena.literals(clause_idx) {
            let v = lit.variable().index();
            if v < self.subsume_dirty.len() {
                self.subsume_dirty[v] = true;
            }
        }
    }

    /// Bump a clause during conflict analysis (CaDiCaL analyze.cpp:225-240).
    ///
    /// For every antecedent clause encountered during 1UIP analysis:
    /// 1. Set `used` to maximum (protects from deletion)
    /// 2. For learned clauses: recompute glue from current assignment and
    ///    promote to a higher tier if the glue decreased
    /// 3. Track per-glue usage for dynamic tier boundary recomputation
    ///
    /// Clause activity plays no role in deletion decisions (#5132) -- only LBD
    /// and clause size determine usefulness per CaDiCaL's `reduce_less_useful`.
    pub(super) fn bump_clause(&mut self, clause_ref: ClauseRef) {
        let clause_idx = clause_ref.0 as usize;

        debug_assert!(
            self.arena.is_active(clause_idx),
            "BUG: bump_clause called on inactive/deleted clause {clause_idx}"
        );

        // (1) Set used to maximum (CaDiCaL: c->used = max_used = 31)
        //
        // Under the two-stage arm this is the conflict-analysis half of
        // `OnClauseUse(c)` and becomes `score(c) += 1` instead: the paper wants
        // a cumulative usage FREQUENCY, and saturating to MAX_USED here would
        // flatten "used once" and "used ten thousand times" into the same
        // value, which is the whole distinction stage 1 sorts on.
        if self.two_stage_clause_management {
            self.two_stage_note_analysis_use(clause_idx);
        } else {
            self.arena
                .set_used(clause_idx, crate::clause_arena::MAX_USED);
        }

        // (2) Recompute glue and promote for learned clauses
        if !self.arena.is_learned(clause_idx) || self.arena.is_empty_clause(clause_idx) {
            return;
        }
        let old_lbd = self.arena.lbd(clause_idx);
        let new_lbd = self.recompute_glue(clause_idx);
        if new_lbd < old_lbd {
            self.arena.set_lbd(clause_idx, new_lbd);
        }

        // Stored LBD only decreases (CaDiCaL analyze.cpp:230-233).
        // If new_lbd >= old_lbd we keep old_lbd, so the invariant holds.
        debug_assert!(
            self.arena.lbd(clause_idx) <= old_lbd,
            "BUG: bump_clause increased stored LBD from {old_lbd} to {} for clause {clause_idx}",
            self.arena.lbd(clause_idx)
        );

        // (#8229) When a clause is promoted into tier-1 (LBD drops to <= tier2_lbd),
        // mark its variables as JIT-dirty so the next delta recompile picks it up.

        // (3) Track per-glue usage (CaDiCaL analyze.cpp:237-239)
        let glue = self.arena.lbd(clause_idx);
        let mode = usize::from(self.stable_mode);
        let bucket = (glue as usize).min(self.tiers.tier_usage[mode].len() - 1);
        self.tiers.tier_usage[mode][bucket] += 1;
        self.tiers.tier_bump_total[mode] += 1;
    }

    /// Force a full rebuild of reason clause marks on the next `ensure` call (#8100).
    ///
    /// Used for mass-invalidation events where incremental mark/unmark is not
    /// feasible: arena GC (clause indices change), incremental clause deletion
    /// batches, and inprocessing reason-clearing loops.
    ///
    /// Idempotent: multiple calls before the next `ensure` are free.
    #[inline]
    pub(super) fn invalidate_reason_clause_marks(&mut self) {
        self.reason_marks_invalidated = true;
    }

    /// Legacy alias for `invalidate_reason_clause_marks()` (#3518 compat).
    ///
    /// Retained to avoid renaming at every call site in one patch. New code
    /// should prefer the explicit name.
    #[inline]
    pub(super) fn bump_reason_graph_epoch(&mut self) {
        self.invalidate_reason_clause_marks();
    }

    /// Incrementally mark a clause as an active reason (#8100).
    ///
    /// **Not called from BCP enqueue functions (#8569).** Backtrack always
    /// invalidates reason marks before any consumer reads them, so
    /// incremental marks written during BCP are wasted cache-line writes.
    /// All consumers call `ensure_reason_clause_marks_current()` which
    /// rebuilds from the trail in O(trail_len) when marks are invalidated.
    ///
    /// Still used by non-BCP paths (learned clause driving assignment in
    /// `search_assign_driving`, external propagation, etc.) where the
    /// caller needs marks to be immediately current.
    ///
    /// Hot path optimization (#8465): `#[inline(always)]` ensures this is
    /// fully inlined, allowing the compiler to hoist the
    /// `reason_marks_invalidated` check out of surrounding loops.
    #[inline(always)]
    #[allow(unsafe_code)]
    pub(super) fn mark_reason_clause(&mut self, clause_idx: usize) {
        if self.reason_marks_invalidated {
            return;
        }
        let marks = &mut self.reason_clause_marks;
        if clause_idx < marks.len() {
            // SAFETY: bounds just checked. Use unchecked in release builds
            // to eliminate the second bounds check from the indexing operator.
            // This is the hottest path in BCP -- called on every propagation.
            unsafe { *marks.get_unchecked_mut(clause_idx) = self.reason_clause_epoch };
        } else {
            // Cold path: arena grew beyond initial pre-allocation.
            self.mark_reason_clause_cold(clause_idx);
        }
    }

    /// Cold path for `mark_reason_clause`: arena grew beyond initial allocation.
    /// Separated to keep the hot inline function small (#8465).
    #[cold]
    #[inline(never)]
    fn mark_reason_clause_cold(&mut self, clause_idx: usize) {
        self.reason_clause_marks.resize(clause_idx + 1, 0);
        self.reason_clause_marks[clause_idx] = self.reason_clause_epoch;
    }

    /// Incrementally unmark a clause as an active reason (#8100).
    ///
    /// Called from `backtrack` when a variable with a clause reason is
    /// unassigned. O(1) per call. Safe to call on already-unmarked clauses.
    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn unmark_reason_clause(&mut self, clause_idx: usize) {
        if clause_idx < self.reason_clause_marks.len() {
            // SAFETY: bounds just checked. Use unchecked in release builds
            // to eliminate the second bounds check on the indexing operator.
            // Set to 0 (never matches any valid epoch >= 1).
            unsafe { *self.reason_clause_marks.get_unchecked_mut(clause_idx) = 0 };
        }
    }

    /// Rebuild reason clause marks only if invalidated (#8100).
    ///
    /// With incremental mark/unmark, this is a no-op in the common case
    /// (BCP + backtrack maintain marks). Only fires after mass-invalidation
    /// events (arena GC, bulk deletion, inprocessing).
    #[inline]
    pub(super) fn ensure_reason_clause_marks_current(&mut self) {
        if !self.reason_marks_invalidated {
            return;
        }
        self.refresh_reason_clause_marks();
        self.reason_marks_invalidated = false;
    }

    /// Rebuild clause-indexed reason markers unconditionally. Prefer `ensure_reason_clause_marks_current()`.
    ///
    /// Scans the trail (assigned variables only) instead of all variables.
    /// Cost: O(trail_len). The trail contains exactly the set of assigned
    /// variables, which is the only set that can have active clause reasons.
    /// The epoch mechanism ensures stale marks from previous epochs are
    /// automatically invalidated without an explicit clear pass.
    pub(super) fn refresh_reason_clause_marks(&mut self) {
        if self.reason_clause_epoch == u32::MAX {
            self.reason_clause_marks.fill(0);
            self.reason_clause_epoch = 1;
        } else {
            self.reason_clause_epoch += 1;
        }

        if self.reason_clause_marks.len() < self.arena.len() {
            self.reason_clause_marks.resize(self.arena.len(), 0);
        }

        let epoch = self.reason_clause_epoch;
        // Iterate the trail (O(trail_len)) rather than all variables (O(num_vars)).
        for &lit in &self.trail {
            let vi = lit.variable().index();
            let vd = self.var_data[vi];
            let reason = vd.reason;
            if is_clause_reason(reason) && !vd.is_lazy_theory_reason() {
                let idx = reason as usize;
                if idx < self.reason_clause_marks.len() {
                    self.reason_clause_marks[idx] = epoch;
                }
            }
        }

        // Post-condition: every trail reason clause is marked in the current epoch.
        #[cfg(debug_assertions)]
        {
            for &lit in &self.trail {
                let vi = lit.variable().index();
                let vd = self.var_data[vi];
                let reason = vd.reason;
                if is_clause_reason(reason) && !vd.is_lazy_theory_reason() {
                    let idx = reason as usize;
                    if idx < self.reason_clause_marks.len() {
                        debug_assert!(
                            self.is_reason_clause_marked(idx),
                            "BUG: trail reason clause {idx} not marked after refresh_reason_clause_marks"
                        );
                    } else {
                        tracing::debug!(
                            var_idx = vi,
                            level = vd.level,
                            reason_idx = idx,
                            arena_len = self.arena.len(),
                            "skipping stale out-of-arena trail reason during reason mark refresh"
                        );
                    }
                }
            }
        }
    }

    /// Check whether a clause is marked as a current reason in the active epoch.
    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn is_reason_clause_marked(&self, clause_idx: usize) -> bool {
        let marks = &self.reason_clause_marks;
        // SAFETY: bounds checked by the first condition. Use unchecked in
        // release builds to avoid the redundant check from the index operator.
        clause_idx < marks.len()
            && unsafe { *marks.get_unchecked(clause_idx) } == self.reason_clause_epoch
    }

    /// Recompute dynamic tier boundaries from per-glue usage statistics.
    ///
    /// Ports CaDiCaL `recompute_tier()` (tier.cpp:7-81):
    /// - tier1 = glue where accumulated usage reaches TIER1_LIMIT_PCT% of total
    /// - tier2 = glue where accumulated usage reaches TIER2_LIMIT_PCT%
    /// - Floors: tier1 >= 1, tier2 > tier1
    /// - Exponential backoff scheduling up to 2^16 conflicts
    pub(super) fn recompute_tier(&mut self) {
        self.tiers.tier_recomputed += 1;

        // Schedule next recomputation with exponential backoff (CaDiCaL tier.cpp:12-14)
        let delta = if self.tiers.tier_recomputed >= 16 {
            1u64 << 16
        } else {
            1u64 << self.tiers.tier_recomputed
        };
        self.tiers.next_recompute_tier = self.num_conflicts.saturating_add(delta);

        let mode = usize::from(self.stable_mode);
        let total = self.tiers.tier_bump_total[mode];

        // If no usage data yet, keep defaults (CaDiCaL tier.cpp:25-30)
        if total == 0 {
            self.tiers.tier1_lbd[mode] = CORE_LBD;
            self.tiers.tier2_lbd[mode] = TIER1_LBD;
            debug_assert!(
                self.tiers.tier2_lbd[mode] > self.tiers.tier1_lbd[mode],
                "BUG: default tier constants violate ordering: CORE_LBD={CORE_LBD} >= TIER1_LBD={TIER1_LBD}"
            );
            return;
        }

        // Compute tier1 boundary: glue where accumulated usage >= tier1limit%
        let tier1_target = total * TIER1_LIMIT_PCT / 100;
        let tier2_target = total * TIER2_LIMIT_PCT / 100;

        let usage = &self.tiers.tier_usage[mode];
        let mut new_tier1 = 1u32;
        let mut new_tier2 = 1u32;
        let mut accumulated = usage[0];

        // Find tier1 boundary
        let mut glue = 1usize;
        while glue < usage.len() {
            accumulated += usage[glue];
            if accumulated >= tier1_target {
                new_tier1 = glue as u32;
                break;
            }
            glue += 1;
        }

        // Find tier2 boundary (continue from where tier1 left off).
        // CaDiCaL tier.cpp:48 also starts tier2 from the same glue value
        // as tier1 break — the double-count is intentional (overlapping
        // cumulative thresholds, not exclusive partitions).
        while glue < usage.len() {
            accumulated += usage[glue];
            if accumulated >= tier2_target {
                new_tier2 = glue as u32;
                break;
            }
            glue += 1;
        }

        // Floor enforcement: tier1 >= 1, tier2 > tier1 (CaDiCaL tier.cpp:63-74)
        if new_tier1 < 1 {
            new_tier1 = 1;
        }
        if new_tier2 < 1 {
            new_tier2 = 1;
        }
        if new_tier1 >= new_tier2 {
            new_tier2 = new_tier1 + 1;
        }

        self.tiers.tier1_lbd[mode] = new_tier1;
        self.tiers.tier2_lbd[mode] = new_tier2;

        // Post-condition: tier boundaries are well-ordered for this mode
        // (CaDiCaL tier.cpp:63-74 floor enforcement).
        debug_assert!(
            self.tiers.tier1_lbd[mode] >= 1,
            "BUG: tier1_lbd[{mode}] ({}) < 1 after recompute_tier",
            self.tiers.tier1_lbd[mode]
        );
        debug_assert!(
            self.tiers.tier2_lbd[mode] > self.tiers.tier1_lbd[mode],
            "BUG: tier2_lbd[{mode}] ({}) <= tier1_lbd[{mode}] ({}) after recompute_tier",
            self.tiers.tier2_lbd[mode],
            self.tiers.tier1_lbd[mode]
        );
    }
}
