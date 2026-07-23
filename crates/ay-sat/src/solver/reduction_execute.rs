// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause database reduction execution: flush and normal reduce paths.
//!
//! Split from `reduction.rs` for file-size compliance (#5142).
//! Contains `reduce_db` and its helper functions that execute the
//! actual deletion of learned clauses.

use super::*;

#[inline]
fn reduce_candidate_rank(glue: u32, size: u32) -> u64 {
    (u64::from(glue) << 32) | u64::from(size)
}

#[inline]
fn reduce_candidate_rank_with_low_word_bias(glue: u32, size: u32, bias: u32) -> u64 {
    let biased_size = size.saturating_add(bias);
    (u64::from(glue) << 32) | u64::from(biased_size)
}

#[inline]
fn reduce_candidate_rank_with_low_word_retention(glue: u32, size: u32, bias: u32) -> u64 {
    let retained_size = size.saturating_sub(bias.min(size));
    (u64::from(glue) << 32) | u64::from(retained_size)
}

#[inline]
fn learned_1963_pressure_reduction_pressure_steps(
    record: &solver_stats::BcpLearned1963IdentityRecord,
) -> u64 {
    record
        .no_replacement_steps
        .max(record.fsw_steps)
        .max(record.repeat_steps)
}

#[inline]
fn learned_1963_pressure_reduction_rank_bias(
    record: &solver_stats::BcpLearned1963IdentityRecord,
) -> u32 {
    let pressure_steps = learned_1963_pressure_reduction_pressure_steps(record);
    if pressure_steps == 0 {
        return 0;
    }
    let step_log = u64::BITS - pressure_steps.leading_zeros();
    let event_bonus = record
        .fsw
        .saturating_add(record.unit)
        .saturating_add(record.conflict)
        .saturating_add(record.repeat_scans)
        .min(1_000_000);
    u64::from(step_log)
        .saturating_add(event_bonus)
        .min(1_000_000) as u32
}

#[inline]
fn compare_reduce_candidates(
    a: &cold::ReduceCandidate,
    b: &cold::ReduceCandidate,
) -> std::cmp::Ordering {
    b.rank
        .cmp(&a.rank)
        .then_with(|| a.clause_idx.cmp(&b.clause_idx))
}

#[inline]
fn dynamic_reduce_delete_permille(low_permille: u64, high_permille: u64, reductions: u64) -> u64 {
    debug_assert!(low_permille <= high_permille);
    let high = high_permille as f64;
    let low = low_permille as f64;
    let permille = if low < high {
        high - (high - low) / (reductions as f64 + 9.0).log10()
    } else {
        low
    };
    permille.clamp(low, high) as u64
}

impl Solver {
    /// Reduce deletion order is only semantically observed by deterministic
    /// decision/replay traces. LRAT/DRAT proof deletion correctness is handled
    /// by `delete_clause_unchecked` emitting each deletion before the arena
    /// entry is removed; proof checkers do not require a pre-sorted reduce
    /// batch.
    #[inline]
    fn reduce_delete_order_is_trace_observable(&self) -> bool {
        self.cold.decision_trace.is_some() || self.cold.replay_trace.is_some()
    }

    #[inline]
    fn reduce_trace_clause_id(&self, idx: usize) -> u64 {
        let clause_ref = ClauseRef(idx as u32);
        let clause_id = self.clause_id(clause_ref);
        if clause_id == 0 {
            (idx as u64) + 1
        } else {
            clause_id
        }
    }

    fn collect_reduce_trace_ids<I>(&self, indices: I) -> Option<Vec<u64>>
    where
        I: IntoIterator<Item = usize>,
    {
        if !self.reduce_delete_order_is_trace_observable() {
            return None;
        }
        let clause_ids: Vec<u64> = indices
            .into_iter()
            .map(|idx| self.reduce_trace_clause_id(idx))
            .collect();
        if clause_ids.is_empty() {
            None
        } else {
            Some(clause_ids)
        }
    }

    #[inline]
    fn learned_1963_pressure_reduction_rank(
        &self,
        idx: usize,
        glue: u32,
        size: u32,
    ) -> Option<(u64, u32, u64)> {
        if !self.cold.bcp_learned_1963_pressure_reduction || !(19..=63).contains(&size) {
            return None;
        }
        let clause_id = self.cold.clause_ids.get(idx).copied().unwrap_or(0);
        let record = self.stats.bcp_learned_1963_identity_record(clause_id)?;
        if record.clause_id != clause_id || record.clause_len != u64::from(size) {
            return None;
        }
        let bias = learned_1963_pressure_reduction_rank_bias(record);
        if bias == 0 {
            return None;
        }
        Some((
            reduce_candidate_rank_with_low_word_bias(glue, size, bias),
            bias,
            learned_1963_pressure_reduction_pressure_steps(record),
        ))
    }

    #[inline]
    fn learned_1963_pressure_retention_rank(
        &self,
        idx: usize,
        glue: u32,
        size: u32,
    ) -> Option<(u64, u32, u64)> {
        if !self.cold.bcp_learned_1963_pressure_retention || !(19..=63).contains(&size) {
            return None;
        }
        let clause_id = self.cold.clause_ids.get(idx).copied().unwrap_or(0);
        let record = self.stats.bcp_learned_1963_identity_record(clause_id)?;
        if record.clause_id != clause_id || record.clause_len != u64::from(size) {
            return None;
        }
        let bias = learned_1963_pressure_reduction_rank_bias(record);
        if bias == 0 {
            return None;
        }
        Some((
            reduce_candidate_rank_with_low_word_retention(glue, size, bias),
            bias,
            learned_1963_pressure_reduction_pressure_steps(record),
        ))
    }

    #[inline]
    fn bve_occurrence_maintenance_live(&self) -> bool {
        self.inproc.bve.is_occ_populated()
    }

    #[inline]
    fn note_live_bve_irredundant_clause_removed(&mut self, idx: usize) {
        if !self.bve_occurrence_maintenance_live() {
            return;
        }
        let old_lits: Vec<Literal> = self.arena.literals(idx).to_vec();
        self.note_irredundant_clause_removed_for_bve(idx, &old_lits);
    }

    /// Check if a clause is satisfied by a literal assigned at decision level 0.
    ///
    /// Level-0 satisfied clauses are trivially true and should be excluded from
    /// reduction candidates to avoid wasting the deletion budget (#3723).
    /// Reference: CaDiCaL `clause_contains_fixed_literal()` (collect.cpp:73-88).
    fn clause_satisfied_at_level0(&self, idx: usize) -> bool {
        // Bounds-check: verify the clause literal span fits in the arena
        // before accessing literals. Misaligned arena walks (e.g., after
        // shrunk-clause stride miscalculation in BVE) can produce offsets
        // where lit_len_raw reads garbage, causing OOB panics in literals()
        // or SIGBUS in the unchecked val_at() path (#8231).
        let len = self.arena.len_of(idx);
        if idx + crate::clause_arena::HEADER_WORDS + len > self.arena.len() {
            debug_assert!(
                false,
                "BUG: clause_satisfied_at_level0: clause at offset {} has \
                 len={} but arena len={}, skipping corrupt clause",
                idx,
                len,
                self.arena.len(),
            );
            return false;
        }
        for &lit in self.arena.literals(idx) {
            // Guard: validate literal is in range before unchecked val access.
            // Out-of-range literals indicate arena corruption (e.g., misaligned
            // arena walk after shrunk-clause stride miscalculation). Without this
            // check, release builds hit SIGBUS in the unchecked val_at() path.
            if lit.variable().index() >= self.num_vars {
                debug_assert!(
                    false,
                    "BUG: clause_satisfied_at_level0: clause at offset {} has \
                     out-of-range literal raw={} (var={}, num_vars={})",
                    idx,
                    lit.raw(),
                    lit.variable().index(),
                    self.num_vars,
                );
                continue;
            }
            if self.lit_val(lit) > 0 && self.var_data[lit.variable().index()].level == 0 {
                return true;
            }
        }
        false
    }

    /// Pre-reduction cleanup: delete all clauses already satisfied at level 0.
    ///
    /// Matches CaDiCaL `mark_satisfied_clauses_as_garbage()` before reduction
    /// candidate planning (collect.cpp:73-88, reduce.cpp:226). These clauses are
    /// permanently true and should not remain in the clause DB. This includes
    /// both learned and irredundant (original) clauses — a level-0-satisfied
    /// original clause is redundant and can be safely garbage-collected.
    /// Proof correctness: `delete_clause_unchecked` traces deletions for both
    /// learned and irredundant clauses via `proof_emit_delete_arena`.
    ///
    /// Occurrence-guided path (#8097): when `gc_occ` is available, only visit
    /// clauses that contain a level-0 true literal, found via occ-list lookup.
    /// This is O(affected) instead of O(total_clauses).
    fn mark_satisfied_clauses_as_garbage(&mut self, allow_full_scan: bool) {
        debug_assert!(
            !self.reason_marks_invalidated,
            "BUG: mark_satisfied_clauses_as_garbage called with stale reason marks",
        );

        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        if level0_end == 0 {
            return;
        }

        if self.gc_occ.is_some() {
            self.stats.reduction_l0_satisfied_occ_scans += 1;
            // Occurrence-guided path: collect clause indices that contain a
            // level-0 true literal. These are the only candidates for deletion.
            // We iterate over the level-0 segment of the trail and look up each
            // literal's occurrence list to find clauses that contain it (and are
            // therefore satisfied).
            let arena_len = self.arena.len();
            self.cold.reduce_indices_buf.clear();

            // SAFETY: gc_occ is Some (checked above). We take a shared ref to
            // gc_occ while also reading trail/trail_lim (no aliasing issue).
            let gc_occ = self.gc_occ.as_ref().expect("checked above");
            for i in 0..level0_end {
                let lit = self.trail[i];
                // Only look at literals that are actually true at level 0.
                if self.lit_val(lit) > 0 && self.var_data[lit.variable().index()].level == 0 {
                    for &cidx in gc_occ.get(lit) {
                        if cidx < arena_len {
                            self.cold.reduce_indices_buf.push(cidx);
                        }
                    }
                }
            }
            // Sort and deduplicate so each clause is visited at most once.
            self.cold.reduce_indices_buf.sort_unstable();
            self.cold.reduce_indices_buf.dedup();

            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if !self.arena.is_active(idx) {
                    continue;
                }
                if self.is_reason_clause_marked(idx) {
                    continue;
                }
                // Never delete unit clauses. Unit clauses propagate level-0
                // facts that must survive across incremental solve re-entries.
                // continue_solving_with_extension_raw() undoes all assignments
                // (including level 0) and relies on process_initial_clauses()
                // to re-propagate unit clauses from the arena. If a unit clause
                // was garbage-collected here, the literal is lost on re-entry,
                // causing invalid_sat_model failures (#8470).
                if self.arena.len_of(idx) == 1 {
                    continue;
                }
                // The clause contains at least one level-0 true literal (by
                // construction from the occ list), so it is satisfied.
                // Double-check with clause_satisfied_at_level0 in debug mode.
                debug_assert!(
                    self.clause_satisfied_at_level0(idx),
                    "BUG: occ-guided candidate {idx} is not actually L0-satisfied"
                );
                // BVE occ list maintenance (#8365): notify BVE of irredundant
                // clause deletion so occ lists stay consistent. This is a no-op
                // when occ lists aren't populated (the common case during search).
                // When occ lists ARE populated (BVE ran recently and reduce_db
                // fires before the next BVE round rebuilds), this prevents stale
                // occ entries from corrupting BVE's elimination decisions.
                if !self.arena.is_learned(idx) {
                    self.note_live_bve_irredundant_clause_removed(idx);
                }
                let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                self.stats.reduction_l0_satisfied_deleted += 1;
            }
        } else if !allow_full_scan {
            // Slot 615: ordinary interval reductions should not pay an
            // arena-wide scan just to find clauses satisfied by root facts.
            // Without gc_occ, keep candidate ranking/deletion policy unchanged
            // and leave this cleanup to occ-guided, flush, or explicit-pressure
            // reductions.
            self.stats.reduction_l0_satisfied_no_occ_skips += 1;
        } else {
            // Fallback: full scan when gc_occ is not yet initialized.
            // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
            self.stats.reduction_l0_satisfied_full_scans += 1;
            self.cold.reduce_indices_buf.clear();
            self.cold.reduce_indices_buf.extend(self.arena.indices());
            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if !self.arena.is_active(idx) {
                    continue;
                }
                if self.is_reason_clause_marked(idx) {
                    continue;
                }
                // Never delete unit clauses (#8470): see occ-guided path above.
                if self.arena.len_of(idx) == 1 {
                    continue;
                }
                if self.clause_satisfied_at_level0(idx) {
                    // BVE occ list maintenance (#8365): same as occ-guided path.
                    if !self.arena.is_learned(idx) {
                        self.note_live_bve_irredundant_clause_removed(idx);
                    }
                    let _ = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                    self.stats.reduction_l0_satisfied_deleted += 1;
                }
            }
        }
    }

    /// Check if a clause flush is due (CaDiCaL reduce.cpp:26-30).
    ///
    /// Flush is more aggressive than normal reduce: it marks ALL unused
    /// learned clauses as garbage regardless of tier. Triggered at
    /// geometrically growing conflict intervals (default 100K x 3^n).
    #[inline]
    fn flushing(&self) -> bool {
        self.num_conflicts >= self.cold.next_flush
    }

    #[inline]
    fn explicit_reduce_pressure(&self) -> bool {
        if self.learned_clause_limit_exceeded() {
            return true;
        }
        if let Some(limit) = self.cold.max_clause_db_bytes {
            if self.clause_db_memory_bytes() > limit {
                return true;
            }
        }
        false
    }

    #[inline]
    pub(super) fn reduce_delete_permille(&self) -> u64 {
        let low = if self.small_dense_learned_reduce_policy() {
            SMALL_DENSE_REDUCE_LOW_PERMILLE
        } else {
            REDUCE_LOW_PERMILLE
        };
        dynamic_reduce_delete_permille(low, REDUCE_HIGH_PERMILLE, self.cold.num_reductions)
    }

    /// Aggressive clause flush: mark all unused learned clauses as garbage.
    ///
    /// Ports CaDiCaL `mark_clauses_to_be_flushed()` (reduce.cpp:34-58).
    /// Unlike normal reduce (which sorts candidates and deletes the worst 75%),
    /// flush evaluates each clause individually:
    /// - Core (glue <= tier1): survives if `used > 0` (any recent usage)
    /// - Tier1 (tier1 < glue <= tier2): survives if `used >= MAX_USED - 1` (very recent)
    /// - Tier2 (glue > tier2): unconditionally marked as garbage
    ///
    /// Does NOT update `kept_glue`/`kept_size` (CaDiCaL reduce.cpp:57 comment).
    fn mark_clauses_to_be_flushed(&mut self, deterministic_order: bool) -> Vec<usize> {
        let mut to_flush = Vec::new();
        let mut considered = 0u64;
        let mut deleted = 0u64;
        let mut reason_protected = 0u64;
        let mut ic3_protected = 0u64;
        let mut low_lbd_protected = 0u64;
        let mut usage_protected = 0u64;
        let mut hyper_deleted = 0u64;
        let mut hyper_kept = 0u64;

        // Reuse persistent buffer and enumerate learned clauses from the arena's
        // learned-clause index instead of walking the full mixed arena.
        self.cold.reduce_indices_buf.clear();
        self.cold
            .reduce_indices_buf
            .extend(self.arena.learned_indices());
        for i in 0..self.cold.reduce_indices_buf.len() {
            let idx = self.cold.reduce_indices_buf[i];
            if !self.arena.is_active(idx) {
                continue;
            }
            if !self.arena.is_learned(idx) {
                continue;
            }
            considered += 1;
            if self.is_reason_clause_marked(idx) {
                reason_protected += 1;
                continue;
            }
            // IC3 lemma protection (#8662 Gap 6): IC3 blocking clauses must
            // persist across incremental queries. They are never eligible for
            // reduction — deleting them causes false UNSAT on consecution queries.
            if self.arena.is_ic3_lemma(idx) {
                ic3_protected += 1;
                continue;
            }

            // CaDiCaL reduce.cpp:44-46: save pre-decrement value, then decay.
            let used = self.arena.used(idx);
            self.arena.decay_used(idx);

            // CaDiCaL reduce.cpp:47-52: hyper resolvents have one-round
            // lifetime in both flush and normal paths.
            if self.arena.is_hyper(idx) {
                debug_assert!(self.arena.len_of(idx) <= 3);
                if used == 0 {
                    to_flush.push(idx);
                    deleted += 1;
                    hyper_deleted += 1;
                } else {
                    hyper_kept += 1;
                }
                continue;
            }

            // Permanent protection for low-glue clauses during flush. Main
            // keeps only LBD-1 permanently; IC3 keeps CORE_LBD because blocking
            // lemmas must persist across incremental queries.
            if self.arena.lbd(idx) <= self.reduce_permanent_protect_lbd() {
                low_lbd_protected += 1;
                continue;
            }

            match self.clause_tier(idx) {
                ClauseTier::Core => {
                    // Core clauses survive flush if they had recent usage
                    if used > 0 {
                        usage_protected += 1;
                        continue;
                    }
                }
                ClauseTier::Tier1 => {
                    // Tier1 needs very recent usage to survive flush
                    if used >= crate::clause_arena::MAX_USED - 1 {
                        usage_protected += 1;
                        continue;
                    }
                }
                ClauseTier::Tier2 => {
                    // Tier2 clauses never survive flush
                }
            }

            to_flush.push(idx);
            deleted += 1;
        }
        if deterministic_order {
            to_flush.sort_unstable();
        }
        self.stats.learned_reduction_considered += considered;
        self.stats.learned_reduction_deleted += deleted;
        self.stats.learned_reduction_reason_protected += reason_protected;
        self.stats.learned_reduction_ic3_protected += ic3_protected;
        self.stats.learned_reduction_low_lbd_protected += low_lbd_protected;
        self.stats.learned_reduction_usage_protected += usage_protected;
        self.stats.learned_reduction_hyper_deleted += hyper_deleted;
        self.stats.learned_reduction_hyper_kept += hyper_kept;
        to_flush
    }

    /// Propagate out-of-order level-0 units before reduce.
    ///
    /// After chronological backtracking, some level-0 units may be assigned
    /// at higher positions in the trail. This function detects them, backtracks
    /// to level 0, and re-propagates to derive all implied units.
    ///
    /// Reference: CaDiCaL reduce.cpp:172-192
    ///
    /// Returns true if no conflict, false if UNSAT at level 0.
    fn propagate_out_of_order_units(&mut self) -> bool {
        if self.decision_level == 0 {
            return true;
        }
        let start = if self.trail_lim.is_empty() {
            0
        } else {
            self.trail_lim[0]
        };
        let mut found_oou = false;
        for i in start..self.trail.len() {
            let lit = self.trail[i];
            if self.var_data[lit.variable().index()].level == 0 {
                found_oou = true;
                break;
            }
        }
        if !found_oou {
            return true;
        }
        self.backtrack(0);
        self.search_propagate().is_none()
    }

    /// Reduce the learned clause database using tier-based management.
    ///
    /// When a flush is due (`num_conflicts >= next_flush`), uses the aggressive
    /// flush path that marks ALL unused clauses as garbage regardless of tier
    /// (CaDiCaL reduce.cpp:34-58). Otherwise, uses the normal sort-and-delete
    /// path that removes the worst 75% of tier-2 candidates.
    ///
    /// Normal-mode three-tiered approach based on LBD:
    /// - CORE (LBD <= tier1): Protected if any recent usage (used > 0)
    /// - TIER1 (tier1 < LBD <= tier2): Protected if very recently bumped (used >= MAX_USED-1)
    /// - TIER2 (LBD > tier2): Always enters sort pool, deleted based on (glue, size) ranking
    ///
    /// Deletion scoring uses CaDiCaL's `reduce_less_useful` comparator (#5132):
    /// higher glue is deleted first, with size as tiebreak. Activity plays no
    /// role -- per Audemard & Simon (IJCAI'09), LBD alone is the best predictor
    /// of learned clause quality.
    pub(super) fn reduce_db(&mut self) {
        // Queue ownership is stronger than reduction pressure. The final
        // popped conflict may reduce normally once no tail references remain.
        if !self.pending_theory_conflicts.is_empty() {
            return;
        }
        // CaDiCaL reduce.cpp:223: propagate out-of-order units first.
        if self.chrono_enabled && !self.propagate_out_of_order_units() {
            self.has_empty_clause = true;
            return;
        }
        self.cold.num_reductions += 1;
        self.ensure_reason_clause_marks_current();

        let flush = self.flushing();
        let explicit_reduce_pressure = self.explicit_reduce_pressure();
        if flush {
            self.set_diagnostic_pass(DiagnosticPass::Flush);
            self.cold.num_flushes += 1;
        } else {
            self.set_diagnostic_pass(DiagnosticPass::Reduce);
        }

        // (#8356) Guardless JIT invalidation: if the compiled formula was
        // compiled without per-clause guard checks (guardless=true), clause
        // deletions below cannot be communicated to the JIT via guard bits.
        // Reattach JIT-detached watches and invalidate the formula BEFORE any
        // deletion. The stashed formula enables fast delta recompilation after
        // reduce_db completes. Without this, guardless JIT code continues
        // propagating using deleted clause offsets as reasons, corrupting the
        // trail with stale ClauseRefs.

        self.mark_satisfied_clauses_as_garbage(flush || explicit_reduce_pressure);

        if flush {
            // Aggressive flush path (CaDiCaL reduce.cpp:34-58)
            let deterministic_reduce_order = self.reduce_delete_order_is_trace_observable();
            let to_flush = self.mark_clauses_to_be_flushed(deterministic_reduce_order);

            #[cfg(debug_assertions)]
            {
                for &idx in &to_flush {
                    debug_assert!(
                        !self.is_reason_clause_marked(idx),
                        "BUG: flush candidate {idx} is a reason clause -- would corrupt trail"
                    );
                    debug_assert!(
                        self.arena.is_learned(idx),
                        "BUG: flush candidate {idx} is irredundant (not learned)"
                    );
                }
            }

            let trace_deleted_clause_ids = self.collect_reduce_trace_ids(to_flush.iter().copied());

            let mut lrat_retained_delete_skips = 0u64;
            for &idx in &to_flush {
                let delete_result = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                if delete_result == mutate::DeleteResult::Skipped
                    && self.lrat_delete_retained_active_clause(idx)
                {
                    lrat_retained_delete_skips += 1;
                }
            }
            self.stats.learned_reduction_lrat_retained_delete_skips += lrat_retained_delete_skips;
            if let Some(trace_deleted_clause_ids) = trace_deleted_clause_ids {
                self.trace_reduce(trace_deleted_clause_ids);
            }

            // Flush does NOT update kept_glue/kept_size
            // (CaDiCaL reduce.cpp:57: "No change to 'lim.kept{size,glue}'")
        } else {
            // Normal reduce path: select the worst quota and delete it.

            // First pass: decay usage counters and collect deletable clause indices
            self.cold.reduce_candidates_buf.clear();
            let mut considered = 0u64;
            let mut deleted = 0u64;
            let mut reason_protected = 0u64;
            let mut ic3_protected = 0u64;
            let mut low_lbd_protected = 0u64;
            let mut usage_protected = 0u64;
            let mut hyper_deleted = 0u64;
            let mut hyper_kept = 0u64;
            let mut lrat_retained_delete_skips = 0u64;
            let mut pressure_candidates = 0u64;
            let mut pressure_pressure_candidates = 0u64;
            let mut pressure_ranked = 0u64;
            let mut pressure_rank_bias_total = 0u64;
            let mut pressure_selected = 0u64;
            let mut pressure_selected_steps = 0u64;
            let mut pressure_deleted = 0u64;
            let mut pressure_deleted_steps = 0u64;
            let mut pressure_kept = 0u64;
            let mut pressure_kept_steps = 0u64;
            let mut pressure_skipped_no_pressure = 0u64;
            let mut pressure_lrat_retained_delete_skips = 0u64;
            let mut retention_candidates = 0u64;
            let mut retention_pressure_candidates = 0u64;
            let mut retention_ranked = 0u64;
            let mut retention_rank_bias_total = 0u64;
            let mut retention_selected = 0u64;
            let mut retention_selected_steps = 0u64;
            let mut retention_deleted = 0u64;
            let mut retention_deleted_steps = 0u64;
            let mut retention_kept = 0u64;
            let mut retention_kept_steps = 0u64;
            let mut retention_skipped_no_pressure = 0u64;
            let mut retention_lrat_retained_delete_skips = 0u64;

            // Reuse persistent buffer and enumerate learned clauses from the
            // arena's learned-clause index instead of walking the full mixed arena.
            self.cold.reduce_indices_buf.clear();
            self.cold
                .reduce_indices_buf
                .extend(self.arena.learned_indices());
            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if !self.arena.is_active(idx) {
                    continue;
                }
                if !self.arena.is_learned(idx) {
                    continue;
                }
                considered += 1;
                if self.is_reason_clause_marked(idx) {
                    reason_protected += 1;
                    continue;
                }
                // IC3 lemma protection (#8662 Gap 6): IC3 blocking clauses must
                // persist across incremental queries. Never eligible for reduction.
                if self.arena.is_ic3_lemma(idx) {
                    ic3_protected += 1;
                    continue;
                }

                // CaDiCaL reduce.cpp:109-111: save used BEFORE decrement,
                // check against pre-decrement value for tier protection.
                let used = self.arena.used(idx);
                self.arena.decay_used(idx);

                // CaDiCaL reduce.cpp:116-120: hyper resolvents (HBR/HTR)
                // have one-round lifetime. If unused, delete immediately;
                // otherwise keep but never enter the sort pool.
                if self.arena.is_hyper(idx) {
                    debug_assert!(self.arena.len_of(idx) <= 3);
                    if used == 0 {
                        let delete_result =
                            self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                        if delete_result == mutate::DeleteResult::Deleted {
                            deleted += 1;
                            hyper_deleted += 1;
                        } else if delete_result == mutate::DeleteResult::Skipped
                            && self.lrat_delete_retained_active_clause(idx)
                        {
                            lrat_retained_delete_skips += 1;
                        }
                    } else {
                        hyper_kept += 1;
                    }
                    continue;
                }

                // Permanent protection for low-glue clauses. Main keeps only
                // LBD-1 clauses permanently; stale LBD-2 clauses continue into
                // the used-gated Core branch below. IC3 keeps CORE_LBD because
                // glue-2 blocking lemmas must persist across incremental queries.
                if self.arena.lbd(idx) <= self.reduce_permanent_protect_lbd() {
                    low_lbd_protected += 1;
                    continue;
                }

                match self.clause_tier(idx) {
                    ClauseTier::Core => {
                        // CaDiCaL reduce.cpp:112: Core clauses with any recent
                        // usage are protected. Unused Core (used=0) become
                        // deletion candidates — prevents unbounded Core growth.
                        if used > 0 {
                            usage_protected += 1;
                            continue;
                        }
                    }
                    ClauseTier::Tier1 => {
                        // CaDiCaL reduce.cpp:114: Tier1 requires very recent
                        // usage (bumped in the current reduce interval) to
                        // survive. Less aggressive than Core (any usage).
                        if used >= crate::clause_arena::MAX_USED - 1 {
                            usage_protected += 1;
                            continue;
                        }
                    }
                    ClauseTier::Tier2 => {
                        // CaDiCaL reduce.cpp:122: Tier2 always enters the
                        // sort pool — no usage-based protection.
                    }
                }

                let glue = self.arena.lbd(idx);
                let size = self.arena.len_of(idx) as u32;
                let mut rank = reduce_candidate_rank(glue, size);
                let mut pressure_adjusted = false;
                let mut pressure_retained = false;
                let mut pressure_steps = 0u64;
                let pressure_rank_policy_conflict = self.cold.bcp_learned_1963_pressure_reduction
                    && self.cold.bcp_learned_1963_pressure_retention;
                if !pressure_rank_policy_conflict
                    && self.cold.bcp_learned_1963_pressure_reduction
                    && (19..=63).contains(&size)
                {
                    pressure_candidates += 1;
                    if let Some((biased_rank, bias, steps)) =
                        self.learned_1963_pressure_reduction_rank(idx, glue, size)
                    {
                        rank = biased_rank;
                        pressure_adjusted = true;
                        pressure_steps = steps;
                        pressure_pressure_candidates += 1;
                        pressure_ranked += 1;
                        pressure_rank_bias_total += u64::from(bias);
                    } else {
                        pressure_skipped_no_pressure += 1;
                    }
                } else if !pressure_rank_policy_conflict
                    && self.cold.bcp_learned_1963_pressure_retention
                    && (19..=63).contains(&size)
                {
                    retention_candidates += 1;
                    if let Some((biased_rank, bias, steps)) =
                        self.learned_1963_pressure_retention_rank(idx, glue, size)
                    {
                        rank = biased_rank;
                        pressure_retained = true;
                        pressure_steps = steps;
                        retention_pressure_candidates += 1;
                        retention_ranked += 1;
                        retention_rank_bias_total += u64::from(bias);
                    } else {
                        retention_skipped_no_pressure += 1;
                    }
                }
                self.cold.reduce_candidates_buf.push(cold::ReduceCandidate {
                    rank,
                    clause_idx: idx,
                    pressure_adjusted,
                    pressure_retained,
                    pressure_steps,
                });
            }

            // Kissat-style dynamic reduce fraction (#8655):
            // percent = high - (high - low) / log10(reductions + 9)
            // Early: low target (conservative). Late: approaching 90% (aggressive).
            //
            // Kissat reduce.c:105-113: `reducehigh`, `reducelow`, `reductions`.
            // CaDiCaL uses a fixed `reducetarget=75`.
            //
            // The dynamic fraction is better for BMC because early reductions
            // should keep more clauses (the DB is still being populated with
            // useful structural information), while later reductions should be
            // more aggressive (the DB contains many stale clauses from
            // earlier search phases).
            let fraction = self.reduce_delete_permille() as f64 / 1000.0;
            let num_to_delete =
                ((self.cold.reduce_candidates_buf.len() as f64) * fraction) as usize;

            debug_assert!(
                num_to_delete <= self.cold.reduce_candidates_buf.len(),
                "BUG: num_to_delete ({num_to_delete}) exceeds candidates ({})",
                self.cold.reduce_candidates_buf.len()
            );

            // CaDiCaL reduce.cpp:74-82 `reduce_less_useful`: delete by
            // (glue DESC, size DESC). Select only the deletion quota. Sort the
            // deleted prefix only when deterministic decision/replay tracing
            // needs the exact deletion sequence.
            let deterministic_reduce_order = self.reduce_delete_order_is_trace_observable();
            if num_to_delete > 0 {
                if num_to_delete < self.cold.reduce_candidates_buf.len() {
                    let (delete_prefix, _, _) = self
                        .cold
                        .reduce_candidates_buf
                        .select_nth_unstable_by(num_to_delete, compare_reduce_candidates);
                    if deterministic_reduce_order {
                        delete_prefix.sort_unstable_by(compare_reduce_candidates);
                    }
                } else if deterministic_reduce_order {
                    self.cold
                        .reduce_candidates_buf
                        .sort_unstable_by(compare_reduce_candidates);
                }
            }

            // Pre-deletion invariant: no candidate is a reason clause.
            #[cfg(debug_assertions)]
            {
                for i in 0..num_to_delete {
                    let idx = self.cold.reduce_candidates_buf[i].clause_idx;
                    debug_assert!(
                        !self.is_reason_clause_marked(idx),
                        "BUG: reduce_db candidate {idx} is a reason clause -- would corrupt trail"
                    );
                    debug_assert!(
                        self.arena.is_learned(idx),
                        "BUG: reduce_db candidate {idx} is irredundant (not learned)"
                    );
                }
            }

            let trace_deleted_clause_ids = self.collect_reduce_trace_ids(
                self.cold.reduce_candidates_buf[..num_to_delete]
                    .iter()
                    .map(|candidate| candidate.clause_idx),
            );
            for candidate in &self.cold.reduce_candidates_buf[..num_to_delete] {
                if candidate.pressure_adjusted {
                    pressure_selected += 1;
                    pressure_selected_steps =
                        pressure_selected_steps.saturating_add(candidate.pressure_steps);
                }
                if candidate.pressure_retained {
                    retention_selected += 1;
                    retention_selected_steps =
                        retention_selected_steps.saturating_add(candidate.pressure_steps);
                }
            }

            // Mark clauses deleted. Watch entries are flushed eagerly below
            // (CaDiCaL reduce.cpp:232 garbage_collection pattern).
            for i in 0..num_to_delete {
                let idx = self.cold.reduce_candidates_buf[i].clause_idx;
                let pressure_adjusted = self.cold.reduce_candidates_buf[i].pressure_adjusted;
                let pressure_retained = self.cold.reduce_candidates_buf[i].pressure_retained;
                let pressure_steps = self.cold.reduce_candidates_buf[i].pressure_steps;
                let delete_result = self.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
                if delete_result == mutate::DeleteResult::Deleted {
                    deleted += 1;
                    if pressure_adjusted {
                        pressure_deleted += 1;
                        pressure_deleted_steps =
                            pressure_deleted_steps.saturating_add(pressure_steps);
                    }
                    if pressure_retained {
                        retention_deleted += 1;
                        retention_deleted_steps =
                            retention_deleted_steps.saturating_add(pressure_steps);
                    }
                } else if delete_result == mutate::DeleteResult::Skipped
                    && self.lrat_delete_retained_active_clause(idx)
                {
                    lrat_retained_delete_skips += 1;
                    if pressure_adjusted {
                        pressure_lrat_retained_delete_skips += 1;
                    }
                    if pressure_retained {
                        retention_lrat_retained_delete_skips += 1;
                    }
                }
            }
            if let Some(trace_deleted_clause_ids) = trace_deleted_clause_ids {
                self.trace_reduce(trace_deleted_clause_ids);
            }

            // Track maximum glue and size among kept (not deleted) candidates.
            // CaDiCaL reduce.cpp:147-157: feeds likely_to_be_kept_clause for subsumption.
            self.tiers.kept_glue = 0;
            self.tiers.kept_size = 0;
            for i in num_to_delete..self.cold.reduce_candidates_buf.len() {
                let candidate = self.cold.reduce_candidates_buf[i];
                if candidate.pressure_adjusted {
                    pressure_kept += 1;
                    pressure_kept_steps =
                        pressure_kept_steps.saturating_add(candidate.pressure_steps);
                }
                if candidate.pressure_retained {
                    retention_kept += 1;
                    retention_kept_steps =
                        retention_kept_steps.saturating_add(candidate.pressure_steps);
                }
                let idx = candidate.clause_idx;
                let glue = self.arena.lbd(idx);
                let size = self.arena.literals(idx).len() as u32;
                if glue > self.tiers.kept_glue {
                    self.tiers.kept_glue = glue;
                }
                if size > self.tiers.kept_size {
                    self.tiers.kept_size = size;
                }
            }
            self.stats.learned_reduction_considered += considered;
            self.stats.learned_reduction_deleted += deleted;
            self.stats.learned_reduction_reason_protected += reason_protected;
            self.stats.learned_reduction_ic3_protected += ic3_protected;
            self.stats.learned_reduction_low_lbd_protected += low_lbd_protected;
            self.stats.learned_reduction_usage_protected += usage_protected;
            self.stats.learned_reduction_target_kept +=
                (self.cold.reduce_candidates_buf.len() - num_to_delete) as u64;
            self.stats.learned_reduction_lrat_retained_delete_skips += lrat_retained_delete_skips;
            self.stats.learned_reduction_hyper_deleted += hyper_deleted;
            self.stats.learned_reduction_hyper_kept += hyper_kept;
            self.stats.learned_1963_pressure_reduction_candidates += pressure_candidates;
            self.stats
                .learned_1963_pressure_reduction_pressure_candidates +=
                pressure_pressure_candidates;
            self.stats.learned_1963_pressure_reduction_ranked += pressure_ranked;
            self.stats.learned_1963_pressure_reduction_rank_bias_total += pressure_rank_bias_total;
            self.stats.learned_1963_pressure_reduction_selected += pressure_selected;
            self.stats.learned_1963_pressure_reduction_selected_steps += pressure_selected_steps;
            self.stats.learned_1963_pressure_reduction_deleted += pressure_deleted;
            self.stats.learned_1963_pressure_reduction_deleted_steps += pressure_deleted_steps;
            self.stats.learned_1963_pressure_reduction_kept += pressure_kept;
            self.stats.learned_1963_pressure_reduction_kept_steps += pressure_kept_steps;
            self.stats
                .learned_1963_pressure_reduction_skipped_no_pressure +=
                pressure_skipped_no_pressure;
            self.stats
                .learned_1963_pressure_reduction_lrat_retained_delete_skips +=
                pressure_lrat_retained_delete_skips;
            self.stats.learned_1963_pressure_retention_candidates += retention_candidates;
            self.stats
                .learned_1963_pressure_retention_pressure_candidates +=
                retention_pressure_candidates;
            self.stats.learned_1963_pressure_retention_ranked += retention_ranked;
            self.stats.learned_1963_pressure_retention_rank_bias_total += retention_rank_bias_total;
            self.stats.learned_1963_pressure_retention_selected += retention_selected;
            self.stats.learned_1963_pressure_retention_selected_steps += retention_selected_steps;
            self.stats.learned_1963_pressure_retention_deleted += retention_deleted;
            self.stats.learned_1963_pressure_retention_deleted_steps += retention_deleted_steps;
            self.stats.learned_1963_pressure_retention_kept += retention_kept;
            self.stats.learned_1963_pressure_retention_kept_steps += retention_kept_steps;
            self.stats
                .learned_1963_pressure_retention_skipped_no_pressure +=
                retention_skipped_no_pressure;
            self.stats
                .learned_1963_pressure_retention_lrat_retained_delete_skips +=
                retention_lrat_retained_delete_skips;
        }

        // Post-deletion invariant: no reason clause was deleted (shared by both paths).
        // After backtrack store elimination (#6991), unassigned variables retain
        // stale reason values. Only assigned variables have valid reason refs.
        #[cfg(debug_assertions)]
        {
            for (var_idx, vd) in self.var_data.iter().enumerate() {
                if is_clause_reason(vd.reason)
                    && !vd.is_lazy_theory_reason()
                    && vd.level > 0
                    && self.var_is_assigned(var_idx)
                {
                    let idx = vd.reason as usize;
                    debug_assert!(
                        self.arena.is_active(idx),
                        "BUG: reduce_db deleted reason clause {idx} for variable {var_idx}"
                    );
                }
            }
        }

        // CaDiCaL reduce.cpp:232 calls garbage_collection() which includes
        // flush_all_occs_and_watches(). Eagerly flush stale watch entries for
        // deleted clauses instead of letting BCP check is_dead() per watcher.
        self.flush_watches();

        let compact_arena = self.should_compact_arena();

        // Shrink ProofManager tracking sets only at memory/GC policy points.
        // `LiveIdSet::shrink_to_fit` rebuilds bitmap storage; ordinary reduce
        // cycles should not pay that cost when no memory pressure exists.
        if let Some(ref mut manager) = self.proof_manager {
            manager.shrink_known_ids_after_reduction(
                flush || explicit_reduce_pressure || compact_arena,
            );
            #[cfg(debug_assertions)]
            manager.cleanup_debug_tracking(1_000_000);
        }

        // Shrink over-provisioned watch lists (#8031).
        // After clause deletion, many watch lists retain peak capacity despite
        // having far fewer entries. Shrink lists using < 50% of capacity,
        // keeping len*3/2 headroom. Reference: CaDiCaL collect.cpp:225
        // (`shrink_vector(ws)` after flush_watches).
        self.stats.watches_shrunk += self.watches.shrink_watch_lists();

        // Arena locality compaction (CaDiCaL arenatype=3, #8030).
        // Reorder clauses in VMTF decision-queue order for cache locality.
        // Only fires when dead space exceeds 25% of arena size.
        if compact_arena {
            // Rebuild deferred VMTF list before compaction uses it (#7998).
            if self.vsids.vmtf_is_deferred() {
                self.vsids.rebuild_vmtf_from_bump_order(&self.vals);
            }
            self.compact_arena_locality();
        }

        // Schedule next reduction: Kissat-style sqrt(reductions) (#8655).
        //
        // Kissat reduce.c:193: UPDATE_CONFLICT_LIMIT(reduce, reductions, SQRT, false)
        //   => delta = reduceint * sqrt(reductions)
        //   At reduction #1:   delta = 1000 * 1 = 1000
        //   At reduction #10:  delta = 1000 * 3.16 = 3162
        //   At reduction #100: delta = 1000 * 10 = 10000
        //
        // (#8448) Combined with raised REDUCE_LOW_PERMILLE (750) to match
        // CaDiCaL's 75% deletion at early reductions. Kissat's more frequent
        // reductions need more aggressive per-reduction deletion to keep
        // the learned DB lean for BCP throughput.
        let reductions = self.cold.num_reductions;
        let factor = (reductions as f64).sqrt().max(1.0);
        let mut delta = (REDUCE_DB_INT as f64 * factor) as u64;
        // Cap reduce interval for small formulas (#8135).
        // On small dense UNSAT formulas (e.g., clique graphs: 180 vars, 3160
        // clauses), the interval can still grow too large. Capping at 2x
        // num_original_clauses keeps the clause DB proportional to formula size.
        if let Some(cap) = self.small_formula_reduce_interval_cap() {
            delta = delta.min(cap);
        }
        // Cap reduce interval for large formulas (#8655).
        // With sqrt(conflicts) scaling, at 1M conflicts the interval reaches
        // 25K conflicts. On deep BMC formulas with millions of clauses,
        // the learned clause DB bloats significantly in 25K conflicts.
        // Cap at LARGE_FORMULA_REDUCE_MAX_INTERVAL (5000) to keep reductions
        // frequent on large formulas, matching CaDiCaL's effective behavior.
        if self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
            delta = delta.min(LARGE_FORMULA_REDUCE_MAX_INTERVAL);
        }
        delta = delta.max(1);
        self.cold.next_reduce_db = self.num_conflicts.saturating_add(delta);

        debug_assert!(
            self.cold.next_reduce_db >= self.num_conflicts,
            "BUG: reduce_db scheduled in the past: next={} < current={}",
            self.cold.next_reduce_db,
            self.num_conflicts
        );

        // Update flush schedule (CaDiCaL reduce.cpp:261-268)
        if flush {
            self.cold.flush_inc = self.cold.flush_inc.saturating_mul(FLUSH_FACTOR);
            self.cold.next_flush = self.num_conflicts.saturating_add(self.cold.flush_inc);
        }

        // Recompute dynamic tier boundaries if scheduled
        if self.num_conflicts >= self.tiers.next_recompute_tier {
            self.recompute_tier();
        }
    }
}
