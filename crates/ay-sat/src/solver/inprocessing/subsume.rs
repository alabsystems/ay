// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward and self-subsumption.

use super::super::mutate::{DeleteResult, ReasonPolicy, ReplaceResult};
use super::super::*;
#[cfg(feature = "gpu")]
use crate::gpu::subsume as gpu_subsume;

impl Solver {
    #[inline]
    pub(in crate::solver) fn use_large_sparse_subsume_idle_cooldown(&self) -> bool {
        let active_clauses = self.arena.active_clause_count();
        if active_clauses < SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES {
            return false;
        }
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        active_vars > 0
            && active_clauses <= active_vars.saturating_mul(SUBSUME_LARGE_SPARSE_MAX_DENSITY)
    }

    #[inline]
    fn schedule_next_subsume(&mut self, made_progress: bool) {
        let (growth_numer, growth_denom, max_interval) = if made_progress {
            // Progressing rounds should run again relatively soon.
            (3, 2, SUBSUME_MAX_INTERVAL)
        } else if self.use_large_sparse_subsume_idle_cooldown() {
            // Large sparse Main-track formulas can spend meaningful wall time
            // just setting up no-op subsumption rounds. Cool those down harder.
            (4, 1, SUBSUME_LARGE_MAX_IDLE_INTERVAL)
        } else {
            // No-op rounds are frequently net-negative on structured SAT.
            // Back off more aggressively before retrying.
            (2, 1, SUBSUME_MAX_IDLE_INTERVAL)
        };
        self.inproc_ctrl.subsume.reschedule_growing(
            self.num_conflicts,
            SUBSUME_INTERVAL,
            growth_numer,
            growth_denom,
            max_interval,
        );
    }

    /// Apply one forward-subsumption deletion with the full set of soundness
    /// guards. Shared by ALL subsumption-result appliers (the preprocess
    /// cleanup stage plus the inprocessing CPU/GPU/SIMD paths) so the guards
    /// cannot diverge again.
    ///
    /// Guards, in order:
    /// 1. Skip self-subsumption (identical clause indices).
    /// 2. Skip if the subsumed clause is out-of-range, inactive, or dead
    ///    (an earlier deletion in the same batch may have removed it).
    /// 3. Skip if the subsumer is not alive (#6913): in batched forward
    ///    subsumption an earlier iteration may have deleted the subsumer.
    ///    Deleting an irredundant clause whose subsumer is gone loses the
    ///    constraint — the formula becomes equisatisfiable rather than
    ///    equivalent, which is unsound.
    /// 4. If an irredundant clause is subsumed by a learned (redundant)
    ///    clause, promote the subsumer to irredundant FIRST (CaDiCaL
    ///    subsume.cpp:125-149) and notify BVE occ maintenance (#8135).
    ///    Otherwise the constraint's only survivor is a learned clause that
    ///    BVE may later delete with no resolvent and no reconstruction
    ///    witness, silently making an UNSAT database satisfiable.
    /// 5. On actual deletion of an irredundant clause, notify BVE dirty
    ///    tracking with a pre-delete literal snapshot (#7905).
    ///
    /// Returns `true` iff the subsumed clause was actually deleted.
    pub(in crate::solver) fn apply_forward_subsumption_deletion(
        &mut self,
        subsumed_idx: usize,
        subsumer_idx: usize,
    ) -> bool {
        // (1) Self-subsumption: never delete a clause on its own authority.
        if subsumed_idx == subsumer_idx {
            return false;
        }
        // (2) Subsumed clause must still be alive.
        if subsumed_idx >= self.arena.len()
            || !self.arena.is_active(subsumed_idx)
            || self.arena.is_dead(subsumed_idx)
        {
            return false;
        }
        // (3) Subsumer-alive guard (#6913).
        let subsumer_alive = subsumer_idx < self.arena.len()
            && self.arena.is_active(subsumer_idx)
            && !self.arena.is_dead(subsumer_idx);
        if !subsumer_alive {
            return false;
        }

        let subsumed_learned = self.arena.is_learned(subsumed_idx);
        let subsumer_learned = self.arena.is_learned(subsumer_idx);

        // (4) Irredundant subsumed by redundant: promote subsumer first.
        if !subsumed_learned && subsumer_learned {
            self.arena.set_learned(subsumer_idx, false);
            // BVE occ lists only track irredundant clauses. The promoted
            // clause was learned (not in occ lists) and is now irredundant.
            // Notify BVE so incremental occ maintenance stays consistent (#8135).
            let promoted_lits: Vec<Literal> = self.arena.literals(subsumer_idx).to_vec();
            self.note_clause_promoted_to_irredundant(subsumer_idx, &promoted_lits);
        }

        // Snapshot literals before delete for BVE dirty-candidate marking (#7905).
        let subsumed_old_lits = if !subsumed_learned {
            Some(self.arena.literals(subsumed_idx).to_vec())
        } else {
            None
        };

        if matches!(
            self.delete_clause_checked(subsumed_idx, ReasonPolicy::Skip),
            DeleteResult::Deleted
        ) {
            // (5) Mark per-variable dirty candidates for BVE re-trigger (#7905).
            if !subsumed_learned {
                self.note_irredundant_clause_removed_for_bve(
                    subsumed_idx,
                    subsumed_old_lits
                        .as_deref()
                        .expect("irredundant subsumed clause snapshot"),
                );
            }
            true
        } else {
            false
        }
    }

    /// Run GPU-accelerated pairwise subsumption as a bulk pre-pass.
    ///
    /// Collects all active clauses (irredundant AND learned — the shared
    /// deletion applier promotes a learned subsumer to irredundant when it
    /// subsumes an irredundant clause) with no level-0 fixed literals,
    /// sends them to the GPU for O(n^2) pairwise checking, and applies
    /// `(subsumed_idx, subsumer_idx)` pairs through the standard guarded
    /// deletion pipeline.
    ///
    /// Only runs when the clause count exceeds `gpu_subsume::GPU_SUBSUME_THRESHOLD`
    /// (10K). Below that, GPU dispatch overhead exceeds the parallelism benefit.
    ///
    /// Returns the number of GPU-detected subsumptions applied.
    #[cfg(feature = "gpu")]
    fn gpu_subsume_prepass(&mut self) -> usize {
        // Collect active clauses suitable for GPU subsumption: irredundant,
        // no fixed literals, within size limit.
        let mut clause_indices: Vec<usize> = Vec::new();
        for idx in self.arena.indices() {
            if self.arena.is_dead(idx) || self.arena.is_empty_clause(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if lits.len() > 100 {
                continue;
            }
            // Skip clauses with level-0 fixed literals.
            let has_fixed = lits.iter().any(|lit| {
                let li = lit.index();
                li < self.vals.len() && self.vals[li] != 0
            });
            if has_fixed {
                continue;
            }
            clause_indices.push(idx);
        }

        if !gpu_subsume::should_use_gpu(clause_indices.len()) {
            return 0;
        }

        // Lazy-init GPU context.
        let ctx = match self.inproc.gpu_context() {
            Some(ctx) => ctx,
            None => return 0,
        };

        // Pack clauses as raw u32 literal arrays for the GPU.
        let raw_clauses: Vec<Vec<u32>> = clause_indices
            .iter()
            .map(|&idx| self.arena.literals(idx).iter().map(|lit| lit.0).collect())
            .collect();
        let clause_refs: Vec<&[u32]> = raw_clauses.iter().map(|c| c.as_slice()).collect();

        let pairs = match gpu_subsume::gpu_subsume_check(ctx, &clause_refs) {
            Ok(pairs) => pairs,
            Err(err) => {
                tracing::debug!("GPU subsumption check failed (falling back to CPU): {err}");
                return 0;
            }
        };

        // Apply GPU-detected subsumption: translate pair indices back to
        // arena clause indices and feed into the standard deletion pipeline.
        let mut applied = 0;
        for pair in &pairs {
            let subsumer_arena_idx = clause_indices[pair.subsumer];
            let subsumed_arena_idx = clause_indices[pair.subsumed];
            if self.apply_forward_subsumption_deletion(subsumed_arena_idx, subsumer_arena_idx) {
                applied += 1;
            }
        }

        if applied > 0 {
            tracing::debug!(
                gpu_pairs = pairs.len(),
                applied,
                clauses_checked = clause_indices.len(),
                "GPU subsumption pre-pass"
            );
        }
        applied
    }

    /// Run SIMD-accelerated batch subsumption as a pre-pass (#8410).
    ///
    /// Packs active clauses into a cache-friendly SIMD arena, generates
    /// candidate pairs sorted by size, and uses NEON/SSE2 to check
    /// subsumption with 4-lane parallel literal comparison.
    ///
    /// Returns the number of SIMD-detected subsumptions applied.
    #[cfg(feature = "jit")]
    fn simd_subsume_prepass(&mut self) -> usize {
        let result = crate::subsume::simd_prepass::simd_subsume_prepass(&self.arena, &self.vals);

        if result.pairs.is_empty() {
            return 0;
        }

        let mut applied = 0;
        for &(subsumed_arena_idx, subsumer_arena_idx) in &result.pairs {
            if self.apply_forward_subsumption_deletion(subsumed_arena_idx, subsumer_arena_idx) {
                applied += 1;
            }
        }

        if applied > 0 {
            tracing::debug!(
                simd_pairs = result.pairs.len(),
                applied,
                clauses_packed = result.clauses_packed,
                pairs_checked = result.pairs_checked,
                "SIMD subsumption pre-pass"
            );
        }
        applied
    }

    /// Run CaDiCaL-style one-watch forward subsumption.
    ///
    /// Uses per-variable `subsume_dirty` bits for incremental scheduling:
    /// only clauses with >= 2 dirty variables are candidates. After a
    /// complete round, dirty bits are reset. Strengthened clauses re-mark
    /// their variables for the next round (CaDiCaL `mark_added`).
    ///
    /// REQUIRES: decision_level == 0
    /// ENSURES: subsumed clauses deleted, strengthened clauses shrunk
    pub(in crate::solver) fn subsume(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // GPU pre-pass: when clause count exceeds threshold, run GPU pairwise
        // subsumption as a bulk accelerator before the fine-grained CPU pass.
        // The GPU pass handles the embarrassingly-parallel O(n^2) case; the
        // CPU pass then handles incremental dirty-variable-guided checking.
        #[cfg(feature = "gpu")]
        {
            let _gpu_applied = self.gpu_subsume_prepass();
        }

        // SIMD pre-pass (#8410): when the jit feature is enabled, run
        // NEON/SSE2 batch subsumption before the one-watch CPU pass.
        // Packs clauses into a cache-friendly flat arena and uses 4-lane
        // SIMD comparisons for literal matching. Handles the bulk pairwise
        // case; the CPU pass then handles incremental dirty-variable checking.
        #[cfg(feature = "jit")]
        {
            let _simd_applied = self.simd_subsume_prepass();
        }

        // Compute tick-proportional effort limit (CaDiCaL subsume.cpp:349-362,
        // ported to search_ticks delta per SET_EFFORT_LIMIT pattern #8148).
        //
        // CaDiCaL uses `stats.propagations.search * subsumeeffort / 1000`
        // (total propagations). AY uses tick-delta since last subsume call
        // for consistency with the unified tick-proportional scheduling model.
        // The delta approach prevents unbounded budget growth on long-running
        // instances where total propagations can reach billions.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_subsume_ticks);
        let effort = (ticks_delta * self.cold.subsume_effort_permille / 1000)
            .clamp(SUBSUME_MIN_EFFORT, SUBSUME_MAX_EFFORT);
        let effort = effort.max(2 * active_vars);
        self.inproc.subsumer.set_check_limit(effort);

        // Run one-watch forward subsumption with dirty bits, level-0 values,
        // and dynamic keep-set thresholds from the last reduce_db() pass.
        // CaDiCaL: likely_to_be_kept_clause gates candidate selection.
        let kept = crate::subsume::KeptThresholds {
            tier2_lbd: self.tiers.tier2_lbd[0],
            kept_glue: self.tiers.kept_glue,
            kept_size: self.tiers.kept_size,
        };
        let result = self.inproc.subsumer.run_forward_subsumption(
            &mut self.arena,
            &self.cold.freeze_counts,
            &self.subsume_dirty,
            &self.vals,
            kept,
        );
        let subsume_round = self.inproc.subsumer.stats().rounds;
        let dirty_vars = self.subsume_dirty.iter().filter(|&&dirty| dirty).count();
        tracing::debug!(
            round = subsume_round,
            effort_limit = effort,
            candidates = result.candidates_scheduled,
            checks = result.checks_performed,
            subsumed = result.subsumed.len(),
            strengthened = result.strengthened.len(),
            completed = result.completed,
            dirty_vars,
            "subsume round"
        );
        let mut made_progress = false;

        // Apply strengthening (self-subsumption) BEFORE forward subsumption
        // deletions. LRAT correctness requires that subsumer clause IDs are
        // still alive when used as resolution hints. If forward subsumption
        // deletes a clause that is also used as a subsumer for self-subsumption,
        // the batched LRAT deletion is flushed before the self-subsumption add,
        // causing "ERROR: using DELETED hint clause" (#4398).
        for (clause_idx, new_lits, subsumer_idx) in &result.strengthened {
            let clause_alive = *clause_idx < self.arena.len()
                && self.arena.is_active(*clause_idx)
                && !self.arena.is_dead(*clause_idx);
            let subsumer_alive = *subsumer_idx < self.arena.len()
                && self.arena.is_active(*subsumer_idx)
                && !self.arena.is_dead(*subsumer_idx);
            if !clause_alive || !subsumer_alive {
                continue;
            }
            // For LRAT, the subsuming clause is an antecedent of the strengthened
            // clause. Include its clause ID as a resolution hint so the LRAT
            // checker can verify the derivation (#4398).
            //
            // Guard: if the subsumer was replaced/deleted earlier in this loop,
            // its old LRAT ID is pending deletion. Using the stale ID as a hint
            // causes "ERROR: using DELETED hint clause" in lrat-check (#4398).
            // Re-read the subsumer's current LRAT ID (updated by earlier
            // replace_clause_impl calls) to get the replacement's ID.
            let subsumer_hints = if self.cold.lrat_enabled {
                vec![self.clause_id(ClauseRef(*subsumer_idx as u32))]
            } else {
                Vec::new()
            };
            // Read irredundant status before replace (header may be invalidated for Unit).
            let is_irredundant = !self.arena.is_learned(*clause_idx);
            // Snapshot literals before replace for BVE dirty-candidate marking (#7905).
            let old_lits = if is_irredundant {
                Some(self.arena.literals(*clause_idx).to_vec())
            } else {
                None
            };
            match self.replace_clause_with_explicit_lrat_hints(
                *clause_idx,
                new_lits,
                &subsumer_hints,
            ) {
                ReplaceResult::Empty => {
                    self.schedule_next_subsume(true);
                    debug_assert_eq!(
                        self.decision_level, 0,
                        "BUG: subsume() did not restore decision level to 0"
                    );
                    return;
                }
                ReplaceResult::Unit | ReplaceResult::Replaced => {
                    made_progress = true;
                    // Mark per-variable dirty candidates for BVE re-trigger (#7905).
                    if is_irredundant {
                        self.note_irredundant_clause_replaced_for_bve(
                            *clause_idx,
                            old_lits
                                .as_deref()
                                .expect("irredundant strengthened clause snapshot"),
                            new_lits,
                        );
                    }
                }
                ReplaceResult::Skipped => {}
            }
        }

        // Apply deletions (forward-subsumed clauses) AFTER self-subsumption.
        // CaDiCaL subsume.cpp:125-149: if a redundant clause subsumes an
        // irredundant clause, promote the subsumer to irredundant first.
        for &(subsumed_idx, subsumer_idx) in &result.subsumed {
            if self.apply_forward_subsumption_deletion(subsumed_idx, subsumer_idx) {
                made_progress = true;
            }
        }

        // Post-condition: forward-subsumed clauses should either be deleted,
        // protected as active reason clauses, or retained because their subsumer
        // died (#6913: irredundant clauses skip deletion when subsumer is dead).
        #[cfg(debug_assertions)]
        for &(subsumed_idx, subsumer_idx) in &result.subsumed {
            if subsumed_idx >= self.arena.len() || !self.arena.is_active(subsumed_idx) {
                continue;
            }
            // If the clause is irredundant and its subsumer is dead, it was
            // intentionally kept by the #6913 soundness guard above.
            let is_irredundant = !self.arena.is_learned(subsumed_idx);
            let subsumer_dead = subsumer_idx >= self.arena.len()
                || !self.arena.is_active(subsumer_idx)
                || self.arena.is_dead(subsumer_idx);
            if is_irredundant && subsumer_dead {
                continue;
            }
            debug_assert!(
                self.is_reason_clause_marked(subsumed_idx),
                "BUG: subsume() left clause {subsumed_idx} active without reason protection"
            );
        }

        // CaDiCaL subsume.cpp:590: only reset dirty bits when the round
        // completed all scheduled candidates. Incomplete rounds (effort limit
        // hit) preserve dirty state so the next round picks up where this one
        // left off. Without this, large formulas lose incremental state and
        // subsequent rounds only see newly-added clauses (#7279).
        if result.completed {
            for v in self.subsume_dirty.iter_mut() {
                *v = false;
            }
        }
        // Re-mark variables in strengthened clauses for the next round
        // (CaDiCaL subsume.cpp:593-594: mark_added for shrunken clauses).
        for (clause_idx, new_lits, _) in &result.strengthened {
            for lit in new_lits {
                let v = lit.variable().index();
                if v < self.subsume_dirty.len() {
                    self.subsume_dirty[v] = true;
                }
            }
            if *clause_idx < self.arena.len()
                && self.arena.is_active(*clause_idx)
                && !self.arena.is_dead(*clause_idx)
            {
                for &lit in self.arena.literals(*clause_idx) {
                    let v = lit.variable().index();
                    if v < self.subsume_dirty.len() {
                        self.subsume_dirty[v] = true;
                    }
                }
            }
        }

        // Record ticks for tick-threshold scheduling (#8148).
        self.cold.last_subsume_ticks = self.search_ticks[0] + self.search_ticks[1];
        self.schedule_next_subsume(made_progress);
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: subsume() did not restore decision level to 0"
        );
    }
}
