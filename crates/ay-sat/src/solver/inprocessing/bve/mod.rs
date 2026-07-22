// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded variable elimination (BVE).

use super::super::*;
use super::RANDOM_KSAT_MIN_CLAUSES;

/// Maximum occurrences per polarity during fastelim (preprocessing).
/// CaDiCaL `fastelimocclim=100` (elimfast.cpp:16-22) uses 100 per-polarity.
/// Kissat `eliminateocclim=2000` uses 2000 total for all elimination.
/// On BVE-dominated formulas like mp1-klieber (30K vars, Kissat eliminates
/// 86%), CaDiCaL's 100 is too restrictive. Use 500 per-polarity to allow
/// profitable eliminations while keeping the resolution product bounded
/// (500*500=250K max pairs per var, well within the FASTELIM_EFFORT budget).
const FASTELIM_OCC_LIMIT: usize = 500;

/// Maximum binary degree product (pos_binary * neg_binary) for BVE
/// candidates during gate-based (additive/inprocessing) mode (#8398, #8466).
///
/// CaDiCaL does NOT have this guard. Gate-aware restricted resolution
/// already limits resolvent production. Kept at 100 (#8448) to prevent
/// multi-pass clause explosion on graph-structured formulas (Dodecahedron:
/// active clauses grew from 179K to 205K with limit=1000). The cumulative
/// clause growth guard in config_preprocess_bve.rs provides additional
/// defense, but the per-variable guard is the first line of defense.
///
/// Note (#8466): this guard is NOT applied in fastelim mode. CaDiCaL's
/// fastelim has no binary degree product guard -- it relies on the
/// resolvent counting loop with fastelimbound=8 to reject expensive
/// variables. Skipping the guard in fastelim allows profitable elimination
/// of clique variables where most binary-binary resolvents are tautological.
const BVE_BINARY_DEGREE_PRODUCT_LIMIT: usize = 100;

mod apply;
mod body;
#[cfg(feature = "gpu")]
mod gpu_dispatch;
// elim_propagate removed (#8356): CaDiCaL elim.cpp:251-263 explicitly
// does NOT propagate after adding resolvents. AY's elim_propagate was
// deleting root-level-satisfied resolvents from occ lists, causing
// later eliminations to miss witness entries and corrupt reconstruction.
mod state;
pub(crate) use state::BveBodyScratch;

impl Solver {
    /// Check if we should run BVE.
    ///
    /// Uses a growing interval (CaDiCaL pattern) so BVE runs less frequently
    /// in later phases. Dual fixed-point guard (CaDiCaL `ineliminating()`,
    /// elim.cpp:60-84): re-fire when new level-0 units have been discovered
    /// OR when irredundant clauses were modified by other inprocessing passes
    /// (subsumption, vivification, decompose).
    ///
    /// The `bve_marked` counter tracks irredundant clause modifications only.
    /// This avoids the mutual re-triggering cycle with `clause_db_changes`
    /// Record an irredundant clause deletion as new BVE work.
    ///
    /// Also updates persistent occ lists incrementally when they are populated
    /// (#8096), avoiding a full O(clause_literals) rebuild on the next BVE round.
    pub(in crate::solver) fn note_irredundant_clause_removed_for_bve(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
    ) {
        self.inproc.bve.occ_remove_clause(clause_idx, old_lits);
        self.inproc.bve.mark_candidates_dirty_clause(old_lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
    }

    /// Record a new irredundant clause addition for BVE occ list maintenance.
    ///
    /// Updates persistent occ lists incrementally when they are populated
    /// (#8096). Called when inprocessing techniques other than BVE add new
    /// irredundant clauses (e.g., HTR, factorize, SBVA).
    pub(in crate::solver) fn note_irredundant_clause_added_for_bve(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
    ) {
        self.inproc
            .bve
            .occ_add_new_irredundant(clause_idx, new_lits);
        self.inproc.bve.mark_candidates_dirty_clause(new_lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
    }

    /// Record an irredundant clause strengthening as new BVE work.
    ///
    /// Also updates persistent occ lists incrementally when they are populated
    /// (#8096), avoiding a full O(clause_literals) rebuild on the next BVE round.
    pub(in crate::solver) fn note_irredundant_clause_replaced_for_bve(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
    ) {
        self.inproc
            .bve
            .occ_replace_clause(clause_idx, old_lits, new_lits);
        self.inproc.bve.mark_candidates_dirty_clause(old_lits);
        self.inproc.bve.mark_candidates_dirty_clause(new_lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
    }

    /// Record a learned clause that was promoted to irredundant.
    ///
    /// When subsumption promotes a redundant (learned) clause to irredundant
    /// (because it subsumes an irredundant clause), BVE occ lists must be
    /// updated to include the newly-irredundant clause. Without this, the
    /// occ lists become stale and `refresh_incremental` produces inconsistent
    /// results (#8135).
    pub(in crate::solver) fn note_clause_promoted_to_irredundant(
        &mut self,
        clause_idx: usize,
        lits: &[Literal],
    ) {
        self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
        // When occ lists are live, add the newly-promoted clause so BVE
        // sees it in subsequent rounds (#8096, #8135).
        self.inproc.bve.occ_add_new_irredundant(clause_idx, lits);
        self.inproc.bve.mark_candidates_dirty_clause(lits);
        self.cold.bve_marked = self.cold.bve_marked.saturating_add(1);
        // JIT dirty marking (#8202): promoted clause is now JIT-eligible
        // (irredundant). Mark its variables dirty so delta recompilation
        // picks it up in the next JIT compile pass.
    }

    /// Record the active clause count after a BVE phase for diagnostics.
    ///
    /// Tracks min(post-phase, pre-phase) active clause count. Informational
    /// only — growth control is per-phase in inprocessing_schedule.rs (#7178).
    pub(in crate::solver) fn update_bve_growth_guard(&mut self, clauses_before_phase: usize) {
        // Track irredundant clause count for the growth guard (#8135).
        // Use irredundant count (not total active) because learned clauses
        // from CDCL search should not penalize BVE. Take min of current
        // irredundant count and the before-phase count to get the baseline.
        let irred_now = self.arena.irredundant_count();
        self.cold.last_bve_clauses = irred_now.min(clauses_before_phase);
    }

    /// Detect likely-random k-SAT formulas where gate/BVE passes are
    /// typically wasted work.
    ///
    /// Heuristic (irredundant clauses only):
    /// - no binary clauses
    /// - all clauses have the same length
    /// - uniform length is at least 3
    /// - at least `RANDOM_KSAT_MIN_CLAUSES` active clauses
    ///
    /// This is intentionally conservative: false negatives are acceptable,
    /// false positives on tiny structured formulas are not.
    pub(in crate::solver) fn is_uniform_nonbinary_irredundant_formula(&mut self) -> bool {
        if let Some(cached) = self.cold.uniform_formula_cache {
            return cached;
        }
        let result = self.compute_uniform_nonbinary_irredundant_formula();
        self.cold.uniform_formula_cache = Some(result);
        result
    }

    /// Recompute the uniform formula detection (O(total_clauses)).
    /// Called only when the cache is dirty.
    fn compute_uniform_nonbinary_irredundant_formula(&self) -> bool {
        let mut clause_count = 0usize;
        let mut uniform_len: Option<usize> = None;

        for idx in self.arena.indices() {
            let off = idx;
            if self.arena.is_dead(off) || self.arena.is_learned(off) {
                continue;
            }
            let len = self.arena.len_of(off);

            // Binary/unit/empty clauses indicate structure that can benefit
            // from gate extraction and elimination.
            if len <= 2 {
                return false;
            }

            match uniform_len {
                Some(expected) if expected != len => return false,
                Some(_) => {}
                None => uniform_len = Some(len),
            }

            clause_count += 1;
        }

        clause_count >= RANDOM_KSAT_MIN_CLAUSES && uniform_len.is_some_and(|len| len >= 3)
    }

    /// Invalidate the cached uniform formula detection result.
    /// Must be called when irredundant clauses are added, deleted, or strengthened.
    #[inline]
    pub(in crate::solver) fn invalidate_uniform_formula_cache(&mut self) {
        self.cold.uniform_formula_cache = None;
    }

    /// Run bounded variable elimination
    ///
    /// Attempts to eliminate variables by resolving clauses. For a variable x,
    /// if the total size of resolvents is bounded, we can eliminate x by:
    /// 1. Adding all resolvents
    /// 2. Removing all clauses containing x
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    ///
    /// Returns true if UNSAT was derived (empty resolvent found).
    ///
    /// REQUIRES: decision_level == 0, last_bve_fixed != fixed_count (fixpoint guard)
    /// ENSURES: eliminated variables marked in self.var_lifecycle and removed from VSIDS,
    ///          no active learned clause contains a removed variable,
    ///          reconstruction entries pushed for all deleted clauses
    pub(in crate::solver) fn bve(&mut self) -> bool {
        // Defer the O(num_vars) stale reason scan during bulk deletions.
        // BVE deletes many clauses per variable; batching the scan reduces
        // cost from O(deleted × num_vars) to O(deleted + num_vars).
        let elim_before = self.inproc.bve.stats().vars_eliminated;
        let irredundant_before = self.arena.irredundant_count();
        self.defer_stale_reason_cleanup = true;
        let result = self.bve_body();
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        let elim_after = self.inproc.bve.stats().vars_eliminated;
        let eliminated_this_phase = elim_after.saturating_sub(elim_before);
        let irredundant_after = self.arena.irredundant_count();

        // Productivity-based backoff (#8135, #8482): when BVE eliminates zero
        // variables OR causes a net irredundant clause increase, exponentially
        // grow the interval. On small dense UNSAT formulas like clique_n2_k10
        // (180 vars, 3160 cls), BVE quickly exhausts profitable eliminations
        // and subsequent calls waste time on watch disconnect/reconnect cycles
        // for zero benefit.
        //
        // #8482: On gate-structured circuit formulas (braun family), additive
        // BVE eliminates variables but the resolvents make the formula harder
        // for CDCL search. The irredundant clause count grows steadily across
        // BVE phases (4732 -> 5789 -> 13510 -> 18498 on braun.9), causing
        // massive clause explosion and timeouts. Treating clause-growing BVE
        // phases as unproductive triggers exponential backoff, preventing the
        // runaway resolvent accumulation.
        //
        // Reset the counter only when BVE both eliminates variables AND
        // reduces (or maintains) the irredundant clause count.
        let clause_grew = irredundant_after > irredundant_before;
        if eliminated_this_phase == 0 || clause_grew {
            self.cold.bve_consecutive_unproductive =
                self.cold.bve_consecutive_unproductive.saturating_add(1);
        } else {
            self.cold.bve_consecutive_unproductive = 0;
        }

        // Schedule next BVE with growing interval (CaDiCaL elim.cpp:1161).
        // CaDiCaL: delta = scale(elimint * (phases + 1))
        // scale() = log2(ratio) when clause/var ratio > 2, else 1.0.
        let base = BVE_INTERVAL_BASE.saturating_mul(u64::from(self.cold.bve_phases + 1));
        let ratio = self.num_original_clauses as f64 / self.num_vars.max(1) as f64;
        // Cap at 3.0 (ratio=8 threshold): AY's BVE is weaker than CaDiCaL's,
        // so extreme interval stretching (5.87x on stable-300's ratio=58.5)
        // starves BVE on small high-ratio formulas. CaDiCaL compensates via
        // stronger elimination cascades that AY doesn't yet have (#7191).
        let factor = if ratio <= 2.0 {
            1.0
        } else {
            ratio.log2().min(3.0)
        };
        // Exponential backoff for unproductive phases (#8135):
        // streak 0: 1x, streak 1: 2x, streak 2: 4x, streak 3: 8x, ...
        // Capped at 64x to prevent BVE from being starved forever.
        let unproductive_scale = if self.cold.bve_consecutive_unproductive > 0 {
            (1u64 << self.cold.bve_consecutive_unproductive.min(6)) as f64
        } else {
            1.0
        };
        let interval = (base as f64 * factor * unproductive_scale) as u64;
        self.inproc_ctrl
            .bve
            .reschedule(self.num_conflicts, interval);
        // Record ticks for tick-threshold scheduling (#8148).
        self.cold.last_bve_ticks = self.search_ticks[0] + self.search_ticks[1];
        result
    }
}
