// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable compaction: remove holes in variable-indexed arrays after
//! elimination/substitution.
//!
//! After BVE eliminates 20-50% of variables on industrial instances, every
//! variable-indexed array (`assignment`, `vals`, `phases`, `vsids.scores`,
//! `watch_lists`, `level`, `reason`, etc.) is 20-50% wasted memory with
//! holes. Compaction remaps all active variable indices to a contiguous
//! range `[0..active_count)`, shrinking every array and improving cache
//! utilization in BCP — the #1 performance bottleneck.
//!
//! Reference: CaDiCaL `compact.cpp` (550 lines).

use super::lifecycle;
use super::mutate::ReasonPolicy;
use super::*;
use crate::literal::{Literal, Variable};
use crate::watched::Watcher;

/// Minimum inactive variables before compaction; CaDiCaL: `compactmin = 100`.
const COMPACT_MIN_INACTIVE: usize = 100;

/// Inactive fraction threshold (per-mille of max_var).
/// CaDiCaL: `compactlim = 100` → 100 * 0.001 = 10% of max_var.
const COMPACT_LIMIT_PER_MILLE: usize = 10;

/// Base conflict interval between compaction attempts.
/// CaDiCaL: `compactint = 2000` (options.hpp:55).
const COMPACT_INTERVAL_BASE: u64 = 2_000;

/// Sentinel value meaning "variable is not mapped" (inactive).
pub(crate) const UNMAPPED: u32 = u32::MAX;

/// Mapping table for variable compaction.
///
/// Maps old variable indices to new contiguous indices. Eliminated and
/// substituted variables are unmapped; all active variables (including
/// level-0 fixed) get contiguous new indices.
pub(crate) struct VariableMap {
    /// `old_to_new[old_var_idx]` = new variable index, or `UNMAPPED` if
    /// the variable is inactive (eliminated/substituted).
    pub(crate) old_to_new: Vec<u32>,
    /// New maximum variable count (contiguous range `[0..new_num_vars)`).
    pub(crate) new_num_vars: usize,
}

impl VariableMap {
    /// Build the mapping table from the current solver state.
    ///
    /// Active and non-eliminated variables get contiguous new indices.
    /// Eliminated/substituted variables are unmapped.
    fn build(num_vars: usize, lifecycle: &lifecycle::VarLifecycle) -> Self {
        let mut old_to_new = vec![UNMAPPED; num_vars];
        let mut next_idx: u32 = 0;

        for (var_idx, slot) in old_to_new.iter_mut().enumerate() {
            if lifecycle.is_removed(var_idx) {
                continue;
            }
            *slot = next_idx;
            next_idx += 1;
        }

        Self {
            old_to_new,
            new_num_vars: next_idx as usize,
        }
    }

    /// Map a variable index. Returns `None` if unmapped (inactive).
    #[inline]
    pub(crate) fn map_var(&self, old: usize) -> Option<usize> {
        if old >= self.old_to_new.len() {
            return None;
        }
        let new = self.old_to_new[old];
        if new == UNMAPPED {
            None
        } else {
            Some(new as usize)
        }
    }

    /// Map a literal. Returns `None` if its variable is unmapped.
    #[inline]
    pub(crate) fn map_lit(&self, lit: Literal) -> Option<Literal> {
        self.map_var(lit.variable().index()).map(|new_var| {
            if lit.is_positive() {
                Literal::positive(Variable(new_var as u32))
            } else {
                Literal::negative(Variable(new_var as u32))
            }
        })
    }

    /// Remap a variable-indexed vector in place: copy `vec[old] → vec[new]`,
    /// then truncate to `new_num_vars`.
    pub(crate) fn remap_var_vec<T: Default + Clone>(&self, vec: &mut Vec<T>) {
        if vec.len() < self.old_to_new.len() {
            vec.resize_with(self.old_to_new.len(), T::default);
        }

        // Process forward: since new <= old for all mapped variables,
        // this is safe without a temporary buffer.
        for old in 0..self.old_to_new.len() {
            if let Some(new) = self.map_var(old) {
                if new != old {
                    vec[new] = vec[old].clone();
                }
            }
        }
        vec.truncate(self.new_num_vars);
    }

    /// Remap a literal-indexed vector in place: move entries for both
    /// polarities of each variable, then truncate to `2 * new_num_vars`.
    pub(crate) fn remap_lit_vec<T: Default + Clone>(&self, vec: &mut Vec<T>) {
        let old_num_lits = self.old_to_new.len().saturating_mul(2);
        if vec.len() < old_num_lits {
            vec.resize_with(old_num_lits, T::default);
        }

        for old_var in 0..self.old_to_new.len() {
            if let Some(new_var) = self.map_var(old_var) {
                if new_var != old_var {
                    let old_pos = old_var * 2;
                    let old_neg = old_var * 2 + 1;
                    let new_pos = new_var * 2;
                    let new_neg = new_var * 2 + 1;
                    vec[new_pos] = vec[old_pos].clone();
                    vec[new_neg] = vec[old_neg].clone();
                }
            }
        }
        vec.truncate(self.new_num_vars * 2);
    }
}

impl Solver {
    /// Check if variable compaction should run.
    ///
    /// CaDiCaL `compacting()` guard (compact.cpp:13-27).
    pub(super) fn compacting(&self) -> bool {
        if self.decision_level != 0 {
            return false;
        }
        if self.cold.has_been_incremental {
            return false;
        }
        if self.proof_manager.is_some() {
            return false;
        }
        if self.cold.freeze_counts.iter().any(|&c| c > 0) {
            return false;
        }
        // NOTE: AY skips CaDiCaL's conflict-based interval guard. More
        // aggressive compaction keeps the clause arena tight for cache
        // performance on large formulas (bvsub 598K vars, stable-300).
        let inactive = self.var_lifecycle.count_removed();
        if inactive < COMPACT_MIN_INACTIVE {
            return false;
        }
        // inactive >= 0.001 * COMPACT_LIMIT_PER_MILLE * num_vars
        if inactive * 1000 < COMPACT_LIMIT_PER_MILLE * self.num_vars {
            return false;
        }
        true
    }

    /// Compact variable indices: remap all active variables to a contiguous
    /// range, shrinking every variable-indexed data structure.
    ///
    /// Preconditions: decision level 0, no pending propagation.
    ///
    /// Reference: CaDiCaL `Internal::compact()` (compact.cpp:162-548).
    pub(super) fn compact(&mut self) {
        debug_assert_eq!(self.decision_level, 0);
        debug_assert_eq!(self.qhead, self.trail.len());

        let map = VariableMap::build(self.num_vars, &self.var_lifecycle);

        if map.new_num_vars == self.num_vars {
            return;
        }

        let old_num_vars = self.num_vars;

        // ── Phase 0: Pre-compaction stale clause cleanup (#8464, #8397) ─────
        //
        // Delete any active clauses that still reference eliminated/substituted
        // variables. BVE's post-elimination GC (body.rs) performs a full arena
        // scan, but subsequent inprocessing passes (factor, SBVA, BCE, CCE,
        // condition, transred, sweep, decompose) can create clause mutations
        // that reintroduce eliminated-variable references. Defense-in-depth:
        // use delete_clause_checked to properly clear reason references,
        // emit proof deletions, and update watch lists before remapping.
        //
        // Reference: CaDiCaL compact.cpp:180.
        {
            let stale_indices: Vec<usize> = self
                .arena
                .active_indices()
                .filter(|&idx| {
                    self.arena
                        .literals(idx)
                        .iter()
                        .any(|lit| map.map_lit(*lit).is_none())
                })
                .collect();
            #[cfg(debug_assertions)]
            for &idx in &stale_indices {
                let lits = self.arena.literals(idx);
                for &lit in lits {
                    if map.map_lit(lit).is_none() {
                        let var = lit.variable().index();
                        let state = self.var_lifecycle.as_slice().get(var).copied();
                        let is_learned = self.arena.is_learned(idx);
                        let clause_lits: Vec<_> = lits.to_vec();
                        tracing::warn!(
                            "compact Phase 0: active clause {idx} \
                             (learned={is_learned}, len={}) contains \
                             eliminated-variable literal {lit:?} (var={var}, \
                             state={state:?}). Clause: {clause_lits:?}. \
                             Deleting before remap.",
                            clause_lits.len(),
                        );
                        break;
                    }
                }
            }
            let stale_count = stale_indices.len();
            for idx in stale_indices {
                self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
            }
            self.stats.compact_stale_clauses_deleted += stale_count as u64;
        }

        // ── Phase 2: Safety net — delete any remaining stale clauses ──
        // All stale clauses should have been deleted in Phase 0 + Phase 1.
        // This is a third layer of defense-in-depth (#8464): if any clause
        // still contains an unmapped literal, delete it gracefully instead
        // of panicking in the remap loop below.
        {
            let remap_stale: Vec<usize> = self
                .arena
                .active_indices()
                .filter(|&idx| {
                    self.arena
                        .literals(idx)
                        .iter()
                        .any(|lit| map.map_lit(*lit).is_none())
                })
                .collect();
            if !remap_stale.is_empty() {
                tracing::error!(
                    "compact: {} active clauses still contain unmapped literals \
                     after Phase 0 + Phase 1 cleanup. Deleting as Phase 2 \
                     safety net (#8464).",
                    remap_stale.len(),
                );
                for idx in remap_stale {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }

        // ── Phase 3: Remap clause literals ────────────────────────────
        // The expect() below is a hard invariant check: if any unmapped
        // literal survives all three cleanup phases, it indicates a bug.
        // Reuse persistent buffer to avoid arena-proportional allocation (#8599).
        self.cold.reduce_indices_buf.clear();
        self.cold
            .reduce_indices_buf
            .extend(self.arena.active_indices());
        for i in 0..self.cold.reduce_indices_buf.len() {
            let idx = self.cold.reduce_indices_buf[i];
            {
                let lits = self.arena.literals_mut(idx);
                for lit in lits.iter_mut() {
                    *lit = map.map_lit(*lit).expect(
                        "invariant: active clause contains eliminated-variable literal \
                             after Phase 0, Phase 1, and Phase 2 safety-net cleanup",
                    );
                }
            }
            // Arena is the sole literal storage after #3904 cutover. No
            // signature refresh needed: signatures are no longer stored —
            // consumers recompute from the (now remapped) literals.
        }

        // Invalidate GC occ list — arena indices change (#8097). Drop the
        // reuse scratch too: its stored clause indices are now stale (it is
        // cleared before every reuse, so this is hygiene, not correctness).
        self.gc_occ = None;
        self.gc_occ_scratch = None;
        self.cold.last_collect_trail_pos = 0;

        // ── Phase 2: Remap watch lists ────────────────────────────────
        // compact_watches() rebuilds watches with binary-first invariant.
        self.compact_watches(&map);

        // ── Phase 3: Remap trail ──────────────────────────────────────
        let mut new_trail = Vec::with_capacity(self.trail.len());
        for &lit in &self.trail {
            if let Some(new_lit) = map.map_lit(lit) {
                new_trail.push(new_lit);
            }
        }
        // #relevancy-frontier-incremental: variable compaction renumbers every
        // variable and rewrites the trail; the frontier cache is keyed by both.
        self.relevancy_frontier.invalidate();
        // The independent-support whitelist (solver/indep_support.rs) holds
        // raw variable indices, so compaction MUST remap it: a stale index
        // outside the new range reaches BCP as a decision literal and panics
        // the `vals` lookup. Members whose variable was eliminated drop out;
        // the whitelist only ever shrinks, so the restriction policy that
        // admitted it still holds.
        if !self.indep_support.is_empty() {
            let mut remapped = Vec::with_capacity(self.indep_support.len());
            for &old in &self.indep_support {
                if let Some(new) = map.map_var(old as usize) {
                    remapped.push(new as u32);
                }
            }
            self.indep_support = remapped;
        }
        self.trail = new_trail;
        self.qhead = self.trail.len();

        // ── Phase 3b: Clear conflict analyzer seen flags BEFORE remap ──
        // `seen_to_clear` contains OLD variable indices from the last
        // conflict analysis. Phase 4 remaps `var_data` to NEW indices.
        // If we clear AFTER remap, the old indices in `seen_to_clear`
        // operate on wrong `var_data` entries, leaving stale seen flags
        // that corrupt `counter`/`resolvent_size` in the next conflict
        // analysis (#7331).
        self.conflict.compact(&mut self.var_data);

        // ── Phase 4: Remap variable-indexed solver arrays ─────────────
        map.remap_var_vec(&mut self.var_data);
        if !self.unit_proof_id.is_empty() {
            map.remap_var_vec(&mut self.unit_proof_id);
        }
        if !self.unit_proof_sign.is_empty() {
            map.remap_var_vec(&mut self.unit_proof_sign);
        }
        map.remap_var_vec(&mut self.phase);
        map.remap_var_vec(&mut self.target_phase);
        map.remap_var_vec(&mut self.best_phase);
        map.remap_var_vec(&mut self.cold.freeze_counts);
        if !self.cold.level0_proof_id.is_empty() {
            map.remap_var_vec(&mut self.cold.level0_proof_id);
        }
        if !self.cold.level0_proof_sign.is_empty() {
            map.remap_var_vec(&mut self.cold.level0_proof_sign);
        }
        self.cold.lrat_level0_unit_materialize_cursor = 0;
        self.cold.lrat_level0_unit_materialize_pinned.clear();
        map.remap_var_vec(&mut self.cold.scope_selector_set);
        map.remap_var_vec(&mut self.glue_stamp);
        map.remap_var_vec(&mut self.shrink_stamp);
        map.remap_var_vec(&mut self.min.minimize_flags);
        map.remap_var_vec(&mut self.vivify_analyzed);

        // ── Phase 4b-pre: Fix trail_pos in var_data after remap (#8359) ──
        // Phase 3 rebuilt the trail with new literal positions, and Phase 4
        // moved var_data to new variable indices. However, remap_var_vec
        // preserved the stale trail_pos field from pre-compaction. Conflict
        // analysis reads trail_pos for ordering comparisons (minimize.rs:46,
        // analyze.rs:514), so stale values corrupt it when ChrBT creates
        // out-of-order trail entries at higher decision levels.
        for (new_pos, &lit) in self.trail.iter().enumerate() {
            let var = lit.variable().index();
            debug_assert!(
                var < map.new_num_vars,
                "BUG: trail entry at position {new_pos} has variable index {var} \
                 >= new_num_vars {} after compaction",
                map.new_num_vars,
            );
            self.var_data[var].trail_pos = new_pos as u32;
        }

        // probe_parent: variable-indexed, values are Literals.
        {
            let mut new_pp: Vec<Option<Literal>> = vec![None; map.new_num_vars];
            for old_var in 0..old_num_vars {
                if let Some(new_var) = map.map_var(old_var) {
                    new_pp[new_var] = self.probe_parent[old_var].and_then(|lit| map.map_lit(lit));
                }
            }
            self.probe_parent = new_pp;
        }

        // lambda: variable-indexed, values are ClauseRefs (arena offsets).
        // ClauseRef values are arena offsets that are remapped by arena compaction,
        // not by variable compaction. However, we must remap the variable index.
        // Lambda entries for eliminated variables are dropped. Lambda entries
        // referencing clauses that may be moved during arena GC will be validated
        // at use time (is_active check in backtrack and conflict analysis).
        {
            let mut new_lambda: Vec<Option<ClauseRef>> = vec![None; map.new_num_vars];
            for old_var in 0..old_num_vars {
                if let Some(new_var) = map.map_var(old_var) {
                    new_lambda[new_var] = self.lambda[old_var];
                }
            }
            self.lambda = new_lambda;
        }

        // stale_reasons: contains old variable indices — remap to new indices,
        // dropping entries for eliminated variables.
        if !self.stale_reasons.is_empty() {
            self.stale_reasons.retain_mut(|vi| {
                if let Some(new_var) = map.map_var(*vi as usize) {
                    *vi = new_var as u32;
                    true
                } else {
                    false
                }
            });
        }

        // ── Phase 4b: Save eliminated variables' level-0 values (#8179) ──
        //
        // CaDiCaL preserves eliminated variables' vals across compaction
        // (extend.cpp:140 reads `internal->val(ilit)` for all variables).
        // AY's Phase 5 below truncates `self.vals`, losing eliminated
        // variables' level-0 assignments. Save them in external-index
        // space so `finalize_sat` can seed ext_model correctly.
        for old_var in 0..old_num_vars {
            if !self.var_lifecycle.is_removed(old_var) {
                continue;
            }
            let ext_var = self.cold.i2e[old_var] as usize;
            if ext_var >= self.cold.eliminated_ext_vals.len() {
                self.cold.eliminated_ext_vals.resize(ext_var + 1, false);
            }
            // Read the positive-literal value from vals (literal-indexed).
            let pos_lit_idx = old_var * 2;
            let val = if pos_lit_idx < self.vals.len() {
                self.vals[pos_lit_idx] > 0
            } else {
                false
            };
            self.cold.eliminated_ext_vals[ext_var] = val;
        }

        // ── Phase 5: Remap literal-indexed arrays ─────────────────────
        map.remap_lit_vec(&mut self.vals);

        // ── Phase 6: Remap VSIDS ──────────────────────────────────────
        self.vsids.compact(&map);

        // ── Phase 7: Remap VarLifecycle ───────────────────────────────
        // All mapped variables are active by construction.
        self.var_lifecycle = lifecycle::VarLifecycle::new(map.new_num_vars);

        // ── Phase 8: Remap scope selectors ────────────────────────────
        self.cold.scope_selectors = self
            .cold
            .scope_selectors
            .iter()
            .filter_map(|v| map.map_var(v.index()).map(|nv| Variable(nv as u32)))
            .collect();

        // ── Phase 9: Conflict analyzer ────────────────────────────────
        // Seen flags already cleared in Phase 3b (before var_data remap).
        // No further remapping needed — ConflictAnalyzer doesn't store
        // variable indices persistently (seen_to_clear was cleared in 3b).

        // ── Phase 9b: Update external↔internal index tables (#5250) ──
        // CaDiCaL compact.cpp:210-233. Rebuild i2e for the compacted
        // variable space and update e2i so that external indices point
        // to the new internal indices. Eliminated variables get
        // UNMAPPED in e2i; the reconstruction stack (which stores
        // external indices) does NOT need remapping.
        {
            let mut new_i2e = vec![UNMAPPED; map.new_num_vars];
            for old_var in 0..old_num_vars {
                if let Some(new_var) = map.map_var(old_var) {
                    let ext_var = self.cold.i2e[old_var];
                    new_i2e[new_var] = ext_var;
                    self.cold.e2i[ext_var as usize] = new_var as u32;
                } else {
                    // Eliminated/substituted: mark as unmapped in e2i
                    let ext_var = self.cold.i2e[old_var];
                    if (ext_var as usize) < self.cold.e2i.len() {
                        self.cold.e2i[ext_var as usize] = UNMAPPED;
                    }
                }
            }
            self.cold.i2e = new_i2e;
        }

        // ── Phase 10: Reconstruction stack uses external indices (#5250) ──
        // No remapping needed — entries store stable external indices that
        // are never affected by internal variable compaction.
        // (Previously: self.reconstruction.compact(&map);)
        #[cfg(debug_assertions)]
        self.validate_reconstruction_stack();

        // ── Phase 11: Recreate inprocessing engines ───────────────────
        // Save accumulated stats before recreating engines with new variable count.
        let bve_stats = self.inproc.bve.stats().clone();
        let decompose_stats = self.inproc.decompose_engine.stats.clone();
        let subsume_stats = self.inproc.subsumer.stats().clone();
        let sweep_stats = self.inproc.sweeper.stats().clone();
        let transred_stats = self.inproc.transred_engine.stats().clone();
        let htr_stats = self.inproc.htr.stats().clone();
        let conditioning_stats = self.inproc.conditioning.stats().clone();
        let bce_stats = self.inproc.bce.stats().clone();
        let probe_stats = self.inproc.prober.stats().clone();
        let congruence_stats = self.inproc.congruence.stats().clone();

        self.inproc.bve = BVE::new(map.new_num_vars);
        self.inproc.bve.restore_stats(bve_stats);
        self.inproc.bce = BCE::new(map.new_num_vars);
        self.inproc.bce.restore_stats(bce_stats);
        self.inproc.subsumer = Subsumer::new(map.new_num_vars);
        self.inproc.subsumer.restore_stats(subsume_stats);
        self.subsume_dirty = vec![true; map.new_num_vars]; // all dirty after compaction
        self.dirty_watches = vec![false; map.new_num_vars * 2]; // reset after compaction
        self.dirty_watch_list.clear(); // reset after compaction
        self.l0_gc_dirty = vec![false; map.new_num_vars]; // reset after compaction
        self.inproc.sweeper = Sweeper::new(map.new_num_vars);
        self.inproc.sweeper.restore_stats(sweep_stats);
        self.inproc.prober = Prober::new(map.new_num_vars);
        self.inproc.prober.restore_stats(probe_stats);
        self.inproc.decompose_engine = Decompose::new(map.new_num_vars);
        self.inproc.decompose_engine.restore_stats(decompose_stats);
        self.inproc.factor_engine = Factor::new(map.new_num_vars);
        self.inproc.sbva_engine = crate::sbva::Sbva::new(map.new_num_vars);
        self.inproc.transred_engine = TransRed::new(map.new_num_vars);
        self.inproc.transred_engine.restore_stats(transred_stats);
        self.inproc.htr = HTR::new(map.new_num_vars);
        self.inproc.htr.restore_stats(htr_stats);
        self.inproc.conditioning = Conditioning::new(map.new_num_vars);
        self.inproc.conditioning.restore_stats(conditioning_stats);
        self.lit_marks = LitMarks::new(map.new_num_vars);
        self.inproc.congruence = CongruenceClosure::new(map.new_num_vars);
        self.inproc.congruence.restore_stats(congruence_stats);

        // Factor candidate marks are indexed by variable — must be reset
        // after compaction renumbers variables (#5172).
        self.cold.factor_candidate_marks = vec![0; map.new_num_vars];
        self.cold.factor_marked_epoch = 1;
        self.cold.factor_last_completed_epoch = 0;

        // ── Phase 12: Clear transient buffers ─────────────────────────
        self.hbr_lits.clear();
        self.min.minimize_to_clear.clear();
        self.min.lrat_to_clear.clear();
        self.vivify_analyzed_to_clear.clear();
        // Level-seen tracking is indexed by decision level, not variable —
        // clearing is sufficient (no remapping needed).
        self.clear_level_seen();

        // ── Phase 13: Forward checker ─────────────────────────────────
        // Recreate with new size, preserving sampling mode (#5625).
        if let Some(ref checker) = self.cold.forward_checker {
            let sample_period = checker.sample_period();
            self.cold.forward_checker = if sample_period > 0 {
                Some(crate::forward_checker::ForwardChecker::new_sampled(
                    map.new_num_vars,
                    sample_period,
                ))
            } else {
                Some(crate::forward_checker::ForwardChecker::new(
                    map.new_num_vars,
                ))
            };
        }

        // ── Phase 14: Solution witness ────────────────────────────────
        if let Some(ref mut witness) = self.cold.solution_witness {
            map.remap_var_vec(witness);
        }

        // ── Phase 15: Original clauses use external indices (#5250) ──
        // Original clauses were added in the initial internal space which
        // equals external space (identity mapping). With external indices,
        // they stay in external space permanently — no remapping needed.
        // (Previously: map_lit_for_reconstruction remapped to compacted space.)

        // ── Phase 16: Root-satisfied clauses use external indices (#5250) ──
        // Root-satisfied clauses are externalized at save time (condition.rs).
        // No remapping needed during compaction.
        // (Previously: map_lit_for_reconstruction remapped to compacted space.)

        // ── Post-compaction validation (#8359) ──────────────────────
        // Verify no literal with var_index >= new_num_vars survives compaction.
        #[cfg(debug_assertions)]
        {
            for (i, &lit) in self.trail.iter().enumerate() {
                debug_assert!(
                    lit.variable().index() < map.new_num_vars,
                    "BUG: trail[{i}] has variable index {} >= new_num_vars {} \
                     after compaction (lit={lit:?})",
                    lit.variable().index(),
                    map.new_num_vars,
                );
            }
            debug_assert!(
                self.phase.len() >= map.new_num_vars,
                "BUG: phase[] length {} < new_num_vars {} after compaction",
                self.phase.len(),
                map.new_num_vars,
            );
            debug_assert!(
                self.var_data.len() >= map.new_num_vars,
                "BUG: var_data[] length {} < new_num_vars {} after compaction",
                self.var_data.len(),
                map.new_num_vars,
            );
            debug_assert!(
                self.vals.len() >= map.new_num_vars * 2,
                "BUG: vals[] length {} < 2*new_num_vars {} after compaction",
                self.vals.len(),
                map.new_num_vars * 2,
            );
            // Verify trail_pos consistency after the Phase 4b-pre fixup.
            for (pos, &lit) in self.trail.iter().enumerate() {
                let var = lit.variable().index();
                debug_assert_eq!(
                    self.var_data[var].trail_pos as usize, pos,
                    "BUG: var_data[{var}].trail_pos ({}) != trail position ({pos}) \
                     after compaction trail_pos fixup (#8359)",
                    self.var_data[var].trail_pos,
                );
            }
        }

        // ── Finalize ──────────────────────────────────────────────────
        self.num_vars = map.new_num_vars;
        // Recompute ghost guard after compaction may have reduced num_vars (#8466).
        // Incremental mode (push/pop) also creates ghost literals (#8489).
        self.ghost_guard_needed =
            self.num_vars > CHRONO_LEVEL_LIMIT as usize || self.cold.has_ever_scoped;
        // user_num_vars is intentionally NOT updated during compaction.
        // It represents the external variable count (what the user/DPLL(T)
        // layer created), which is the full e2i.len(). Compaction only
        // changes internal variable indices; external indices are stable.
        // Reducing user_num_vars would truncate the returned model,
        // losing variables with high external indices (#5522).
        debug_assert!(
            !self.cold.has_been_incremental,
            "BUG: compact must not run in incremental mode"
        );
        self.target_trail_len = self.trail.len();
        self.best_trail_len = self.trail.len();

        // Schedule next compaction (CaDiCaL compact.cpp:540-541).
        self.cold.compact_count += 1;
        let delta = COMPACT_INTERVAL_BASE.saturating_mul(self.cold.compact_count + 1);
        self.cold.compact_next_conflict = self.num_conflicts.saturating_add(delta);
    }

    /// Remap watch lists during compaction.
    ///
    /// Two-phase approach (#8362):
    ///
    /// Phase A: Copy binary watch entries from old to new watch lists.
    ///   Binary watches are structural (blocker = other literal) and are
    ///   eagerly maintained, so they are always current.
    ///
    /// Phase B: Rebuild long-clause watches from the arena.
    ///   Long-clause watches can be stale: BCP lazily filters them, and
    ///   inprocessing passes (subsume/factor/sweep) may replace a clause's
    ///   watched literals without updating all watch lists. Copying stale
    ///   entries from old lists places watches under wrong (remapped) literals,
    ///   causing missing-watch assertions after compaction.
    ///
    ///   Instead, iterate active clauses with len >= 3 and attach fresh
    ///   watches at positions [0] and [1] (which were already remapped to
    ///   new literals in Phase 1 of compact()). This is O(active_clauses)
    ///   but is correct by construction.
    fn compact_watches(&mut self, map: &VariableMap) {
        let old_num_lits = self.num_vars * 2;
        let mut new_watches = WatchedLists::new(map.new_num_vars);

        // Phase A: Copy binary watch entries.
        for old_lit_idx in 0..old_num_lits {
            let old_lit = Literal::from_index(old_lit_idx);
            let new_lit = match map.map_lit(old_lit) {
                Some(nl) => nl,
                None => continue,
            };

            let wl = self.watches.get_watches(old_lit);
            let mut dst = new_watches.get_watches_mut(new_lit);
            for wi in 0..wl.len() {
                if !wl.is_binary(wi) {
                    continue; // Long-clause entries handled in Phase B.
                }
                let old_blocker = wl.blocker(wi);
                let clause_off = wl.clause_ref(wi);
                // Skip dead clauses (#8497 family, husk adjudication): Phase B
                // filters garbage/pending-garbage but Phase A previously copied
                // binary watches for garbage-kept husks verbatim, letting BCP
                // propagate through logically deleted clauses.
                if clause_off.index() >= self.arena.len() || self.arena.is_dead(clause_off.index())
                {
                    continue;
                }
                let Some(new_blocker) = map.map_lit(old_blocker) else {
                    // Other literal's variable was eliminated — stale binary watch.
                    continue;
                };
                dst.push_watcher(Watcher::binary(clause_off, new_blocker));
            }
        }

        // Also scan extension-variable watch lists (beyond num_vars) for
        // binary entries (#8135). Extension variables from BVE/SBVA may
        // still have binary watch entries that reference active clauses.
        let total_old_lists = self.watches.num_lists();
        for old_lit_idx in old_num_lits..total_old_lists {
            let old_lit = Literal::from_index(old_lit_idx);
            let new_lit = match map.map_lit(old_lit) {
                Some(nl) => nl,
                None => continue,
            };
            let wl = self.watches.get_watches(old_lit);
            let mut dst = new_watches.get_watches_mut(new_lit);
            for wi in 0..wl.len() {
                if !wl.is_binary(wi) {
                    continue;
                }
                let old_blocker = wl.blocker(wi);
                let clause_off = wl.clause_ref(wi);
                // Same dead-clause skip as the main Phase A loop above.
                if clause_off.index() >= self.arena.len() || self.arena.is_dead(clause_off.index())
                {
                    continue;
                }
                let Some(new_blocker) = map.map_lit(old_blocker) else {
                    continue;
                };
                dst.push_watcher(Watcher::binary(clause_off, new_blocker));
            }
        }

        // Phase B: Attach fresh long-clause watches from the arena.
        // Clause literals were already remapped to new indices in Phase 1
        // of compact(), so positions [0] and [1] contain the correct new
        // watched literals.
        for ci in self.arena.active_indices() {
            let clause_len = self.arena.len_of(ci);
            if clause_len < 3 {
                continue; // Binary clauses use binary watch entries only.
            }
            if self.arena.is_garbage(ci) || self.arena.is_pending_garbage(ci) {
                continue;
            }
            let cref = ClauseRef(ci as u32);
            let lit0 = self.arena.literal(ci, 0);
            let lit1 = self.arena.literal(ci, 1);
            // Use lit1 as blocker for lit0's entry and vice versa
            // (standard 2WL blocker choice).
            {
                let mut dst0 = new_watches.get_watches_mut(lit0);
                dst0.push_watcher(Watcher::new(cref, lit1));
            }
            {
                let mut dst1 = new_watches.get_watches_mut(lit1);
                dst1.push_watcher(Watcher::new(cref, lit0));
            }
        }

        self.watches = new_watches;
        // Binary-first invariant is maintained incrementally via push_watcher.
        self.watches.debug_assert_binary_first();
    }
}

#[cfg(test)]
#[path = "compact_tests.rs"]
mod tests;
