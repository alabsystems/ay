// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof ID queries and level-0 unit chain collection.
//!
//! Proof ID lookup (unit, level-0, cached), BFS transitive closure on
//! level-0 variables, and reverse-trail unit chain collection for LRAT
//! hint construction. Extracted from `conflict_analysis_lrat.rs` to keep
//! each file under 500 lines.

use super::*;
use crate::kani_compat::DetHashSet;

impl Solver {
    /// Reverse LRAT hints and drop zeros.
    ///
    /// LRAT checkers consume hints in listed order, while AY collects them in
    /// analysis order, so we reverse first. Deduplication of duplicate clause
    /// IDs is handled at the proof output boundary in `ProofManager::emit_add`
    /// (#5248), not here — post-hoc dedup at this level breaks multi-stage
    /// ordering that the LRAT checker requires (#5194). Sentinel value 0 is
    /// filtered.
    pub(super) fn lrat_reverse_hints(hints: &[u64]) -> Vec<u64> {
        hints.iter().rev().copied().filter(|&h| h != 0).collect()
    }

    #[inline]
    pub(crate) fn unit_proof_id_of_var_index(&self, var_index: usize) -> Option<u64> {
        self.unit_proof_id
            .get(var_index)
            .copied()
            .filter(|&id| id != 0)
    }

    #[inline]
    pub(crate) fn record_unit_proof_id_for_lit(&mut self, lit: Literal, proof_id: u64) {
        let var_index = lit.variable().index();
        if var_index < self.unit_proof_id.len() {
            self.unit_proof_id[var_index] = proof_id;
            self.unit_proof_sign[var_index] = if proof_id == 0 { 0 } else { lit.sign_i8() };
            self.pin_lrat_level0_unit_materialize_for_var(var_index);
        }
    }

    #[inline]
    pub(crate) fn record_level0_proof_id_for_lit(&mut self, lit: Literal, proof_id: u64) {
        let var_index = lit.variable().index();
        if var_index < self.cold.level0_proof_id.len() {
            self.cold.level0_proof_id[var_index] = proof_id;
            self.cold.level0_proof_sign[var_index] = if proof_id == 0 { 0 } else { lit.sign_i8() };
            self.pin_lrat_level0_unit_materialize_for_var(var_index);
        }
    }

    /// Mark a level-0 variable's trail slot as needing a (re-)materialization
    /// attempt. Pre-#A5 this lowered the scalar materialize cursor, forcing a
    /// re-walk of every slot after it; now the slot is pinned individually and
    /// the high-water cursor never moves backward for a single variable.
    #[inline]
    pub(super) fn pin_lrat_level0_unit_materialize_for_var(&mut self, var_index: usize) {
        if !self.cold.lrat_enabled
            || var_index >= self.num_vars
            || self.var_data[var_index].level != 0
            || !self.var_is_assigned(var_index)
        {
            return;
        }
        let trail_pos = self.var_data[var_index].trail_pos as usize;
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        if trail_pos >= level0_end || trail_pos >= self.cold.lrat_level0_unit_materialize_cursor {
            // Never attempted yet: the next scan's fresh range covers it.
            return;
        }
        let pinned = &mut self.cold.lrat_level0_unit_materialize_pinned;
        let idx = pinned.partition_point(|&p| p < trail_pos);
        if pinned.get(idx) != Some(&trail_pos) {
            pinned.insert(idx, trail_pos);
        }
    }

    /// Clamp the level-0 materialization high-water cursor to `pos` and drop
    /// pinned retry slots at or above the new cursor: after a trail shrink or
    /// compaction those positions no longer describe the same literals, and
    /// the fresh range of the next scan covers them (#A5).
    #[inline]
    pub(super) fn clamp_lrat_level0_unit_materialize_cursor(&mut self, pos: usize) {
        let cursor = self.cold.lrat_level0_unit_materialize_cursor.min(pos);
        self.cold.lrat_level0_unit_materialize_cursor = cursor;
        let pinned = &mut self.cold.lrat_level0_unit_materialize_pinned;
        let keep = pinned.partition_point(|&p| p < cursor);
        pinned.truncate(keep);
    }

    #[inline]
    pub(crate) fn lrat_hint_id_visible(&self, clause_id: u64) -> bool {
        if clause_id == 0 || !self.cold.lrat_enabled {
            return clause_id != 0;
        }
        match self.proof_manager.as_ref() {
            Some(manager) => manager.lrat_id_visible_in_file(clause_id),
            None => true,
        }
    }

    #[inline]
    pub(crate) fn visible_unit_proof_id_for_lit(&self, lit: Literal) -> Option<u64> {
        let var_index = lit.variable().index();
        let id = self.unit_proof_id.get(var_index).copied().unwrap_or(0);
        let sign = self.unit_proof_sign.get(var_index).copied().unwrap_or(0);
        (id != 0 && sign == lit.sign_i8() && self.lrat_hint_id_visible(id)).then_some(id)
    }

    #[inline]
    fn visible_level0_proof_id_for_lit(&self, lit: Literal) -> Option<u64> {
        let var_index = lit.variable().index();
        let id = self
            .cold
            .level0_proof_id
            .get(var_index)
            .copied()
            .unwrap_or(0);
        let sign = self
            .cold
            .level0_proof_sign
            .get(var_index)
            .copied()
            .unwrap_or(0);
        (id != 0 && sign == lit.sign_i8() && self.lrat_hint_id_visible(id)).then_some(id)
    }

    #[inline]
    fn assigned_level0_lit(&self, var_index: usize) -> Option<Literal> {
        if var_index >= self.num_vars
            || self.var_data[var_index].level != 0
            || !self.var_is_assigned(var_index)
        {
            return None;
        }
        let variable = Variable::new(var_index as u32);
        if self.lit_val(Literal::positive(variable)) > 0 {
            Some(Literal::positive(variable))
        } else {
            Some(Literal::negative(variable))
        }
    }

    #[inline]
    pub(super) fn cached_conflict_clause_id(&self, conflict_ref: ClauseRef) -> u64 {
        let direct = self.clause_id(conflict_ref);
        if direct != 0 {
            return direct;
        }
        if self.last_conflict_clause_ref == Some(conflict_ref) {
            return self.last_conflict_clause_id;
        }
        0
    }

    /// Check if a variable has an LRAT proof ID preserved by ClearLevel0.
    ///
    /// When BVE deletes a reason clause via ClearLevel0, `reason[vi]` is set
    /// to None but `level0_proof_id[vi]` preserves the clause ID for LRAT
    /// chain construction (#4617).
    #[inline]
    pub(super) fn has_level0_proof_id(&self, var_index: usize) -> bool {
        var_index < self.cold.level0_proof_id.len() && self.cold.level0_proof_id[var_index] != 0
    }

    /// Check whether a level-0 variable has LRAT provenance from any source:
    /// reason clause, visible unit_proof_id, or visible level0_proof_id
    /// (#6257, #6270).
    ///
    /// Use this as the BFS seed/expansion condition for LRAT hint collection.
    /// After #6257, unit clauses are enqueued with reason=None but their proof
    /// ID is stored in unit_proof_id, so `reason[vi].is_some() ||
    /// has_level0_proof_id(vi)` is insufficient.
    #[inline]
    pub(super) fn has_any_proof_id(&self, var_index: usize) -> bool {
        // #8467: a lazy theory reason stores a table index in `reason`, not an
        // arena offset — it carries no proof-bearing clause, so it must not
        // count as a clause reason here.
        let vd = self.var_data[var_index];
        let has_clause_reason = is_clause_reason(vd.reason) && !vd.is_lazy_theory_reason();
        if self.cold.lrat_enabled {
            let signed_proof = self.assigned_level0_lit(var_index).is_some_and(|lit| {
                self.visible_unit_proof_id_for_lit(lit).is_some()
                    || self.visible_level0_proof_id_for_lit(lit).is_some()
            });
            has_clause_reason || signed_proof
        } else {
            has_clause_reason
                || (var_index < self.unit_proof_id.len() && self.unit_proof_id[var_index] != 0)
                || self.has_level0_proof_id(var_index)
        }
    }

    /// Get the LRAT proof ID for a level-0 variable.
    ///
    /// In LRAT mode, does NOT fall back to multi-literal reason clause IDs.
    /// Using a multi-literal reason as a hint causes RUP failure because the
    /// hint clause has 2+ non-falsified literals under the RUP assumption.
    /// Callers should still prefer `ensure_level0_unit_proof_ids()` so that
    /// level-0 implied variables have materialized unit proofs. As a fallback,
    /// this method accepts unit reason clauses directly when no materialized
    /// proof ID exists yet (#7108).
    ///
    /// In non-LRAT mode (DRAT), prefers reason clause IDs for RUP compatibility.
    #[inline]
    pub(super) fn level0_var_proof_id(&self, var_index: usize) -> Option<u64> {
        if self.cold.lrat_enabled {
            return self
                .assigned_level0_lit(var_index)
                .and_then(|lit| self.level0_var_proof_id_for_lit(lit));
        }
        self.level0_var_proof_id_for_var_index_unsafely(var_index)
    }

    #[inline]
    pub(super) fn level0_var_proof_id_for_lit(&self, lit: Literal) -> Option<u64> {
        let var_index = lit.variable().index();
        if self.cold.lrat_enabled {
            // LRAT mode: only return unit clause proof IDs.
            if self.lit_value(lit) != Some(true) || self.var_data[var_index].level != 0 {
                return None;
            }
            if let Some(id) = self.visible_level0_proof_id_for_lit(lit) {
                return Some(id);
            }
            if let Some(pid) = self.visible_unit_proof_id_for_lit(lit) {
                return Some(pid);
            }
            // Fall back to reason clause ID ONLY for unit clauses (len 1).
            // Multi-literal reasons are rejected because they have 2+
            // non-falsified literals under RUP assumption. Unit clauses
            // have exactly one literal and are valid LRAT hints (#7108).
            // #8467: lazy theory reasons are table indexes, not arena offsets.
            let reason_raw = self.var_data[var_index].reason;
            if is_clause_reason(reason_raw) && !self.var_data[var_index].is_lazy_theory_reason() {
                let ci = reason_raw as usize;
                if ci < self.arena.len() && self.arena.len_of(ci) == 1 {
                    if self.arena.literal(ci, 0) != lit {
                        return None;
                    }
                    let id = self.clause_id(ClauseRef(reason_raw));
                    if self.lrat_hint_id_visible(id) {
                        return Some(id);
                    }
                }
            }
            None
        } else {
            self.level0_var_proof_id_for_var_index_unsafely(var_index)
        }
    }

    #[inline]
    fn level0_var_proof_id_for_var_index_unsafely(&self, var_index: usize) -> Option<u64> {
        if self.cold.lrat_enabled {
            self.assigned_level0_lit(var_index)
                .and_then(|lit| self.level0_var_proof_id_for_lit(lit))
        } else {
            // DRAT mode: reason clause → level0_proof_id → unit_proof_id.
            // #8467: lazy theory reasons are table indexes, not arena offsets.
            let reason_raw = self.var_data[var_index].reason;
            if is_clause_reason(reason_raw) && !self.var_data[var_index].is_lazy_theory_reason() {
                let id = self.clause_id(ClauseRef(reason_raw));
                if id != 0 {
                    return Some(id);
                }
            }
            if self.has_level0_proof_id(var_index) {
                return Some(self.cold.level0_proof_id[var_index]);
            }
            if let Some(pid) = self.unit_proof_id_of_var_index(var_index) {
                return Some(pid);
            }
            None
        }
    }

    /// Check if a variable's reason clause is satisfied by the RUP assumption.
    ///
    /// Returns `true` if the reason clause (or the variable itself for deleted
    /// reason clauses) contains a literal from `rup_satisfied`. Such hint
    /// clauses must be excluded from LRAT chains (#5026).
    fn is_reason_rup_satisfied(&self, var_idx: usize, rup_satisfied: &DetHashSet<Literal>) -> bool {
        if rup_satisfied.is_empty() {
            return false;
        }
        if let Some(reason_ref) = self.var_reason(var_idx) {
            let ci = reason_ref.0 as usize;
            let clen = self.arena.len_of(ci);
            for j in 0..clen {
                if rup_satisfied.contains(&self.arena.literal(ci, j)) {
                    return true;
                }
            }
            false
        } else {
            // No reason clause (ClearLevel0 or decision). Check if the variable
            // itself is referenced by rup_satisfied (its original reason clause
            // was deleted but would have contained the satisfied literal).
            rup_satisfied
                .iter()
                .any(|&sl| sl.variable().index() == var_idx)
        }
    }

    /// Phase 1 only: BFS transitive closure on level-0 variables.
    ///
    /// Seeds must already be marked with `LRAT_A` in `minimize_flags` and pushed
    /// to `lrat_to_clear`. After return, `minimize_flags[v] & LRAT_A != 0` for
    /// all transitively reachable level-0 variables and their indices are in
    /// `lrat_to_clear`.
    ///
    /// Variables marked with `LRAT_B` are excluded from BFS expansion (used by
    /// replace_clause to skip new clause literals the RUP checker already knows).
    ///
    /// Does NOT clean up `LRAT_A` or `lrat_to_clear`; caller is responsible.
    fn bfs_level0_transitive_closure(&mut self) {
        let num_vars = self.var_data.len();
        let mut head = 0;
        while head < self.min.lrat_to_clear.len() {
            let vi = self.min.lrat_to_clear[head];
            head += 1;
            let Some(reason_ref) = self.var_reason(vi) else {
                // Include ClearLevel0 victims whose reason was cleared by BVE —
                // no clause to BFS through, but level0_proof_id preserves the
                // clause ID for Phase 2 (#4617, #5014).
                continue;
            };
            let ci = reason_ref.0 as usize;
            if ci >= self.arena.len() {
                continue;
            }
            let clen = self.arena.len_of(ci);
            for i in 0..clen {
                let reason_lit = self.arena.literal(ci, i);
                let rv = reason_lit.variable().index();
                if rv != vi
                    && rv < num_vars
                    && self.var_data[rv].level == 0
                    && self.min.minimize_flags[rv] & (LRAT_A | LRAT_B) == 0
                    && self.has_any_proof_id(rv)
                {
                    self.min.minimize_flags[rv] |= LRAT_A;
                    self.min.lrat_to_clear.push(rv);
                }
            }
        }
    }

    /// BFS transitive closure on level-0 variables, then reverse-trail scan
    /// to collect LRAT proof IDs in RUP processing order.
    ///
    /// **Protocol:** Before calling, the caller must:
    /// 1. Mark seed variables: `minimize_flags[v] |= LRAT_A` for each seed.
    /// 2. Push seeds into `lrat_to_clear` (used as BFS queue + cleanup list).
    /// 3. Optionally mark exclusions with `minimize_flags[v] |= LRAT_B` (e.g.,
    ///    new clause literals in replace_clause that the RUP checker already knows).
    ///    Caller is responsible for `LRAT_B` cleanup afterward.
    ///
    /// Returns proof IDs in reverse-trail order (ready for LRAT hint chain).
    /// Cleans up `LRAT_A` and `lrat_to_clear` before returning.
    ///
    /// CaDiCaL reference: analyze.cpp:253-268 (analyze_literal) + 1240-1246.
    pub(super) fn collect_level0_unit_chain(&mut self) -> Vec<u64> {
        let mut chain: Vec<u64> = Vec::new();
        self.emit_level0_unit_chain_filtered(None, |_, id| chain.push(id));
        chain
    }

    /// Shared implementation for callers that need a materialized unit chain.
    /// Runs BFS Phase 1, then Phase 2 reverse-trail scan with an optional
    /// RUP-satisfied filter (#5271 dedup).
    ///
    /// When `rup_satisfied` is empty the filter is a no-op
    /// (`is_reason_rup_satisfied` short-circuits on empty sets).
    pub(super) fn collect_level0_unit_chain_filtered(
        &mut self,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Vec<u64> {
        let mut chain: Vec<u64> = Vec::new();
        self.emit_level0_unit_chain_filtered(Some(rup_satisfied), |_, id| chain.push(id));
        chain
    }

    #[inline]
    fn lrat_unit_chain_root_scan_window(&self, level0_end: usize) -> (usize, usize) {
        let mut saw_marked = false;
        let mut min_pos = usize::MAX;
        let mut max_pos = 0usize;

        for &var_idx in &self.min.lrat_to_clear {
            if var_idx >= self.var_data.len() || self.min.minimize_flags[var_idx] & LRAT_A == 0 {
                continue;
            }

            let trail_pos = self.var_data[var_idx].trail_pos as usize;
            if trail_pos >= level0_end || self.trail[trail_pos].variable().index() != var_idx {
                return (0, level0_end);
            }

            saw_marked = true;
            min_pos = min_pos.min(trail_pos);
            max_pos = max_pos.max(trail_pos);
        }

        if saw_marked {
            (min_pos, max_pos + 1)
        } else {
            (0, 0)
        }
    }

    /// Run BFS Phase 1, then Phase 2 reverse-trail scan, emitting each
    /// selected unit proof ID in chain order. This lets hot conflict analysis
    /// append directly to its persistent proof buffer without materializing a
    /// temporary `Vec<u64>`.
    fn emit_level0_unit_chain_filtered<F>(
        &mut self,
        rup_satisfied: Option<&DetHashSet<Literal>>,
        mut emit: F,
    ) where
        F: FnMut(&mut Self, u64),
    {
        let num_vars = self.var_data.len();
        let record_lrat_stats = self.cold.lrat_enabled;
        if record_lrat_stats {
            self.stats.lrat_unit_chain_calls += 1;
        }

        // Phase 1: BFS transitive closure on level-0 variables.
        self.bfs_level0_transitive_closure();

        // Phase 2: Scan the trail in REVERSE order for level-0 variables.
        // Collect proof IDs via 3-tier fallback: reason → unit_proof_id → level0_proof_id.
        //
        // RUP-satisfied filter (#5026): Skip hints whose clause is trivially
        // satisfied by the RUP assumption — strict checkers reject such hints.
        //
        // LRAT vs DRAT distinction (#7108): In DRAT mode, level0_var_proof_id
        // may return multi-literal reason clause IDs, and the reason clause may
        // contain a literal satisfied by the RUP assumption. In LRAT mode,
        // level0_var_proof_id returns unit proof IDs (single-literal clauses).
        // A unit clause [x] is RUP-satisfied only if x itself is in
        // rup_satisfied — not if the original reason clause contains a
        // satisfied literal. Checking the reason clause incorrectly filters
        // out unit hints that are necessary for the chain.
        // CaDiCaL reference: analyze.cpp unit_chain has no RUP filter — unit
        // IDs are always included unconditionally.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let (scan_start, scan_end) = self.lrat_unit_chain_root_scan_window(level0_end);
        if record_lrat_stats {
            self.stats.lrat_unit_chain_root_trail_entries += (scan_end - scan_start) as u64;
        }
        let mut emitted_hints = 0_u64;
        for i in (scan_start..scan_end).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx < num_vars && self.min.minimize_flags[var_idx] & LRAT_A != 0 {
                // In LRAT mode, the hint is a unit clause [lit]. Check if lit
                // itself is RUP-satisfied (already true under the RUP assumption).
                // If so, skip it — the checker already knows this variable.
                // In DRAT mode, check if the reason clause is RUP-satisfied.
                let skip = match rup_satisfied {
                    None => false,
                    Some(rup_satisfied) if self.cold.lrat_enabled => {
                        // Unit clause [lit] is satisfied if lit ∈ rup_satisfied.
                        rup_satisfied.contains(&lit)
                    }
                    Some(rup_satisfied) => self.is_reason_rup_satisfied(var_idx, rup_satisfied),
                };
                if !skip {
                    // Hidden TrustedTransform units are never valid external
                    // LRAT hints because ProofManager strips them from the
                    // file output. Callers must materialize visible unit
                    // proofs before collecting a chain that needs them.
                    if let Some(id) = self.level0_var_proof_id(var_idx) {
                        if record_lrat_stats {
                            emitted_hints += 1;
                        }
                        emit(self, id);
                    } else if record_lrat_stats {
                        self.stats.lrat_unit_chain_missing_hints += 1;
                    }
                }
            }
        }
        if record_lrat_stats {
            self.stats.lrat_unit_chain_hints += emitted_hints;
            self.stats.lrat_unit_chain_max_hints =
                self.stats.lrat_unit_chain_max_hints.max(emitted_hints);
        }

        // Sparse cleanup: reset only touched indices.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
    }

    /// Append LRAT unit chain for conflict analysis learned clause.
    ///
    /// Seeds `LRAT_A` in `minimize_flags` from `level0_vars`, then delegates to
    /// `collect_level0_unit_chain_filtered` with the RUP-satisfied filter.
    /// Collected proof IDs are appended to `self.conflict` chain.
    ///
    /// CaDiCaL reference: analyze.cpp:253-268 (analyze_literal) + 1240-1246.
    pub(super) fn append_lrat_unit_chain(
        &mut self,
        level0_vars: &[usize],
        rup_satisfied: &DetHashSet<Literal>,
    ) {
        // CaDiCaL analyze.cpp:433: all level-0 vars must actually be at level 0
        debug_assert!(
            level0_vars
                .iter()
                .all(|&v| v < self.var_data.len() && self.var_data[v].level == 0),
            "BUG: append_lrat_unit_chain called with non-level-0 variable"
        );
        let num_vars = self.var_data.len();
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let mut fast_path_units: Vec<(usize, Literal, u64)> = Vec::new();
        let mut can_fast_path = self.cold.lrat_enabled;

        // Seed LRAT_A from level0_vars.
        for &v in level0_vars {
            if v < num_vars && self.min.minimize_flags[v] & LRAT_A == 0 {
                self.min.minimize_flags[v] |= LRAT_A;
                self.min.lrat_to_clear.push(v);
                if can_fast_path {
                    let Some(lit) = self.assigned_level0_lit(v) else {
                        can_fast_path = false;
                        continue;
                    };
                    let trail_pos = self.var_data[v].trail_pos as usize;
                    if trail_pos >= level0_end || self.trail[trail_pos] != lit {
                        can_fast_path = false;
                        continue;
                    }
                    let Some(id) = self.visible_unit_proof_id_for_lit(lit) else {
                        can_fast_path = false;
                        continue;
                    };
                    fast_path_units.push((trail_pos, lit, id));
                }
            }
        }

        // After materialization, the common case is that every seed already
        // has its own visible unit clause. Then the transitive BFS is redundant:
        // the checker can use those standalone unit IDs directly.
        if can_fast_path {
            fast_path_units.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));

            self.stats.lrat_unit_chain_calls += 1;
            let mut emitted_hints = 0_u64;
            for (_, lit, id) in fast_path_units {
                if rup_satisfied.is_empty() || !rup_satisfied.contains(&lit) {
                    emitted_hints += 1;
                    self.conflict.add_to_chain(id);
                }
            }
            self.stats.lrat_unit_chain_hints += emitted_hints;
            self.stats.lrat_unit_chain_max_hints =
                self.stats.lrat_unit_chain_max_hints.max(emitted_hints);

            for &idx in &self.min.lrat_to_clear {
                self.min.minimize_flags[idx] &= !LRAT_A;
            }
            self.min.lrat_to_clear.clear();
            return;
        }

        // Append directly to the persistent conflict proof chain while
        // preserving the same BFS + reverse-trail-scan hint order (#5271).
        self.emit_level0_unit_chain_filtered(Some(rup_satisfied), |solver, id| {
            solver.conflict.add_to_chain(id)
        });
    }

    /// Materialize level-0 unit proof IDs before LRAT hint collection.
    ///
    /// Alias for `materialize_level0_unit_proofs`. Called by probe, backbone,
    /// condition, and decompose before hint collection to ensure all level-0
    /// implied variables have proper unit proof IDs (#7108).
    pub(super) fn ensure_level0_unit_proof_ids(&mut self) {
        self.materialize_level0_unit_proofs();
    }
}
