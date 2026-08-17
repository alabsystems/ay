// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof chain computation for clause minimization.
//!
//! Extracted from conflict_analysis_minimize.rs for code-health (500-line limit).
//! Contains: compute_lrat_chain_for_removed_literals, level0 proof ID helpers,
//! materialize_level0_minimize_unit_proofs, materialize_level0_unit_proofs,
//! with DFS traversal in `conflict_analysis_minimize_lrat/minimize_dfs.rs`.
//!
//! CaDiCaL reference: `calculate_minimize_chain()` in minimize.cpp:155-199,
//! called from `shrink_and_minimize_clause()` in shrink.cpp:462-486.

mod minimize_dfs;

use super::*;

impl Solver {
    /// Compute the LRAT proof chain for literals removed during shrink/minimize.
    ///
    /// CaDiCaL reference: `calculate_minimize_chain()` in minimize.cpp:155-199,
    /// called from `shrink_and_minimize_clause()` in shrink.cpp:462-486.
    ///
    /// Algorithm: For each literal in the original clause that is NOT in the final
    /// (shrunk/minimized) clause, walk backward through the reason graph using
    /// DFS post-order, collecting all transitive reason clause IDs.
    ///
    /// Returns the variable indices of level-0 units discovered during DFS.
    /// CaDiCaL routes these to `unit_chain` (not `mini_chain`) so they appear
    /// first in the LRAT hint list after global reversal (#7108).
    pub(super) fn compute_lrat_chain_for_removed_literals(
        &mut self,
        original_learned: &[Literal],
    ) -> Vec<usize> {
        self.stats.lrat_removed_literal_chain_calls += 1;

        // Build set of variables in the final learned clause (post-shrink/minimize).
        // Uses LRAT_A bit in minimize_flags as reusable "in_final" bitmap (#5089, #4579).
        let final_count = self.conflict.learned_count();
        let uip_var = self.conflict.asserting_literal().variable().index();
        let num_vars = self.var_data.len();
        self.min.minimize_flags[uip_var] |= LRAT_A;
        self.min.lrat_to_clear.push(uip_var);
        for i in 0..final_count {
            let lit = self.conflict.learned_at(i);
            let vi = lit.variable().index();
            if vi < num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        // Check if any literals were removed
        let has_removed = original_learned.iter().any(|lit| {
            let vi = lit.variable().index();
            vi < num_vars && self.min.minimize_flags[vi] & LRAT_A == 0
        });
        if !has_removed {
            // Clean up LRAT_A before returning
            for &idx in &self.min.lrat_to_clear {
                self.min.minimize_flags[idx] &= !LRAT_A;
            }
            self.min.lrat_to_clear.clear();
            return Vec::new();
        }

        self.materialize_level0_minimize_unit_proofs();

        // Seed LRAT_B (visited) from LRAT_A (in_final): final clause
        // variables are pre-visited so DFS skips their reason subgraphs.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] |= LRAT_B;
        }

        // CaDiCaL minimize.cpp:155-199: level-0 units go to unit_chain, not
        // mini_chain. Collect them separately and return to the caller for
        // merging into the main level-0 variable set (#7108).
        let mut level0_vars = Vec::new();
        let minimize_chain = self.dfs_minimize_chain(original_learned, num_vars, &mut level0_vars);

        // Clean up both LRAT bits using sparse list
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
            self.min.minimize_flags[idx] &= !LRAT_B;
        }
        self.min.lrat_to_clear.clear();

        // Append in reverse: chain is in topological order (deepest first),
        // and add_learned_clause() reverses the entire resolution chain.
        for &id in minimize_chain.iter().rev() {
            self.conflict.add_to_chain(id);
        }

        level0_vars
    }

    /// Prefer a materialized level-0 unit proof over the raw reason clause
    /// when building removed-literal minimize chains.
    ///
    /// In LRAT mode, does NOT fall back to multi-literal reason clause IDs.
    /// Using a multi-literal reason as a hint causes RUP failure because the
    /// hint has 2+ non-falsified literals under the RUP assumption (#7108).
    /// In non-LRAT mode (DRAT), reason clause fallback is safe.
    #[inline]
    pub(super) fn level0_minimize_chain_proof_id(&self, var_index: usize) -> Option<u64> {
        if self.cold.lrat_enabled {
            return self.level0_var_proof_id(var_index);
        }
        if let Some(id) = self.level0_var_proof_id(var_index) {
            return Some(id);
        }
        // #8467: lazy theory reasons are table indexes, not arena offsets.
        let reason_raw = self.var_data[var_index].reason;
        let omission = if !is_clause_reason(reason_raw) {
            Some(crate::HintOmission::NotClauseReason)
        } else if self.var_data[var_index].is_lazy_theory_reason() {
            Some(crate::HintOmission::LazyTheoryReason)
        } else {
            let id = self.clause_id(ClauseRef(reason_raw));
            if id != 0 {
                self.record_hint_lookup(None);
                return Some(id);
            }
            Some(crate::HintOmission::ZeroClauseId)
        };
        // Introspection: an unhinted literal cannot be resolved away downstream,
        // which is what turns a reconstructed clause into a strict superclause
        // of its target and forces the `trust` fallback.
        self.record_hint_lookup(omission);
        None
    }

    #[inline]
    pub(super) fn level0_minimize_chain_proof_id_for_lit(&self, lit: Literal) -> Option<u64> {
        let var_index = lit.variable().index();
        if self.cold.lrat_enabled {
            return self.level0_var_proof_id_for_lit(lit);
        }
        if let Some(id) = self.level0_var_proof_id(var_index) {
            return Some(id);
        }
        // #8467: lazy theory reasons are table indexes, not arena offsets.
        let reason_raw = self.var_data[var_index].reason;
        let omission = if !is_clause_reason(reason_raw) {
            Some(crate::HintOmission::NotClauseReason)
        } else if self.var_data[var_index].is_lazy_theory_reason() {
            Some(crate::HintOmission::LazyTheoryReason)
        } else {
            let id = self.clause_id(ClauseRef(reason_raw));
            if id != 0 {
                self.record_hint_lookup(None);
                return Some(id);
            }
            Some(crate::HintOmission::ZeroClauseId)
        };
        // Introspection: an unhinted literal cannot be resolved away downstream,
        // which is what turns a reconstructed clause into a strict superclause
        // of its target and forces the `trust` fallback.
        self.record_hint_lookup(omission);
        None
    }

    /// Forward a level-0 hint-lookup outcome to the clause trace, when tracing
    /// is enabled. No-op (and no cost beyond an `Option` check) otherwise.
    #[inline]
    pub(super) fn record_hint_lookup(&self, omission: Option<crate::HintOmission>) {
        if let Some(trace) = self.cold.clause_trace.as_ref() {
            trace.record_hint_lookup(omission);
        }
    }

    /// Charge `units` of search-time proof bookkeeping work against the #A2b
    /// construction budget. Returns `false` once the budget is exhausted; the
    /// exhausting call marks the clause trace `proof_work_exhausted` so
    /// downstream certificate reconstruction fails closed (verdict kept,
    /// honest "no proof certificate emitted" warning). Unbudgeted (`None`,
    /// all explicit proof modes) always returns `true`.
    pub(super) fn charge_proof_bookkeeping(&mut self, units: u64) -> bool {
        let Some(remaining) = self.cold.proof_bookkeeping_budget else {
            return true;
        };
        if remaining == 0 {
            return false;
        }
        if remaining <= units {
            self.cold.proof_bookkeeping_budget = Some(0);
            if let Some(trace) = self.cold.clause_trace.as_mut() {
                trace.mark_proof_work_exhausted();
            }
            tracing::warn!(
                "search-time proof bookkeeping work budget exhausted; \
                 synthesized-default certificate will not be reconstructed \
                 (verdict unaffected)"
            );
            return false;
        }
        self.cold.proof_bookkeeping_budget = Some(remaining - units);
        true
    }

    /// Mirror a proof-only derived unit into `ClauseTrace`.
    ///
    /// Level-0 materialization emits a standalone unit through the LRAT proof
    /// manager without inserting that unit into the clause arena.  The unit ID
    /// can later replace a cleared reason in a terminal conflict chain, so the
    /// in-memory trace must retain the same clause and its complete derivation.
    /// Otherwise the terminal chain names an ID the independent positive-RUP
    /// replay cannot resolve and must be discarded.
    #[inline]
    fn trace_materialized_level0_unit(&mut self, unit_id: u64, unit_lit: Literal, hints: &[u64]) {
        if unit_id == 0 || self.cold.clause_trace.is_none() {
            return;
        }

        // Match the deterministic trace-add charge used by ordinary clause DB
        // insertion.  If the budget exhausts, the trace is poisoned before the
        // entry is appended and all certificate consumers still fail closed.
        let units = 4_u64
            .saturating_add((hints.len() as u64).saturating_mul(8))
            .saturating_add(16);
        if !self.charge_proof_bookkeeping(units) {
            return;
        }
        if let Some(trace) = self.cold.clause_trace.as_mut() {
            trace.add_clause_with_hint_slices(unit_id, &[unit_lit], false, hints);
        }
    }

    /// Materialize derived unit proof IDs for level-0 reason clauses before
    /// removed-literal minimize-chain DFS runs.
    ///
    /// The DFS records level-0 antecedents via proof IDs, not raw implication
    /// clauses. Walking the root-level trail in assignment order gives a
    /// topological order of level-0 implications, so each derived unit can be
    /// emitted after the proof IDs of the falsified literals in its reason are
    /// already available.
    pub(super) fn materialize_level0_minimize_unit_proofs(&mut self) {
        if !self.cold.lrat_enabled {
            return;
        }

        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let start = self
            .cold
            .lrat_level0_unit_materialize_cursor
            .min(level0_end);
        // #A2b search-time construction budget: once exhausted, this is a
        // no-op (the certificate is already forfeit; see charge below).
        if self.cold.proof_bookkeeping_budget == Some(0) {
            return;
        }
        // #A5 (cursor, pinned) de-pinning: retry only the individually pinned
        // slots below the high-water cursor, then walk the fresh suffix.
        // Already-materialized prefixes are never re-walked; per-call work is
        // O(|pinned| + new entries) instead of O(suffix after the oldest pin).
        let mut pinned = std::mem::take(&mut self.cold.lrat_level0_unit_materialize_pinned);
        let retry_len = pinned.partition_point(|&p| p < start);
        // #A2b charge parity (same principle as the A2 v2 memoization): the
        // pre-#A5 scalar cursor would have restarted this scan at the oldest
        // pending slot. The waste charge below must fire at the same calls
        // with the same magnitudes as before, so budgeted (synthesized-
        // default) runs exhaust at the same point they always did.
        let legacy_start = pinned.first().copied().unwrap_or(start).min(level0_end);
        self.stats.lrat_materialize_minimize_calls += 1;
        self.stats.lrat_materialize_minimize_root_trail_entries +=
            (retry_len + (level0_end - start)) as u64;
        let mut hints = std::mem::take(&mut self.cold.lrat_materialize_hints_buf);
        // Surviving pins are compacted in place: the write index never
        // overtakes the retry read index, and slots at or past `retry_len`
        // are stale (at or past `start`) and dropped by the final truncate.
        let mut kept = 0usize;
        macro_rules! keep_pinned {
            ($i:expr) => {{
                if kept < pinned.len() {
                    pinned[kept] = $i;
                } else {
                    pinned.push($i);
                }
                kept += 1;
            }};
        }
        for slot in 0..retry_len + (level0_end - start) {
            let i = if slot < retry_len {
                pinned[slot]
            } else {
                start + (slot - retry_len)
            };
            let unit_lit = self.trail[i];
            let var_idx = unit_lit.variable().index();
            if var_idx >= self.num_vars
                || self.var_data[var_idx].level != 0
                || self.level0_minimize_chain_proof_id(var_idx).is_some()
            {
                continue;
            }

            let Some(reason_ref) = self.var_reason(var_idx) else {
                continue;
            };
            let clause_idx = reason_ref.0 as usize;
            if clause_idx >= self.arena.len() {
                keep_pinned!(i);
                continue;
            }
            let clause_len = self.arena.len_of(clause_idx);
            if !(0..clause_len).any(|j| self.arena.literal(clause_idx, j) == unit_lit) {
                self.stats.lrat_materialize_minimize_incomplete_chains += 1;
                keep_pinned!(i);
                continue;
            }

            let reason_id = self.clause_id(reason_ref);
            if reason_id == 0 || !self.lrat_hint_id_visible(reason_id) {
                self.stats.lrat_materialize_minimize_incomplete_chains += 1;
                keep_pinned!(i);
                continue;
            }

            if clause_len <= 1 {
                self.record_level0_proof_id_for_lit(unit_lit, reason_id);
                self.record_unit_proof_id_for_lit(unit_lit, reason_id);
                continue;
            }

            hints.clear();
            if hints.capacity() < clause_len {
                hints.reserve(clause_len - hints.capacity());
            }
            let mut complete = true;
            for j in 0..clause_len {
                let other_lit = self.arena.literal(clause_idx, j);
                let other_var = other_lit.variable().index();
                if other_var == var_idx {
                    continue;
                }
                debug_assert_eq!(
                    self.var_data[other_var].level, 0,
                    "BUG: level-0 reason for {unit_lit:?} depends on non-level-0 {other_lit:?}",
                );
                let Some(pid) = self.level0_minimize_chain_proof_id_for_lit(other_lit.negated())
                else {
                    complete = false;
                    break;
                };
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            }

            if !complete {
                self.stats.lrat_materialize_minimize_incomplete_chains += 1;
                keep_pinned!(i);
                continue;
            }

            // LRAT RUP order for a derived unit is: falsifying antecedent
            // units first, then the implication clause that becomes
            // conflicting/unit under those assignments.
            hints.push(reason_id);
            let hint_count = hints.len() as u64;

            let unit_id = self
                .proof_emit_add(&[unit_lit], &hints, ProofAddKind::Derived)
                .unwrap_or(0);
            if unit_id != 0 {
                self.trace_materialized_level0_unit(unit_id, unit_lit, &hints);
                self.stats.lrat_materialize_minimize_emitted_unit_lines += 1;
                self.stats.lrat_materialize_minimize_unit_hints += hint_count;
                self.stats.lrat_materialize_minimize_unit_max_hints = self
                    .stats
                    .lrat_materialize_minimize_unit_max_hints
                    .max(hint_count);
                self.record_level0_proof_id_for_lit(unit_lit, unit_id);
                self.record_unit_proof_id_for_lit(unit_lit, unit_id);
            } else {
                keep_pinned!(i);
            }
        }
        hints.clear();
        self.cold.lrat_materialize_hints_buf = hints;
        pinned.truncate(kept);
        // #A2b: charge only WASTED rescan work. Pre-#A5 the condition was
        // "the cursor failed to advance past its restart slot" — i.e. the
        // entry at `legacy_start` failed again — and the charge was the span
        // that scan re-walked. #A5 no longer re-walks that span, but the
        // charge is kept at parity (see `legacy_start` above).
        let repinned_at_legacy_start = pinned.first() == Some(&legacy_start);
        self.cold.lrat_level0_unit_materialize_pinned = pinned;
        self.cold.lrat_level0_unit_materialize_cursor = level0_end;
        if repinned_at_legacy_start && level0_end > legacy_start {
            self.charge_proof_bookkeeping((level0_end - legacy_start) as u64);
        }
    }

    #[inline]
    pub(super) fn level0_unit_chain_proof_id_for_lit(&self, lit: Literal) -> Option<u64> {
        let var_index = lit.variable().index();
        if self.cold.lrat_enabled {
            // LRAT mode: prefer unit_proof_id (always a unit clause) over
            // level0_proof_id (may be a multi-literal clause from failed
            // ClearLevel0 materialization). Multi-literal hints cause NonUnit
            // rejection in the LRAT checker (#7108).
            if let Some(pid) = self.visible_unit_proof_id_for_lit(lit) {
                return Some(pid);
            }
            if let Some(id) = self.level0_var_proof_id_for_lit(lit) {
                return Some(id);
            }
            // Fall back to unit-only reason clauses.
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
            // DRAT mode: any clause ID works as a hint.
            if self.has_level0_proof_id(var_index) {
                return Some(self.cold.level0_proof_id[var_index]);
            }
            if let Some(pid) = self.unit_proof_id_of_var_index(var_index) {
                return Some(pid);
            }
            // #8467: lazy theory reasons are table indexes, not arena offsets.
            let reason_raw = self.var_data[var_index].reason;
            if is_clause_reason(reason_raw) && !self.var_data[var_index].is_lazy_theory_reason() {
                let id = self.clause_id(ClauseRef(reason_raw));
                if id != 0 {
                    return Some(id);
                }
            }
            None
        }
    }

    /// Materialize derived unit proof IDs for level-0 reason clauses before
    /// clause deletion proof steps (#6270).
    ///
    /// Walking the root-level trail in assignment order gives a topological
    /// order of level-0 implications, so each derived unit can be emitted
    /// after the proof IDs of the falsified literals in its reason are
    /// already available.
    ///
    /// Uses `level0_unit_chain_proof_id` which does NOT fall back to
    /// multi-literal reason clause IDs in LRAT mode (#7108).
    pub(super) fn materialize_level0_unit_proofs(&mut self) {
        let _ = self.materialize_level0_unit_proofs_impl(false);
    }

    /// Interruptible form for callers that can atomically decline the pending
    /// clause mutation.  Other proof-building callers retain the original
    /// all-or-complete behavior so a deadline cannot silently leave their
    /// proof row half prepared.
    pub(super) fn materialize_level0_unit_proofs_interruptible(&mut self) -> bool {
        self.materialize_level0_unit_proofs_impl(true)
    }

    fn materialize_level0_unit_proofs_impl(&mut self, honor_stop: bool) -> bool {
        if !self.cold.lrat_enabled {
            return true;
        }

        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let start = self
            .cold
            .lrat_level0_unit_materialize_cursor
            .min(level0_end);
        // #A2b search-time construction budget (see
        // `materialize_level0_minimize_unit_proofs` for the waste-only
        // charging rationale). This is the safe degrade point (root level,
        // between clause operations): once the budget is exhausted, drop to
        // no-proof search entirely.
        if self.cold.proof_bookkeeping_budget == Some(0) {
            self.degrade_proof_bookkeeping_after_exhaustion();
            return true;
        }
        self.stats.lrat_materialize_calls += 1;
        // #A5 (cursor, pinned) de-pinning + #A2b charge parity: see
        // `materialize_level0_minimize_unit_proofs` for both rationales.
        let mut pinned = std::mem::take(&mut self.cold.lrat_level0_unit_materialize_pinned);
        let retry_len = pinned.partition_point(|&p| p < start);
        let legacy_start = pinned.first().copied().unwrap_or(start).min(level0_end);
        self.stats.lrat_materialize_root_trail_entries += (retry_len + (level0_end - start)) as u64;
        let mut hints = std::mem::take(&mut self.cold.lrat_materialize_hints_buf);
        // Surviving pins are compacted in place: the write index never
        // overtakes the retry read index, and slots at or past `retry_len`
        // are stale (at or past `start`) and dropped by the final truncate.
        let mut kept = 0usize;
        macro_rules! keep_pinned {
            ($i:expr) => {{
                if kept < pinned.len() {
                    pinned[kept] = $i;
                } else {
                    pinned.push($i);
                }
                kept += 1;
            }};
        }
        // On deadline truncation the cursor retreats so every unattempted
        // slot stays covered: to `start` while retries remain outstanding
        // (the untouched tail of the retry list is re-kept below), or to the
        // first unattempted fresh slot.
        let mut next_cursor = level0_end;
        let mut deadline_truncated = false;
        for slot in 0..retry_len + (level0_end - start) {
            let from_retry = slot < retry_len;
            let i = if from_retry {
                pinned[slot]
            } else {
                start + (slot - retry_len)
            };
            // This routine is reached from incremental level-0 garbage
            // collection before the CDCL loop can poll `should_stop`. A long
            // LRAT trail used to overrun the forwarded whole-solve deadline by
            // minutes while repeatedly reconstructing unit chains. Stop only
            // between proof rows, retain the unfinished entries (pinned or
            // via the cursor), and let the surrounding solve publish Unknown.
            if honor_stop
                && slot.is_multiple_of(64)
                && (self.solve_deadline_expired() || self.is_interrupted())
            {
                if from_retry {
                    pinned.copy_within(slot..retry_len, kept);
                    kept += retry_len - slot;
                    next_cursor = start;
                } else {
                    next_cursor = i;
                }
                deadline_truncated = true;
                break;
            }
            let unit_lit = self.trail[i];
            let var_idx = unit_lit.variable().index();
            if var_idx >= self.num_vars
                || self.var_data[var_idx].level != 0
                || self.level0_var_proof_id(var_idx).is_some()
            {
                continue;
            }

            let Some(reason_ref) = self.var_reason(var_idx) else {
                // No reason: original decision or unit input clause.
                // unit_proof_id should already be set by add_clause for unit
                // inputs. If it's not, there's nothing we can do here.
                continue;
            };
            let clause_idx = reason_ref.0 as usize;
            if clause_idx >= self.arena.len() {
                keep_pinned!(i);
                continue;
            }
            let clause_len = self.arena.len_of(clause_idx);
            if !(0..clause_len).any(|j| self.arena.literal(clause_idx, j) == unit_lit) {
                self.stats.lrat_materialize_incomplete_chains += 1;
                keep_pinned!(i);
                continue;
            }

            let reason_id = self.clause_id(reason_ref);
            if reason_id == 0 || !self.lrat_hint_id_visible(reason_id) {
                self.stats.lrat_materialize_incomplete_chains += 1;
                keep_pinned!(i);
                continue;
            }

            // Unit reason clause: the reason itself IS the unit proof (#7108).
            // Learned unit clauses from conflict analysis (add_conflict_learned_clause)
            // don't go through proof_emit_unit, so unit_proof_id was never set.
            // Set it directly from the reason clause's proof ID.
            if clause_len <= 1 {
                self.record_level0_proof_id_for_lit(unit_lit, reason_id);
                self.record_unit_proof_id_for_lit(unit_lit, reason_id);
                continue;
            }

            hints.clear();
            if hints.capacity() < clause_len {
                hints.reserve(clause_len - hints.capacity());
            }
            let mut complete = true;
            for j in 0..clause_len {
                if honor_stop
                    && j.is_multiple_of(64)
                    && (self.solve_deadline_expired() || self.is_interrupted())
                {
                    if from_retry {
                        keep_pinned!(i);
                        pinned.copy_within(slot + 1..retry_len, kept);
                        kept += retry_len - slot - 1;
                        next_cursor = start;
                    } else {
                        next_cursor = i;
                    }
                    deadline_truncated = true;
                    complete = false;
                    break;
                }
                let other_lit = self.arena.literal(clause_idx, j);
                let other_var = other_lit.variable().index();
                if other_var == var_idx {
                    continue;
                }
                let Some(pid) = self.level0_unit_chain_proof_id_for_lit(other_lit.negated()) else {
                    complete = false;
                    break;
                };
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            }

            if deadline_truncated {
                break;
            }
            if !complete {
                let hidden_already_materialized = self
                    .cold
                    .level0_proof_id
                    .get(var_idx)
                    .copied()
                    .zip(self.cold.level0_proof_sign.get(var_idx).copied())
                    .is_some_and(|(id, sign)| {
                        id != 0 && sign == unit_lit.sign_i8() && !self.lrat_hint_id_visible(id)
                    })
                    || self
                        .unit_proof_id
                        .get(var_idx)
                        .copied()
                        .zip(self.unit_proof_sign.get(var_idx).copied())
                        .is_some_and(|(id, sign)| {
                            id != 0 && sign == unit_lit.sign_i8() && !self.lrat_hint_id_visible(id)
                        });
                if hidden_already_materialized {
                    self.stats.lrat_materialize_incomplete_chains += 1;
                    keep_pinned!(i);
                    continue;
                }
                self.stats.lrat_materialize_incomplete_chains += 1;
                // Fallback: emit as TrustedTransform so the variable has a
                // proof ID. Without this, collect_level0_unit_chain_filtered
                // silently drops the variable, causing incomplete LRAT chains
                // for learned clauses that depend on it (#7108 Fix E).
                let tt_id = self
                    .proof_emit_add(&[unit_lit], &[], ProofAddKind::TrustedTransform)
                    .unwrap_or(0);
                if tt_id != 0 {
                    self.stats.lrat_materialize_hidden_trusted_units += 1;
                    self.record_level0_proof_id_for_lit(unit_lit, tt_id);
                    self.record_unit_proof_id_for_lit(unit_lit, tt_id);
                }
                keep_pinned!(i);
                continue;
            }

            hints.push(reason_id);
            let hint_count = hints.len() as u64;

            let unit_id = self
                .proof_emit_add(&[unit_lit], &hints, ProofAddKind::Derived)
                .unwrap_or(0);
            if unit_id != 0 {
                self.trace_materialized_level0_unit(unit_id, unit_lit, &hints);
                self.stats.lrat_materialize_emitted_unit_lines += 1;
                self.stats.lrat_materialize_unit_hints += hint_count;
                self.stats.lrat_materialize_unit_max_hints =
                    self.stats.lrat_materialize_unit_max_hints.max(hint_count);
                self.record_level0_proof_id_for_lit(unit_lit, unit_id);
                self.record_unit_proof_id_for_lit(unit_lit, unit_id);
            } else {
                keep_pinned!(i);
            }
        }
        hints.clear();
        self.cold.lrat_materialize_hints_buf = hints;
        pinned.truncate(kept);
        // #A2b: charge only wasted (still-pinned) rescan work at parity with
        // the pre-#A5 scalar cursor; see
        // `materialize_level0_minimize_unit_proofs`.
        let repinned_at_legacy_start = pinned.first() == Some(&legacy_start);
        self.cold.lrat_level0_unit_materialize_pinned = pinned;
        self.cold.lrat_level0_unit_materialize_cursor = next_cursor;
        if !deadline_truncated && repinned_at_legacy_start && level0_end > legacy_start {
            self.charge_proof_bookkeeping((level0_end - legacy_start) as u64);
        }
        !deadline_truncated
    }
}
