// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward trail analysis for vivification conflicts and implied literals.

use super::super::super::*;

impl Solver {
    /// Check whether the conflict clause already subsumes the candidate.
    ///
    /// CaDiCaL vivify.cpp:666-744 (`vivify_deduce`) marks the candidate and
    /// short-circuits when the conflict clause is a literal subset after
    /// dropping level-0-false literals. This avoids analyzing a clause we can
    /// delete immediately.
    pub(in crate::solver) fn vivify_conflict_clause_subsumes_candidate(
        &mut self,
        candidate_idx: usize,
        candidate_lits: &[Literal],
        conflict_ref: ClauseRef,
    ) -> bool {
        if candidate_lits.is_empty() {
            return false;
        }

        let conflict_idx = conflict_ref.0 as usize;
        if conflict_idx >= self.arena.len() || conflict_idx == candidate_idx {
            return false;
        }

        let lit_capacity = self.num_vars.saturating_mul(2);
        if self.backbone_seen.len() < lit_capacity {
            self.backbone_seen.resize(lit_capacity, false);
        }

        let mut marked = Vec::with_capacity(candidate_lits.len());
        for &lit in candidate_lits {
            let lit_idx = lit.index();
            if lit_idx >= self.backbone_seen.len() || self.backbone_seen[lit_idx] {
                continue;
            }
            self.backbone_seen[lit_idx] = true;
            marked.push(lit_idx);
        }

        let mut active_conflict_lits = 0usize;
        let mut subsumes = true;
        for &lit in self.arena.literals(conflict_idx) {
            let var_idx = lit.variable().index();
            if var_idx >= self.num_vars || self.var_data[var_idx].level == 0 {
                continue;
            }

            active_conflict_lits += 1;
            let lit_idx = lit.index();
            if lit_idx >= self.backbone_seen.len() || !self.backbone_seen[lit_idx] {
                subsumes = false;
                break;
            }
        }

        for lit_idx in marked {
            self.backbone_seen[lit_idx] = false;
        }

        subsumes && active_conflict_lits > 0
    }

    /// Pick the earliest propagated true candidate literal before implied
    /// backward analysis.
    ///
    /// CaDiCaL does not analyze whichever true literal happens to appear first
    /// in sorted order. After probing stops, it re-picks the earliest true
    /// candidate literal on the trail (`better_subsume_trail` in vivify.cpp)
    /// so the implied path follows the shortest available dependency chain.
    ///
    /// The input `current` is already known to be true with a non-decision
    /// reason. We keep that as the fallback and only move to an earlier true
    /// literal that is also implied by a reason clause.
    pub(in crate::solver) fn pick_vivify_implied_literal(
        &self,
        current: Literal,
        candidate_lits: &[Literal],
    ) -> Literal {
        let current_var = current.variable().index();
        let mut best = current;
        let mut best_trail = self.var_data[current_var].trail_pos;

        for &lit in candidate_lits {
            if self.lit_val(lit) <= 0 {
                continue;
            }
            let var_idx = lit.variable().index();
            if var_idx >= self.num_vars || self.var_data[var_idx].reason == NO_REASON {
                continue;
            }
            let trail_pos = self.var_data[var_idx].trail_pos;
            if trail_pos < best_trail {
                best = lit;
                best_trail = trail_pos;
            }
        }

        best
    }

    /// Backward analysis for an already-implied candidate literal.
    ///
    /// CaDiCaL `vivify_deduce` routes implied literals through the same
    /// backward analysis used for conflicts so vivification can either:
    /// 1. find a concrete subsuming reason clause, or
    /// 2. derive a shorter clause containing only the necessary decisions plus
    ///    the implied literal.
    ///
    /// The direct "implied => delete candidate" shortcut misses both cases.
    pub(in crate::solver) fn vivify_analyze_implied_literal(
        &mut self,
        implied_lit: Literal,
        candidate_lits: &[Literal],
    ) -> (Vec<usize>, Vec<u64>, bool, Option<ClauseRef>) {
        let num_vars = self.num_vars;
        let implied_var = implied_lit.variable().index();
        // Use persistent vivify_analyzed buffer instead of per-call allocation (#8543).
        if self.vivify_analyzed.len() < num_vars {
            self.vivify_analyzed.resize(num_vars, false);
        }
        debug_assert!(
            self.vivify_analyzed_to_clear.is_empty(),
            "BUG: vivify_analyzed_to_clear not empty at analysis start"
        );
        let mut necessary_decisions: Vec<usize> = Vec::new();
        let mut reason_chain: Vec<u64> = Vec::new();
        let mut uses_redundant = false;

        let check_subsumption = !candidate_lits.is_empty();
        let candidate_size = candidate_lits.len();
        let mut marked_lits: Vec<usize> = Vec::new();
        if check_subsumption {
            let lit_capacity = num_vars.saturating_mul(2);
            if self.backbone_seen.len() < lit_capacity {
                self.backbone_seen.resize(lit_capacity, false);
            }
            marked_lits.reserve(candidate_size);
            for &lit in candidate_lits {
                let li = lit.index();
                if li < self.backbone_seen.len() && !self.backbone_seen[li] {
                    self.backbone_seen[li] = true;
                    marked_lits.push(li);
                }
            }
        }

        if implied_var < num_vars {
            self.vivify_analyzed[implied_var] = true;
            self.vivify_analyzed_to_clear.push(implied_var);
        }

        for i in (0..self.trail.len()).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx >= num_vars || !self.vivify_analyzed[var_idx] {
                continue;
            }
            self.vivify_analyzed[var_idx] = false;

            if self.var_data[var_idx].level == 0 {
                continue;
            }

            if let Some(reason_ref) = self.var_reason(var_idx) {
                if self.cold.lrat_enabled {
                    let reason_id = self.clause_id(reason_ref);
                    if reason_id != 0 {
                        reason_chain.push(reason_id);
                    }
                }
                let ci = reason_ref.0 as usize;
                if ci < self.arena.len() {
                    let is_reason_learned = self.arena.is_learned(ci);
                    uses_redundant |= is_reason_learned;

                    // CaDiCaL vivify_analyze vivify.cpp:627-628: promote
                    // redundant reason clauses encountered during backward
                    // analysis. Recompute glue using current assignment levels
                    // and keep the better (lower) value.
                    if is_reason_learned {
                        let new_glue = self.recompute_glue(ci);
                        let old_glue = self.arena.lbd(ci);
                        if new_glue < old_glue {
                            self.arena.set_lbd(ci, new_glue);
                        }
                    }

                    let clen = self.arena.len_of(ci);

                    if check_subsumption && clen <= candidate_size {
                        let mut reason_subsumes = true;
                        let mut active_lits = 0u32;
                        for j in 0..clen {
                            let rl = self.arena.literal(ci, j);
                            let rv = rl.variable().index();
                            if rv >= num_vars || self.var_data[rv].level == 0 {
                                continue;
                            }
                            active_lits += 1;
                            let li = rl.index();
                            if li >= self.backbone_seen.len() || !self.backbone_seen[li] {
                                reason_subsumes = false;
                                break;
                            }
                        }
                        if reason_subsumes && active_lits > 0 {
                            // Sparse cleanup before early return (#8543).
                            for i in 0..self.vivify_analyzed_to_clear.len() {
                                let idx = self.vivify_analyzed_to_clear[i];
                                self.vivify_analyzed[idx] = false;
                            }
                            self.vivify_analyzed_to_clear.clear();
                            for &li in &marked_lits {
                                self.backbone_seen[li] = false;
                            }
                            if self.cold.lrat_enabled {
                                for &rv in &self.min.lrat_to_clear {
                                    if rv < self.min.minimize_flags.len() {
                                        self.min.minimize_flags[rv] &= !LRAT_A;
                                    }
                                }
                                self.min.lrat_to_clear.clear();
                            }
                            return (
                                necessary_decisions,
                                reason_chain,
                                uses_redundant,
                                Some(reason_ref),
                            );
                        }
                    }

                    for j in 0..clen {
                        let rl = self.arena.literal(ci, j);
                        let rv = rl.variable().index();
                        if rv == var_idx || rv >= num_vars {
                            continue;
                        }
                        if self.var_data[rv].level == 0 {
                            if self.cold.lrat_enabled
                                && self.has_any_proof_id(rv)
                                && self.min.minimize_flags[rv] & LRAT_A == 0
                            {
                                self.min.minimize_flags[rv] |= LRAT_A;
                                self.min.lrat_to_clear.push(rv);
                            }
                        } else if !self.vivify_analyzed[rv] {
                            self.vivify_analyzed[rv] = true;
                            self.vivify_analyzed_to_clear.push(rv);
                        }
                    }
                }
            } else {
                necessary_decisions.push(var_idx);
            }
        }

        // Sparse cleanup of vivify_analyzed buffer (#8543).
        for i in 0..self.vivify_analyzed_to_clear.len() {
            let idx = self.vivify_analyzed_to_clear[i];
            self.vivify_analyzed[idx] = false;
        }
        self.vivify_analyzed_to_clear.clear();

        for &li in &marked_lits {
            self.backbone_seen[li] = false;
        }

        if self.cold.lrat_enabled {
            let unit_chain = self.collect_level0_unit_chain();
            reason_chain.extend(unit_chain);
        }

        (necessary_decisions, reason_chain, uses_redundant, None)
    }

    /// Backward trail analysis for vivify conflict (CaDiCaL vivify_analyze).
    ///
    /// Walks the trail backward from the conflict clause, resolving with reason
    /// clauses for propagated literals. Decision literals (no reason) are added
    /// to the result — these are the only decisions causally needed for the
    /// conflict. This produces strictly shorter vivified clauses than the simple
    /// "keep all decisions" filter.
    ///
    /// Also collects LRAT resolution hints in the same pass (when LRAT enabled).
    ///
    /// When `candidate_lits` is non-empty, each reason clause encountered during
    /// the backward walk is checked for subsumption against the candidate
    /// (CaDiCaL vivify_analyze vivify.cpp:587-635). If a reason clause's
    /// non-level-0 literals are all in the candidate, the candidate is subsumed
    /// and analysis short-circuits.
    ///
    /// Returns (necessary_decision_vars, lrat_chain, uses_redundant_reason,
    ///          subsuming_clause).
    /// - necessary_decision_vars: set of var indices that were decisions needed
    ///   for the conflict. The caller intersects with sorted[] to build the clause.
    /// - lrat_chain: reason clause IDs for proof reconstruction.
    /// - uses_redundant_reason: true if any reason clause in the chain is learned
    ///   (redundant). CaDiCaL vivify.cpp:586 tracks this to decide whether
    ///   irredundant clause subsumption/demotion is safe.
    /// - subsuming_clause: if a reason clause subsumes the candidate during
    ///   backward analysis, its ClauseRef is returned here.
    pub(in crate::solver) fn vivify_analyze_conflict(
        &mut self,
        conflict_ref: ClauseRef,
        candidate_lits: &[Literal],
    ) -> (Vec<usize>, Vec<u64>, bool, Option<ClauseRef>) {
        let num_vars = self.num_vars;
        // Use persistent vivify_analyzed buffer instead of per-call allocation (#8543).
        if self.vivify_analyzed.len() < num_vars {
            self.vivify_analyzed.resize(num_vars, false);
        }
        debug_assert!(
            self.vivify_analyzed_to_clear.is_empty(),
            "BUG: vivify_analyzed_to_clear not empty at conflict analysis start"
        );
        let mut necessary_decisions: Vec<usize> = Vec::new();
        let mut reason_chain: Vec<u64> = Vec::new();
        let mut uses_redundant = false;

        // Mark candidate literals in backbone_seen for polarity-aware subsumption
        // detection during backward analysis (CaDiCaL vivify_analyze vivify.cpp:587).
        let check_subsumption = !candidate_lits.is_empty();
        let candidate_size = candidate_lits.len();
        let mut marked_lits: Vec<usize> = Vec::new();
        if check_subsumption {
            let lit_capacity = num_vars.saturating_mul(2);
            if self.backbone_seen.len() < lit_capacity {
                self.backbone_seen.resize(lit_capacity, false);
            }
            marked_lits.reserve(candidate_size);
            for &lit in candidate_lits {
                let li = lit.index();
                if li < self.backbone_seen.len() && !self.backbone_seen[li] {
                    self.backbone_seen[li] = true;
                    marked_lits.push(li);
                }
            }
        }

        // Seed: mark conflict clause literals as seen.
        // Track if the conflict clause itself is learned (CaDiCaL vivify.cpp:586).
        debug_assert!(self.min.lrat_to_clear.is_empty());
        let conflict_idx = conflict_ref.0 as usize;
        if conflict_idx < self.arena.len() {
            uses_redundant = self.arena.is_learned(conflict_idx);
            let clen = self.arena.len_of(conflict_idx);
            for i in 0..clen {
                let rl = self.arena.literal(conflict_idx, i);
                let rv = rl.variable().index();
                if rv >= num_vars {
                    continue;
                }
                if self.var_data[rv].level == 0 {
                    // Include ClearLevel0 victims whose reason was cleared by
                    // BVE but whose proof ID is preserved in level0_proof_id
                    // or unit_proof_id (#5014).
                    if self.cold.lrat_enabled
                        && self.has_any_proof_id(rv)
                        && self.min.minimize_flags[rv] & LRAT_A == 0
                    {
                        self.min.minimize_flags[rv] |= LRAT_A;
                        self.min.lrat_to_clear.push(rv);
                    }
                } else {
                    self.vivify_analyzed[rv] = true;
                    self.vivify_analyzed_to_clear.push(rv);
                }
            }
        }

        // Walk trail backward (CaDiCaL vivify_analyze pattern).
        let trail_len = self.trail.len();
        for i in (0..trail_len).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx >= num_vars || !self.vivify_analyzed[var_idx] {
                continue;
            }
            self.vivify_analyzed[var_idx] = false;

            if self.var_data[var_idx].level == 0 {
                continue;
            }

            if let Some(reason_ref) = self.var_reason(var_idx) {
                // Propagated: resolve with reason clause.
                if self.cold.lrat_enabled {
                    let reason_id = self.clause_id(reason_ref);
                    if reason_id != 0 {
                        reason_chain.push(reason_id);
                    }
                }
                let ci = reason_ref.0 as usize;
                if ci < self.arena.len() {
                    // CaDiCaL vivify.cpp:586: track if any reason is redundant.
                    let is_reason_learned = self.arena.is_learned(ci);
                    uses_redundant |= is_reason_learned;

                    // CaDiCaL vivify_analyze vivify.cpp:627-628: promote
                    // redundant reason clauses encountered during backward
                    // analysis. Recompute glue using current assignment levels
                    // and keep the better (lower) value.
                    if is_reason_learned {
                        let new_glue = self.recompute_glue(ci);
                        let old_glue = self.arena.lbd(ci);
                        if new_glue < old_glue {
                            self.arena.set_lbd(ci, new_glue);
                        }
                    }

                    let clen = self.arena.len_of(ci);

                    // CaDiCaL vivify_analyze vivify.cpp:587-635: check if this
                    // reason clause subsumes the candidate. A reason clause
                    // subsumes if every non-level-0 literal (with matching
                    // polarity) appears in the candidate.
                    if check_subsumption && clen <= candidate_size {
                        let mut reason_subsumes = true;
                        let mut active_lits = 0u32;
                        for j in 0..clen {
                            let rl = self.arena.literal(ci, j);
                            let rv = rl.variable().index();
                            if rv >= num_vars || self.var_data[rv].level == 0 {
                                continue;
                            }
                            active_lits += 1;
                            let li = rl.index();
                            if li >= self.backbone_seen.len() || !self.backbone_seen[li] {
                                reason_subsumes = false;
                                break;
                            }
                        }
                        if reason_subsumes && active_lits > 0 {
                            // Reason clause subsumes candidate — clean up and
                            // return early (CaDiCaL vivify.cpp:630-635).
                            // Sparse cleanup before early return (#8543).
                            for i in 0..self.vivify_analyzed_to_clear.len() {
                                let idx = self.vivify_analyzed_to_clear[i];
                                self.vivify_analyzed[idx] = false;
                            }
                            self.vivify_analyzed_to_clear.clear();
                            for &li in &marked_lits {
                                self.backbone_seen[li] = false;
                            }
                            if self.cold.lrat_enabled {
                                for i in 0..self.min.lrat_to_clear.len() {
                                    let rv = self.min.lrat_to_clear[i];
                                    if rv < self.min.minimize_flags.len() {
                                        self.min.minimize_flags[rv] &= !LRAT_A;
                                    }
                                }
                                self.min.lrat_to_clear.clear();
                            }
                            return (
                                necessary_decisions,
                                reason_chain,
                                uses_redundant,
                                Some(reason_ref),
                            );
                        }
                    }

                    for j in 0..clen {
                        let rl = self.arena.literal(ci, j);
                        let rv = rl.variable().index();
                        if rv == var_idx || rv >= num_vars {
                            continue;
                        }
                        if self.var_data[rv].level == 0 {
                            // Include ClearLevel0 victims (#5014).
                            if self.cold.lrat_enabled
                                && self.has_any_proof_id(rv)
                                && self.min.minimize_flags[rv] & LRAT_A == 0
                            {
                                self.min.minimize_flags[rv] |= LRAT_A;
                                self.min.lrat_to_clear.push(rv);
                            }
                        } else if !self.vivify_analyzed[rv] {
                            self.vivify_analyzed[rv] = true;
                            self.vivify_analyzed_to_clear.push(rv);
                        }
                    }
                }
            } else {
                // Decision: causally needed for the conflict.
                necessary_decisions.push(var_idx);
            }
        }

        // Sparse cleanup of vivify_analyzed buffer (#8543).
        for i in 0..self.vivify_analyzed_to_clear.len() {
            let idx = self.vivify_analyzed_to_clear[i];
            self.vivify_analyzed[idx] = false;
        }
        self.vivify_analyzed_to_clear.clear();

        // Clean up candidate marks from backbone_seen.
        for &li in &marked_lits {
            self.backbone_seen[li] = false;
        }

        // LRAT: collect level-0 unit chain, including ClearLevel0 victims
        // whose reason was cleared by BVE — handled via level0_var_proof_id
        // inside collect_level0_unit_chain (#4617, #5014).
        if self.cold.lrat_enabled {
            let unit_chain = self.collect_level0_unit_chain();
            reason_chain.extend(unit_chain);
        }

        (necessary_decisions, reason_chain, uses_redundant, None)
    }
}
