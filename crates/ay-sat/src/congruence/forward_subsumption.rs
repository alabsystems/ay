// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward subsumption using equivalence-aware representatives.

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

use super::union_find::UnionFind;
use super::{debug_congruence_enabled, CongruenceClosure};

impl CongruenceClosure {
    /// Forward subsumption using equivalence-aware representatives.
    ///
    /// After congruence closure, clauses may become subsumed when equivalent
    /// literals are treated as identical. Example: (a, c) subsumes (b, c, d)
    /// when a ≡ b.
    ///
    /// Called from the solver wrapper AFTER proof emission is complete, because
    /// RUP checks need gate-defining clauses alive during decide/propagate.
    ///
    /// Reference: CaDiCaL congruence.cpp:4955-5073 forward_subsume_matching_clauses()
    ///
    /// Soundness argument (re-enabled from #7432 disable):
    /// - Congruence adds binary equivalence clauses (¬a ∨ b) and (a ∨ ¬b) for
    ///   each equivalence a ≡ b to the working clause arena.
    /// - The CDCL solver must satisfy all active arena clauses, including these
    ///   binaries, so equivalent variables always have the same truth value in
    ///   any SAT model.
    /// - Forward subsumption only deletes clause C when a shorter clause D
    ///   exists such that D's representative literals are a subset of C's
    ///   representative literals. Any model satisfying D therefore satisfies C
    ///   under the equivalence binaries.
    /// - finalize_sat_model verifies against the immutable original_ledger.
    ///   Since equivalent variables have consistent values in the model (forced
    ///   by the binaries), the original clause C is satisfied whenever D is.
    /// - LRAT mode is guarded separately at the call site (congruence/mod.rs)
    ///   because proof deletion certificates require additional plumbing.
    pub(crate) fn forward_subsume_with_equivalences(
        &mut self,
        clauses: &mut ClauseArena,
        equivalence_edges: &[(Literal, Literal)],
    ) -> u64 {
        if equivalence_edges.is_empty() {
            return 0;
        }

        // Build UF from equivalence edges.
        let num_lits = self.num_vars * 2;
        let mut uf = UnionFind::new(num_lits);
        for &(lhs, rhs) in equivalence_edges {
            let li = lhs.index();
            let ri = rhs.index();
            // Skip same-variable edges: trivial (x ≡ x) is a no-op, and the
            // complementary contradiction edge (x ≡ ¬x, recorded by
            // merge_or_contradict to close an UNSAT cycle for the witness
            // unit's RUP probe) must NEVER be treated as an equivalence here.
            // It reaches this point on the rejected-UNSAT fall-through (all
            // witness units failed RUP), where equating x with ¬x would let
            // the tautology/subsumption checks delete live clauses —
            // constraint loss (wf_ff5991a1).
            if li / 2 == ri / 2 {
                continue;
            }
            if li < num_lits && ri < num_lits {
                let _ = uf.union_lits(li, ri);
            }
        }
        let vals: Option<&[i8]> = None; // No level-0 vals in solver context
        let mut subsumed_count: u64 = 0;

        // Phase 1: Identify matchable variables (vars with non-trivial representative).
        if self.forward_subsumption_matchable.len() < self.num_vars {
            self.forward_subsumption_matchable
                .resize(self.num_vars, false);
        }
        if self.forward_subsumption_marked.len() < num_lits {
            self.forward_subsumption_marked.resize(num_lits, false);
        }
        self.forward_subsumption_matchable.fill(false);
        self.forward_subsumption_marked.fill(false);
        let matchable = &mut self.forward_subsumption_matchable;
        let marked = &mut self.forward_subsumption_marked;

        for var in 0..self.num_vars {
            let lit_idx = var * 2;
            if lit_idx >= num_lits {
                continue;
            }
            let repr = uf.find(lit_idx);
            if repr != lit_idx {
                matchable[var] = true;
                let repr_var = repr / 2;
                if repr_var < self.num_vars {
                    matchable[repr_var] = true;
                }
            }
        }

        // Phase 2: Build candidate list (non-binary irredundant with matchable vars).
        // Collect all clause indices first to avoid borrow conflict
        // (indices() borrows arena immutably, mark_garbage borrows mutably).
        let all_indices: Vec<usize> = clauses.indices().collect();
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        let mut repr_buf: Vec<usize> = Vec::new();

        for idx in all_indices {
            if clauses.is_garbage(idx) {
                continue;
            }
            let len = clauses.len_of(idx);
            if len <= 2 || clauses.is_learned(idx) {
                continue;
            }

            repr_buf.clear();
            let mut contains_matchable = false;
            let mut is_tautology = false;

            for i in 0..len {
                let lit = clauses.literal(idx, i);
                let li = lit.index();
                // Skip false literals (level-0 assignments).
                if let Some(v) = vals {
                    if li < v.len() {
                        if v[li] < 0 {
                            continue;
                        }
                        if v[li] > 0 {
                            is_tautology = true;
                            break;
                        }
                    }
                }

                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr >= num_lits {
                    continue;
                }
                if marked[repr] {
                    continue; // duplicate representative
                }
                let neg_repr = repr ^ 1;
                if neg_repr < num_lits && marked[neg_repr] {
                    is_tautology = true;
                    break;
                }

                marked[repr] = true;
                repr_buf.push(repr);

                let var_idx = li / 2;
                if var_idx < self.num_vars && matchable[var_idx] {
                    contains_matchable = true;
                }
            }

            // Unmark.
            for &r in &repr_buf {
                marked[r] = false;
            }

            if is_tautology {
                clauses.mark_garbage_keep_data(idx);
                subsumed_count += 1;
                continue;
            }
            if !contains_matchable || repr_buf.is_empty() {
                continue;
            }

            candidates.push((idx, repr_buf.len()));
        }

        if candidates.is_empty() {
            return subsumed_count;
        }

        // Phase 3: Sort by representative count (smallest first = potential subsumers).
        candidates.sort_by_key(|&(_, count)| count);

        // Build occurrence lists indexed by representative literal.
        // CaDiCaL adds each non-subsumed clause to ONE occurrence list
        // (the least-occurring representative) to keep lists small.
        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); num_lits];

        for &(clause_idx, _) in &candidates {
            if clauses.is_garbage(clause_idx) {
                continue;
            }

            // Mark all representative literals of this clause (index-based
            // access avoids borrowing the arena as a slice, allowing mutable
            // mark_garbage_keep_data below).
            repr_buf.clear();
            let clen = clauses.len_of(clause_idx);
            for i in 0..clen {
                let lit = clauses.literal(clause_idx, i);
                let li = lit.index();
                if let Some(v) = vals {
                    if li < v.len() && v[li] < 0 {
                        continue;
                    }
                }
                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr < num_lits && !marked[repr] {
                    marked[repr] = true;
                    repr_buf.push(repr);
                }
            }

            // Check occurrence lists for a subsuming clause.
            let mut found_subsuming = false;
            let mut least_occurring_repr = 0usize;
            let mut least_count = usize::MAX;

            'check: for &repr in &repr_buf {
                let occ_len = occs[repr].len();
                if occ_len < least_count {
                    least_count = occ_len;
                    least_occurring_repr = repr;
                }
                for &other_idx in &occs[repr] {
                    if clauses.is_garbage(other_idx) {
                        continue;
                    }
                    // Check if other_idx subsumes clause_idx:
                    // all representative literals of other_idx must be marked.
                    let olen = clauses.len_of(other_idx);
                    let mut all_marked = true;
                    for j in 0..olen {
                        let olit = clauses.literal(other_idx, j);
                        let oli = olit.index();
                        if let Some(v) = vals {
                            if oli < v.len() && v[oli] < 0 {
                                continue;
                            }
                        }
                        if oli >= num_lits {
                            all_marked = false;
                            break;
                        }
                        let orepr = uf.find(oli);
                        if orepr >= num_lits || !marked[orepr] {
                            all_marked = false;
                            break;
                        }
                    }
                    if all_marked {
                        clauses.mark_garbage_keep_data(clause_idx);
                        subsumed_count += 1;
                        found_subsuming = true;
                        break 'check;
                    }
                }
            }

            // Unmark.
            for &r in &repr_buf {
                marked[r] = false;
            }

            // If not subsumed, add to occurrence list at the least-occurring repr.
            if !found_subsuming && !repr_buf.is_empty() {
                occs[least_occurring_repr].push(clause_idx);
            }
        }

        if debug_congruence_enabled() && subsumed_count > 0 {
            eprintln!("[congruence] forward subsumed {subsumed_count} clauses via equivalences");
        }

        subsumed_count
    }

    /// Same as `forward_subsume_with_equivalences` but returns the list of
    /// subsumed clause indices instead of marking them as garbage directly.
    /// The caller (solver) handles marking garbage and emitting proof deletions.
    /// Used in LRAT mode where proof deletion certificates are required (#6270).
    pub(crate) fn forward_subsume_collect_indices(
        &mut self,
        clauses: &ClauseArena,
        equivalence_edges: &[(Literal, Literal)],
    ) -> Vec<usize> {
        if equivalence_edges.is_empty() {
            return Vec::new();
        }

        let num_lits = self.num_vars * 2;
        let mut uf = UnionFind::new(num_lits);
        for &(lhs, rhs) in equivalence_edges {
            let li = lhs.index();
            let ri = rhs.index();
            // Same-variable edge skip: see forward_subsume_with_equivalences.
            if li / 2 == ri / 2 {
                continue;
            }
            if li < num_lits && ri < num_lits {
                let _ = uf.union_lits(li, ri);
            }
        }
        let vals: Option<&[i8]> = None;
        let mut subsumed_indices: Vec<usize> = Vec::new();

        if self.forward_subsumption_matchable.len() < self.num_vars {
            self.forward_subsumption_matchable
                .resize(self.num_vars, false);
        }
        if self.forward_subsumption_marked.len() < num_lits {
            self.forward_subsumption_marked.resize(num_lits, false);
        }
        self.forward_subsumption_matchable.fill(false);
        self.forward_subsumption_marked.fill(false);
        let matchable = &mut self.forward_subsumption_matchable;
        let marked = &mut self.forward_subsumption_marked;

        for var in 0..self.num_vars {
            let lit_idx = var * 2;
            if lit_idx >= num_lits {
                continue;
            }
            let repr = uf.find(lit_idx);
            if repr != lit_idx {
                matchable[var] = true;
                let repr_var = repr / 2;
                if repr_var < self.num_vars {
                    matchable[repr_var] = true;
                }
            }
        }

        let all_indices: Vec<usize> = clauses.indices().collect();
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        let mut repr_buf: Vec<usize> = Vec::new();

        for idx in all_indices {
            if clauses.is_garbage(idx) {
                continue;
            }
            let len = clauses.len_of(idx);
            if len <= 2 || clauses.is_learned(idx) {
                continue;
            }

            repr_buf.clear();
            let mut contains_matchable = false;
            let mut is_tautology = false;

            for i in 0..len {
                let lit = clauses.literal(idx, i);
                let li = lit.index();
                if let Some(v) = vals {
                    if li < v.len() {
                        if v[li] < 0 {
                            continue;
                        }
                        if v[li] > 0 {
                            is_tautology = true;
                            break;
                        }
                    }
                }

                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr >= num_lits {
                    continue;
                }
                if marked[repr] {
                    continue;
                }
                let neg_repr = repr ^ 1;
                if neg_repr < num_lits && marked[neg_repr] {
                    is_tautology = true;
                    break;
                }

                marked[repr] = true;
                repr_buf.push(repr);

                let var_idx = li / 2;
                if var_idx < self.num_vars && matchable[var_idx] {
                    contains_matchable = true;
                }
            }

            for &r in &repr_buf {
                marked[r] = false;
            }

            if is_tautology {
                subsumed_indices.push(idx);
                continue;
            }
            if !contains_matchable || repr_buf.is_empty() {
                continue;
            }

            candidates.push((idx, repr_buf.len()));
        }

        if candidates.is_empty() {
            return subsumed_indices;
        }

        candidates.sort_by_key(|&(_, count)| count);

        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); num_lits];

        for &(clause_idx, _) in &candidates {
            if clauses.is_garbage(clause_idx) || subsumed_indices.contains(&clause_idx) {
                continue;
            }

            repr_buf.clear();
            let clen = clauses.len_of(clause_idx);
            for i in 0..clen {
                let lit = clauses.literal(clause_idx, i);
                let li = lit.index();
                if let Some(v) = vals {
                    if li < v.len() && v[li] < 0 {
                        continue;
                    }
                }
                if li >= num_lits {
                    continue;
                }
                let repr = uf.find(li);
                if repr < num_lits && !marked[repr] {
                    marked[repr] = true;
                    repr_buf.push(repr);
                }
            }

            let mut found_subsuming = false;
            let mut least_occurring_repr = 0usize;
            let mut least_count = usize::MAX;

            'check: for &repr in &repr_buf {
                let occ_len = occs[repr].len();
                if occ_len < least_count {
                    least_count = occ_len;
                    least_occurring_repr = repr;
                }
                for &other_idx in &occs[repr] {
                    if clauses.is_garbage(other_idx) || subsumed_indices.contains(&other_idx) {
                        continue;
                    }
                    let olen = clauses.len_of(other_idx);
                    let mut all_marked = true;
                    for j in 0..olen {
                        let olit = clauses.literal(other_idx, j);
                        let oli = olit.index();
                        if let Some(v) = vals {
                            if oli < v.len() && v[oli] < 0 {
                                continue;
                            }
                        }
                        if oli >= num_lits {
                            all_marked = false;
                            break;
                        }
                        let orepr = uf.find(oli);
                        if orepr >= num_lits || !marked[orepr] {
                            all_marked = false;
                            break;
                        }
                    }
                    if all_marked {
                        subsumed_indices.push(clause_idx);
                        found_subsuming = true;
                        break 'check;
                    }
                }
            }

            for &r in &repr_buf {
                marked[r] = false;
            }

            if !found_subsuming && !repr_buf.is_empty() {
                occs[least_occurring_repr].push(clause_idx);
            }
        }

        if debug_congruence_enabled() && !subsumed_indices.is_empty() {
            eprintln!(
                "[congruence] forward subsume collected {} clause indices for proof deletion",
                subsumed_indices.len()
            );
        }

        subsumed_indices
    }

    /// Build literal map from union-find
    pub(super) fn build_lit_map(&self, uf: &mut UnionFind) -> Vec<Literal> {
        let num_lits = self.num_vars * 2;
        let mut lit_map = Vec::with_capacity(num_lits);

        for lit_idx in 0..num_lits {
            let rep_idx = uf.find(lit_idx);
            lit_map.push(Literal::from_index(rep_idx));
        }

        // Postcondition: every representative in the output map is a fixpoint.
        debug_assert!(
            lit_map.iter().all(|&rep| {
                let ri = rep.index();
                ri < num_lits && uf.find(ri) == ri
            }),
            "BUG: build_lit_map produced non-fixpoint representative"
        );
        lit_map
    }
}
