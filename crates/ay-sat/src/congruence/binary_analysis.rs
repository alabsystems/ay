// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary clause analysis: hyper-ternary resolution, unit discovery, equivalence extraction.

use crate::clause_arena::ClauseArena;
use crate::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use crate::literal::Literal;

use super::union_find::{merge_or_contradict, UnionFind};
use super::{debug_congruence_enabled, CongruenceClosure};

impl CongruenceClosure {
    /// Hyper-ternary resolution: derive new binary clauses from ternary + binary pairs.
    ///
    /// For each ternary clause (a, b, c) and existing binary clause (-a, b),
    /// derive the binary clause (b, c) by hyper-resolution. This enriches the
    /// binary implication graph, enabling AND gate extraction to find more
    /// gate patterns.
    ///
    /// Reference: CaDiCaL congruence.cpp extract_binaries() (Biere et al. 2024).
    pub(super) fn hyper_ternary_resolution(
        &mut self,
        clauses: &mut ClauseArena,
    ) -> Vec<(usize, Literal, Literal)> {
        let num_lits = self.num_vars * 2;
        let mut new_binaries: Vec<(usize, Literal, Literal)> = Vec::new();

        // Index all existing binary clauses: lit → set of other literals.
        // Use HashMap (sparse) instead of Vec<HashSet> (dense) to avoid
        // allocating 2*num_vars empty HashSets — only literals that actually
        // appear in binary clauses get entries (#5079 Finding 2).
        let mut binary_map: HashMap<usize, HashSet<Literal>> = HashMap::default();
        let mut ternary_indices: Vec<usize> = Vec::new();

        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) {
                continue;
            }
            let lits = clauses.literals(idx);
            match lits.len() {
                2 => {
                    let a = lits[0];
                    let b = lits[1];
                    if a.index() < num_lits && b.index() < num_lits {
                        binary_map.entry(a.index()).or_default().insert(b);
                        binary_map.entry(b.index()).or_default().insert(a);
                    }
                }
                3 => {
                    ternary_indices.push(idx);
                }
                _ => {}
            }
        }

        // For each ternary clause, try to derive new binary clauses.
        for &idx in &ternary_indices {
            let lits = clauses.literals(idx);
            let tri = [lits[0], lits[1], lits[2]];

            // Try each literal as the resolved-away variable.
            for i in 0..3 {
                let resolved = tri[i];
                let neg_resolved = resolved.negated();
                if neg_resolved.index() >= num_lits {
                    continue;
                }

                let j = (i + 1) % 3;
                let k = (i + 2) % 3;
                let remaining_a = tri[j];
                let remaining_b = tri[k];

                // If binary (-resolved, remaining_a) exists:
                // resolved → remaining_a. In ternary (resolved ∨ remaining_a ∨ remaining_b):
                //   if ¬resolved: remaining_a ∨ remaining_b must hold
                //   if resolved: remaining_a holds (from implication), so remaining_a ∨ remaining_b holds
                // Therefore (remaining_a ∨ remaining_b) is implied.
                let neg_has_a = binary_map
                    .get(&neg_resolved.index())
                    .is_some_and(|s| s.contains(&remaining_a));
                let neg_has_b = binary_map
                    .get(&neg_resolved.index())
                    .is_some_and(|s| s.contains(&remaining_b));
                let already_exists = binary_map
                    .get(&remaining_a.index())
                    .is_some_and(|s| s.contains(&remaining_b));

                if remaining_a.index() < num_lits
                    && remaining_b.index() < num_lits
                    && !already_exists
                    && (neg_has_a || neg_has_b)
                {
                    let new_idx = clauses.add(&[remaining_a, remaining_b], false);
                    binary_map
                        .entry(remaining_a.index())
                        .or_default()
                        .insert(remaining_b);
                    binary_map
                        .entry(remaining_b.index())
                        .or_default()
                        .insert(remaining_a);
                    new_binaries.push((new_idx, remaining_a, remaining_b));
                }
            }
        }

        if debug_congruence_enabled() && !new_binaries.is_empty() {
            let n = new_binaries.len();
            eprintln!("[congruence] hyper-ternary: derived {n} new binary clauses");
        }

        new_binaries
    }

    /// Build binary clause adjacency list into `cached_binary_adj`.
    ///
    /// Reuses cached storage across calls to avoid O(num_lits) fresh Vec
    /// allocations per call. On shuffling-2 (276K lits), this saves 276K
    /// allocations per round. Only irredundant (non-learned) binary clauses
    /// are included.
    pub(super) fn build_binary_adjacency_cached(&mut self, clauses: &ClauseArena) {
        let num_lits = self.num_vars * 2;
        self.cached_binary_adj.resize_with(num_lits, Vec::new);
        for v in self.cached_binary_adj.iter_mut().take(num_lits) {
            v.clear();
        }
        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) || clauses.is_learned(idx) {
                continue;
            }
            let lits = clauses.literals(idx);
            if lits.len() == 2 {
                let a = lits[0].index();
                let b = lits[1].index();
                if a < num_lits && b < num_lits {
                    self.cached_binary_adj[a].push(b);
                    self.cached_binary_adj[b].push(a);
                }
            }
        }
    }

    /// Binary complementary pair unit discovery using `cached_binary_adj`.
    ///
    /// For each literal `lit`, if binary clauses `(lit, y)` and `(lit, -y)` both
    /// exist, then `lit` is a forced unit (resolution yields the unit clause `(lit)`).
    /// This catches units from binary clause structure that gate-based analysis misses.
    ///
    /// CaDiCaL congruence.cpp:4360-4399 (find_units).
    pub(super) fn find_units_cached(&self) -> Vec<Literal> {
        let num_lits = self.num_vars * 2;
        let mut units = Vec::new();

        // For each literal, check if both y and -y appear as binary partners.
        let mut marked = vec![false; num_lits];
        for (lit_idx, adj) in self.cached_binary_adj.iter().enumerate().take(num_lits) {
            if adj.is_empty() {
                continue;
            }
            // Mark all partners of this literal.
            for &other in adj {
                marked[other] = true;
            }
            // Check if any partner's negation is also marked.
            let mut is_unit = false;
            for &other in adj {
                let neg_other = other ^ 1;
                if neg_other < num_lits && marked[neg_other] {
                    // (lit, other) and (lit, -other) → lit is unit
                    is_unit = true;
                    break;
                }
            }
            // Unmark all.
            for &other in adj {
                marked[other] = false;
            }
            if is_unit {
                let lit = Literal(lit_idx as u32);
                units.push(lit);
            }
        }

        if debug_congruence_enabled() && !units.is_empty() {
            let n = units.len();
            eprintln!(
                "[congruence] find_units: discovered {n} units from binary complementary pairs"
            );
        }

        units
    }

    /// Binary implication equivalence discovery using `cached_binary_adj`.
    ///
    /// For each variable `v` with `lit = pos(v)`:
    /// - Binary clause `(lit, a)` means `¬lit → a`
    /// - Binary clause `(¬lit, b)` means `lit → b`
    /// - If `¬b` was a partner of `lit` (i.e., `¬lit → ¬b`), then `lit → b`
    ///   and `¬lit → ¬b`, so `lit ≡ b`.
    ///
    /// CaDiCaL congruence.cpp:4401-4478 (find_equivalences).
    pub(super) fn find_equivalences_cached(
        &mut self,
        uf: &mut UnionFind,
        equivalence_edges: &mut Vec<(Literal, Literal)>,
        edge_provenance: &mut Vec<crate::congruence::EdgeProvenance>,
    ) -> Result<bool, Literal> {
        let num_lits = self.num_vars * 2;
        let mut marked = vec![false; num_lits];
        let mut found_any = false;

        for var in 0..self.num_vars {
            let lit = var * 2; // positive literal index
            let neg_lit = lit ^ 1; // negative literal index

            // Skip if no binary clauses on positive literal.
            if self.cached_binary_adj[lit].is_empty() {
                continue;
            }

            // Mark all partners of `lit` (binary clauses containing `lit`).
            // Each `(lit, other)` clause encodes implication `¬lit → other`.
            let mut analyzed: Vec<usize> = Vec::new();
            for i in 0..self.cached_binary_adj[lit].len() {
                let other = self.cached_binary_adj[lit][i];
                // CaDiCaL ordering filter: skip if lit has higher variable
                // index than other. This avoids double-processing symmetric
                // pairs and ensures the lower-index variable is the "source".
                if lit / 2 > other / 2 {
                    continue;
                }
                if !marked[other] {
                    marked[other] = true;
                    analyzed.push(other);
                }
            }

            if analyzed.is_empty() {
                continue;
            }

            // Scan binary clauses of `¬lit`. Each `(¬lit, other2)` encodes
            // implication `lit → other2`. If `¬other2` is marked, we have
            // both `¬lit → ¬other2` and `lit → other2`, proving `lit ≡ other2`.
            let mut restart = false;
            if neg_lit < self.cached_binary_adj.len() {
                for i in 0..self.cached_binary_adj[neg_lit].len() {
                    let other2 = self.cached_binary_adj[neg_lit][i];
                    // CaDiCaL ordering filter for negative literal.
                    if neg_lit / 2 > other2 / 2 {
                        continue;
                    }
                    let neg_other2 = other2 ^ 1;
                    if neg_other2 < num_lits && marked[neg_other2] {
                        // Found: (lit, ¬other2) and (¬lit, other2) → lit ≡ other2
                        let lit_repr = uf.find(lit);
                        let other2_repr = uf.find(other2);
                        if lit_repr != other2_repr {
                            match merge_or_contradict(
                                uf,
                                lit,
                                other2,
                                equivalence_edges,
                                crate::congruence::EdgeProvenance::Plain,
                                edge_provenance,
                                &mut self.stats,
                            ) {
                                Ok(true) => {
                                    found_any = true;
                                    // CaDiCaL: unmark_all + goto RESTART after merge,
                                    // since the merge may enable cascading equivalences.
                                    restart = true;
                                    break;
                                }
                                Ok(false) => {} // already equivalent
                                Err(unit) => {
                                    // Contradiction: literal merged with complement.
                                    // Clean up marks before returning.
                                    for &m in &analyzed {
                                        marked[m] = false;
                                    }
                                    return Err(unit);
                                }
                            }
                        }
                    }
                }
            }

            // Unmark all.
            for &m in &analyzed {
                marked[m] = false;
            }

            // CaDiCaL RESTART: after a merge, restart the variable scan from
            // the same variable to find cascading equivalences.
            if restart {
                // We can't use goto in Rust, so we use a continue-based approach:
                // The outer loop will advance to the next variable. CaDiCaL restarts
                // the same variable, but since the merge already happened, the key
                // effect is that subsequent variables see the updated UF state.
                // For simplicity, we don't re-scan the same variable — decompose()
                // will catch any cascading equivalences via SCC.
            }
        }

        if debug_congruence_enabled() && found_any {
            eprintln!(
                "[congruence] find_equivalences: discovered equivalences from binary implications"
            );
        }

        Ok(found_any)
    }
}
