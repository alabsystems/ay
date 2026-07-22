// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equivalence rewriting: union-find lit_map construction and rewrite stats.

use super::Sweeper;
use crate::clause_arena::ClauseArena;
use crate::lit_marks::ClauseRewriteOutcome;
use crate::literal::Literal;

impl Sweeper {
    /// Build a lit_map from collected equivalences using union-find.
    pub(super) fn build_lit_map_from_equivalences(
        &mut self,
        equivalences: &[(u32, u32)],
        frozen: &[u32],
        num_lits: usize,
    ) -> Vec<Literal> {
        if equivalences.is_empty() {
            return Vec::new();
        }

        // Union-find: parent[lit] = parent literal.
        let mut parent: Vec<u32> = (0..num_lits as u32).collect();

        fn find(parent: &mut [u32], mut x: u32) -> u32 {
            while parent[x as usize] != x {
                parent[x as usize] = parent[parent[x as usize] as usize]; // path compression
                x = parent[x as usize];
            }
            x
        }

        fn union(parent: &mut [u32], a: u32, b: u32) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                // Canonical: use smaller index as representative.
                if ra < rb {
                    parent[rb as usize] = ra;
                    // Also union the negations for consistency.
                    let nra = find(parent, ra ^ 1);
                    let nrb = find(parent, rb ^ 1);
                    if nra != nrb {
                        if nra < nrb {
                            parent[nrb as usize] = nra;
                        } else {
                            parent[nra as usize] = nrb;
                        }
                    }
                } else {
                    parent[ra as usize] = rb;
                    let nra = find(parent, ra ^ 1);
                    let nrb = find(parent, rb ^ 1);
                    if nra != nrb {
                        if nrb < nra {
                            parent[nra as usize] = nrb;
                        } else {
                            parent[nrb as usize] = nra;
                        }
                    }
                }
            }
        }

        for &(a, b) in equivalences {
            if (a as usize) < num_lits && (b as usize) < num_lits {
                union(&mut parent, a, b);
            }
        }

        #[cfg(debug_assertions)]
        {
            for i in (0..num_lits).step_by(2) {
                let pos_repr = find(&mut parent, i as u32);
                let neg_repr = find(&mut parent, (i as u32) ^ 1);
                debug_assert_eq!(
                    pos_repr ^ 1,
                    neg_repr,
                    "BUG: negation invariant violated for var {}: +repr={}, -repr={}",
                    i / 2,
                    pos_repr,
                    neg_repr
                );
            }

            for i in 0..num_lits {
                let repr = find(&mut parent, i as u32);
                let neg_repr = find(&mut parent, (i as u32) ^ 1);
                debug_assert_ne!(
                    repr,
                    neg_repr,
                    "BUG: variable {} maps to same representative as its negation",
                    i / 2
                );
            }
        }

        // Build lit_map: each literal maps to its representative.
        let mut lit_map = Vec::with_capacity(num_lits);
        let mut any_non_identity = false;
        for i in 0..num_lits {
            let var_idx = i / 2;
            // Frozen variables must be self-mapped.
            if var_idx < frozen.len() && frozen[var_idx] > 0 {
                lit_map.push(Literal(i as u32));
                continue;
            }
            let rep = find(&mut parent, i as u32);
            if rep != i as u32 {
                any_non_identity = true;
            }
            lit_map.push(Literal(rep));
        }

        if !any_non_identity {
            return Vec::new(); // No equivalences → return empty map
        }
        lit_map
    }

    /// Count clause rewriting stats without modifying the arena.
    pub(super) fn count_rewrite_stats(&mut self, clauses: &ClauseArena, lit_map: &[Literal]) {
        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) {
                continue;
            }

            let old_lits = clauses.literals(idx);
            match self
                .marks
                .rewrite_clause(old_lits, lit_map, &[], &mut self.scratch)
            {
                ClauseRewriteOutcome::Tautology | ClauseRewriteOutcome::Satisfied => {
                    self.stats.clauses_deleted_tautology += 1;
                }
                ClauseRewriteOutcome::Empty => {
                    self.stats.clauses_became_empty += 1;
                }
                ClauseRewriteOutcome::Unit(_) => {
                    self.stats.clauses_became_unit += 1;
                }
                ClauseRewriteOutcome::Changed => {
                    self.stats.clauses_rewritten += 1;
                }
                ClauseRewriteOutcome::Unchanged => {}
            }
        }
    }
}
