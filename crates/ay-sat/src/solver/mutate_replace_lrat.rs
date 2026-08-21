// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT hint computation for clause replacement.
//!
//! Contains `replace_clause_impl` (computes LRAT hint chains from level-0
//! reason graphs) and `collect_level0_reason_chain` (BFS transitive closure
//! over level-0 variables for explicit hint construction).
//!
//! Extracted from `mutate_replace.rs` to keep each file under 500 lines.
//! The core replacement API (wrappers, `replace_clause_core`) remains in
//! `mutate_replace.rs`.

use super::*;
use crate::solver::mutate::ReplaceResult;

impl Solver {
    /// Collect transitive level-0 reason chain for LRAT hint construction.
    ///
    /// BFS through level-0 reason clauses starting from `seed_vars`, excluding
    /// variables in `exclude_vars` (which are already in the new clause). Returns
    /// proof IDs in trail-forward order (LRAT checker processing order).
    ///
    /// CaDiCaL reference: elim.cpp:303-308,349-350 (#5026).
    pub(super) fn collect_level0_reason_chain(
        &mut self,
        seed_vars: &[usize],
        exclude_vars: &[usize],
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        let num_vars = self.num_vars;
        debug_assert!(self.min.lrat_to_clear.is_empty());

        // Mark excluded variables (in new clause — checker already knows them).
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] |= LRAT_B;
            }
        }

        // Phase 1: Seed the BFS with the given variables.
        for &vi in seed_vars {
            if vi < num_vars
                && self.var_data[vi].level == 0
                && self.has_any_proof_id(vi)
                && self.min.minimize_flags[vi] & (LRAT_A | LRAT_B) == 0
            {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        // Phase 2: BFS transitive closure on level-0 variables.
        let mut head = 0;
        while head < self.min.lrat_to_clear.len() {
            let vi = self.min.lrat_to_clear[head];
            head += 1;
            let Some(reason_ref) = self.var_reason(vi) else {
                continue;
            };
            let ci = reason_ref.0 as usize;
            if ci >= self.arena.len() {
                continue;
            }
            let clen = self.arena.len_of(ci);
            for li in 0..clen {
                let rl = self.arena.literal(ci, li);
                let rv = rl.variable().index();
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

        // Phase 3: Collect proof IDs in trail-forward order (LRAT checker
        // processing order). Earlier trail variables are dependencies of later
        // ones, so they must appear first in the hint chain.
        let mut hints = Vec::new();
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx < num_vars && self.min.minimize_flags[var_idx] & LRAT_A != 0 {
                if let Some(id) = self.level0_var_proof_id(var_idx) {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
        }

        // Sparse cleanup.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &vi in exclude_vars {
            if vi < num_vars {
                self.min.minimize_flags[vi] &= !LRAT_B;
            }
        }

        hints
    }
}

mod finish_clause;
mod replace_clause;
mod replace_clause_emit;
mod replace_clause_hints;
mod replace_clause_prepare;
