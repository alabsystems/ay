// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cone-of-Influence (COI) construction for kitten-based sweep.

use super::{Sweeper, COI_CLAUSE_LIMIT, COI_DEPTH_LIMIT, COI_VAR_LIMIT};
use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::occ_list::OccList;

impl Sweeper {
    /// Build a Cone-of-Influence environment for `start_var` in the kitten
    /// sub-solver. Returns the number of clauses fed to kitten.
    ///
    /// BFS expansion from `start_var`: add all clauses containing the variable,
    /// then all variables in those clauses, then clauses containing those
    /// variables, etc., up to depth and variable limits.
    ///
    /// Reference: CaDiCaL sweep.cpp lines 1540-1593.
    pub(super) fn build_coi(
        &mut self,
        start_var: usize,
        arena: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
    ) -> usize {
        let coi_var_limit = std::env::var("AY_AB_COI_VARS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(COI_VAR_LIMIT);
        let coi_depth_limit: u32 = std::env::var("AY_AB_COI_DEPTH")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(COI_DEPTH_LIMIT);
        self.kitten.clear();
        self.coi_vars.clear();
        self.coi_clauses.clear();

        // Mark start variable.
        self.coi_depths[start_var] = 1;
        self.coi_vars.push(start_var);

        let mut expand = 0;
        let mut next_layer_start = 1;
        let mut depth: u32 = 1;
        let mut encoded: usize = 0;

        while expand < self.coi_vars.len() {
            if encoded >= COI_CLAUSE_LIMIT {
                break;
            }
            if expand == next_layer_start {
                if depth >= coi_depth_limit {
                    break;
                }
                next_layer_start = self.coi_vars.len();
                if expand == next_layer_start {
                    break;
                }
                depth += 1;
            }
            let var_idx = self.coi_vars[expand];
            expand += 1;

            // Add all clauses containing this variable (both polarities).
            for sign in 0..2u32 {
                let lit = Literal(var_idx as u32 * 2 + sign);
                for &clause_idx in occ.get(lit) {
                    if self.coi_vars.len() >= coi_var_limit {
                        break;
                    }
                    if encoded >= COI_CLAUSE_LIMIT {
                        break;
                    }
                    if arena.is_garbage(clause_idx) || arena.is_empty_clause(clause_idx) {
                        continue;
                    }
                    // CaDiCaL can_sweep_clause (sweep.cpp:64-70): only feed
                    // irredundant clauses and binary learned clauses. Large
                    // learned clauses are heuristically strengthened and their
                    // interactions with kitten probing are untested.
                    if arena.is_learned(clause_idx) && arena.len_of(clause_idx) > 2 {
                        continue;
                    }
                    // O(1) duplicate check (HashSet replaces O(n) Vec::contains).
                    if !self.coi_clauses.insert(clause_idx) {
                        continue;
                    }

                    // Feed clause to kitten (skip satisfied clauses, remove falsified lits).
                    let lits = arena.literals(clause_idx);
                    let mut satisfied = false;
                    let mut ext_lits: Vec<u32> = Vec::new();
                    for &l in lits {
                        let li = l.index();
                        if li < vals.len() {
                            if vals[li] > 0 {
                                // Literal is satisfied → entire clause is true, skip it.
                                satisfied = true;
                                break;
                            }
                            if vals[li] < 0 {
                                // Literal is falsified → remove from clause.
                                continue;
                            }
                        }
                        ext_lits.push(l.0);
                    }
                    if satisfied {
                        self.coi_clauses.remove(&clause_idx);
                        continue;
                    }
                    self.kitten
                        .add_clause_with_id(clause_idx as u32, &ext_lits, u32::MAX);
                    encoded += 1;

                    // Add new variables from this clause to the COI.
                    for &l in lits {
                        let v = l.variable().index();
                        if v < self.coi_depths.len()
                            && self.coi_depths[v] == 0
                            && v < vals.len() / 2
                            && vals[v * 2] == 0
                        {
                            self.coi_depths[v] = depth + 1;
                            self.coi_vars.push(v);
                        }
                    }
                }
            }
        }

        encoded
    }

    /// Clear COI working state after processing one variable.
    ///
    /// CaDiCaL sweep.cpp:294-313 clear_sweeper(): calls kitten_clear() to wipe
    /// all solver state between variables. Without this, level-0 propagations
    /// from variable A's COI contaminate variable B's clause simplification
    /// (add_clause_with_id removes falsified literals using kitten's values[]).
    /// This produces false backbone/equivalence claims because B's clauses are
    /// over-simplified by A's local implications that don't hold globally.
    pub(super) fn clear_coi(&mut self) {
        self.kitten.clear();
        for &v in &self.coi_vars {
            if v < self.coi_depths.len() {
                self.coi_depths[v] = 0;
            }
        }
        self.coi_vars.clear();
        self.coi_clauses.clear();
    }
}
