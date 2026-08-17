// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DFS traversal of reason graphs for literals removed by minimization.

use super::super::*;

impl Solver {
    /// Return reason IDs in post-order and collect materialized level-0 units.
    pub(super) fn dfs_minimize_chain(
        &mut self,
        original_learned: &[Literal],
        num_vars: usize,
        level0_vars: &mut Vec<usize>,
    ) -> Vec<u64> {
        let mut chain = Vec::new();
        for &lit in original_learned {
            let var_idx = lit.variable().index();
            if var_idx >= num_vars
                || self.min.minimize_flags[var_idx] & LRAT_A != 0
                || self.min.minimize_flags[var_idx] & LRAT_B != 0
            {
                continue;
            }
            self.dfs_minimize_visit(var_idx, num_vars, &mut chain, level0_vars);
        }
        chain
    }

    /// Visit one removed literal's reason graph using explicit post-visit marks.
    fn dfs_minimize_visit(
        &mut self,
        root: usize,
        num_vars: usize,
        chain: &mut Vec<u64>,
        level0_vars: &mut Vec<usize>,
    ) {
        let mut stack = vec![root];
        while let Some(entry) = stack.pop() {
            if entry >= usize::MAX / 2 {
                let var_idx = usize::MAX - entry;
                if let Some(reason_ref) = self.var_reason(var_idx) {
                    let id = self.clause_id(reason_ref);
                    if id != 0 {
                        chain.push(id);
                    }
                }
                continue;
            }
            let var_idx = entry;
            if var_idx >= num_vars || self.min.minimize_flags[var_idx] & LRAT_B != 0 {
                continue;
            }
            self.min.minimize_flags[var_idx] |= LRAT_B;
            self.min.lrat_to_clear.push(var_idx);
            if self.var_data[var_idx].level == 0
                && self.level0_minimize_chain_proof_id(var_idx).is_some()
            {
                // Route authenticated root units through the unit chain so
                // they precede non-unit minimize reasons after reversal.
                level0_vars.push(var_idx);
                continue;
            }
            let Some(reason_ref) = self.var_reason(var_idx) else {
                continue;
            };
            stack.push(usize::MAX - var_idx);
            let clause_idx = reason_ref.0 as usize;
            for &reason_lit in self.arena.literals(clause_idx) {
                let reason_var = reason_lit.variable().index();
                if reason_var != var_idx
                    && reason_var < num_vars
                    && self.min.minimize_flags[reason_var] & LRAT_B == 0
                {
                    stack.push(reason_var);
                }
            }
        }
    }
}
