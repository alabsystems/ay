// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One budgeted SAT solve in an FP-to-Real refinement chain.

use ay_sat::Solver as SatSolver;

use super::*;

impl Executor {
    /// Build and solve a SAT instance from base + blocking clauses.
    ///
    /// `chain_conflicts_consumed` is the running conflict total of THIS
    /// refinement chain: each call arms the fresh solver with the remaining
    /// `:rlimit` allowance (#8749, FP lane) and adds its own conflicts to the
    /// accumulator, so the chain total — not each fresh solver individually —
    /// is what the budget bounds.
    pub(super) fn solve_fp_sat(
        &mut self,
        base_clauses: &[CnfClause],
        blocking_clauses: &[CnfClause],
        total_vars: usize,
        chain_conflicts_consumed: &mut u64,
    ) -> SatResult {
        let mut solver = SatSolver::new(total_vars);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        // Adaptive reorder gate for large FP instances (#8118).
        if total_vars > 50_000 {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }
        for clause in base_clauses.iter().chain(blocking_clauses.iter()) {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            solver.add_clause(lits);
        }

        self.solve_sat_in_budget_chain(&mut solver, chain_conflicts_consumed)
    }
}
