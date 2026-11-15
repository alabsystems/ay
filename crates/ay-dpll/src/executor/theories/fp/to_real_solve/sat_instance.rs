// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One budgeted SAT solve in an FP-to-Real refinement chain.

use ay_sat::Solver as SatSolver;

use super::super::super::ChainSpend;
use super::*;

impl Executor {
    /// Build and solve a SAT instance from base + blocking clauses.
    ///
    /// `chain_spent` is the running work total of THIS refinement chain: each
    /// call arms the fresh solver with the remaining `:rlimit` allowances
    /// (#8749 conflicts, P4a decisions; FP lane) and debits its own work, so
    /// the chain total — not each fresh solver individually — is what the
    /// budget bounds.
    pub(super) fn solve_fp_sat_controlled(
        &mut self,
        base_clauses: &[CnfClause],
        blocking_clauses: &[CnfClause],
        total_vars: usize,
        chain_spent: &mut ChainSpend,
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
        search: FpRealPhase,
    ) -> std::result::Result<SatResult, UnknownOrigin> {
        self.fp_real_checkpoint(stop, observe, FpRealPhase::SatLoad)?;
        if total_vars > i32::MAX as usize {
            return Err(stop.refuse(UnknownOrigin::DeterministicResourceBudget));
        }
        let mut solver = SatSolver::new(total_vars);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        // Adaptive reorder gate for large FP instances (#8118).
        if total_vars > 50_000 && !matches!(search, FpRealPhase::SimpleSearch) {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }
        for clause in base_clauses.iter().chain(blocking_clauses.iter()) {
            self.fp_real_checkpoint(stop, observe, FpRealPhase::SatLoad)?;
            let mut lits = Vec::new();
            for (index, &lit) in clause.literals().iter().enumerate() {
                if index % 256 == 0 {
                    stop.check()?;
                }
                lits.push(crate::cnf_lit_to_sat(lit));
            }
            solver.add_clause(lits);
            stop.check()?;
        }

        self.arm_sat_count_budget(&mut solver, *chain_spent);
        self.fp_real_checkpoint(stop, observe, search)?;
        let result = self.solve_sat_under_query_stop(&mut solver, || {
            observe(FpRealPhase::SatPoll);
            stop.should_stop()
        });
        collect_sat_stats!(self, &solver);
        chain_spent.debit(&solver);
        self.capture_fp_sat_unknown(&result, solver.last_unknown_reason(), stop);
        self.fp_real_checkpoint(stop, observe, FpRealPhase::SatReturned)?;
        Ok(result)
    }
}
