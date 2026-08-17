// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded re-solve loop for array functional-consistency refinement.

use ay_bv::BvBits;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;
use ay_sat::{SatResult, Solver as SatSolver};

use super::{CegarArrayCheck, Executor};
use crate::executor_types::UnknownReason;

impl Executor {
    /// Audit and refine a candidate array model until FC is established.
    ///
    /// Every incomplete audit and every exhausted refinement budget fails
    /// closed to `Unknown`; an unchecked candidate is never published as SAT.
    pub(in crate::executor) fn refine_array_fc_model(
        &mut self,
        mut solve_result: SatResult,
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        total_vars: u32,
        solver: &mut SatSolver,
        max_cegar_iterations: u32,
    ) -> SatResult {
        let mut cegar_next_var = total_vars;
        let mut cegar_iteration = 0u32;
        let mut already_covered = HashSet::default();

        while let SatResult::Sat(ref model) = solve_result {
            if cegar_iteration >= max_cegar_iterations {
                // The last refinement produced a new model that has not yet
                // been audited. Only a complete, consistent audit may escape.
                let residual = self.check_array_fc_violations(
                    model,
                    term_bits,
                    var_offset,
                    cegar_next_var as usize,
                    &mut already_covered,
                );
                if !matches!(residual, CegarArrayCheck::Consistent) {
                    self.note_incomplete_array_fc_audit();
                    solve_result = SatResult::Unknown;
                }
                break;
            }
            if self.should_abort_theory_loop() {
                solve_result = SatResult::Unknown;
                break;
            }

            let result = match self.check_array_fc_violations(
                model,
                term_bits,
                var_offset,
                cegar_next_var as usize,
                &mut already_covered,
            ) {
                CegarArrayCheck::Consistent => break,
                CegarArrayCheck::Refinement(result) => result,
                CegarArrayCheck::Incomplete => {
                    self.note_incomplete_array_fc_audit();
                    solve_result = SatResult::Unknown;
                    break;
                }
            };

            cegar_iteration += 1;
            let Ok(num_new_vars) = u32::try_from(result.num_new_vars) else {
                self.note_incomplete_array_fc_audit();
                solve_result = SatResult::Unknown;
                break;
            };
            let Some(next_var) = cegar_next_var.checked_add(num_new_vars) else {
                self.note_incomplete_array_fc_audit();
                solve_result = SatResult::Unknown;
                break;
            };
            cegar_next_var = next_var;
            let max_var = result
                .clauses
                .iter()
                .flat_map(|clause| clause.iter())
                .map(|literal| literal.variable().index() + 1)
                .max()
                .unwrap_or(0);
            solver.ensure_num_vars(max_var);
            for clause in result.clauses {
                solver.add_clause(clause);
            }

            let should_stop = self.make_should_stop();
            solve_result = solver.solve_interruptible(should_stop).into_inner();
            collect_sat_stats!(self, &solver);
        }
        let prior_rounds = self
            .last_statistics
            .get_int("smt.abv.array_fc_cegar.refinement_rounds")
            .unwrap_or(0);
        self.last_statistics.set_int(
            "smt.abv.array_fc_cegar.refinement_rounds",
            prior_rounds.saturating_add(u64::from(cegar_iteration)),
        );
        solve_result
    }

    fn note_incomplete_array_fc_audit(&mut self) {
        if !matches!(
            self.last_unknown_reason,
            Some(
                UnknownReason::Timeout
                    | UnknownReason::ResourceLimit
                    | UnknownReason::MemoryLimit
                    | UnknownReason::Interrupted
            )
        ) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
    }
}
