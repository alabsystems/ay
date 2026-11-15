// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded re-solve loop for array functional-consistency refinement.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_sat::{SatResult, Solver as SatSolver};

use super::{CegarArrayCheck, Executor, FcAuditLits, NestedReadPaths};
use crate::executor::theories::ChainSpend;
use crate::executor_types::UnknownReason;

impl Executor {
    /// Audit and refine a candidate array model until FC is established.
    ///
    /// Every incomplete audit and every exhausted refinement budget fails
    /// closed to `Unknown`; an unchecked candidate is never published as SAT.
    /// Each re-solve continues the solve chain `spent` (P4a): it is armed
    /// with what the chain's earlier solves left of the `:rlimit` counts.
    pub(in crate::executor) fn refine_array_fc_model(
        &mut self,
        mut solve_result: SatResult,
        lits: &FcAuditLits<'_>,
        cross_pairs: &[(
            ay_core::TermId,
            ay_core::TermId,
            ay_core::TermId,
            Option<ay_core::TermId>,
        )],
        total_vars: u32,
        solver: &mut SatSolver,
        max_cegar_iterations: u32,
        spent: &mut ChainSpend,
    ) -> SatResult {
        let mut cegar_next_var = total_vars;
        let mut cegar_iteration = 0u32;
        let mut already_covered = HashSet::default();

        while let SatResult::Sat(ref model) = solve_result {
            if cegar_iteration >= max_cegar_iterations {
                // The last refinement produced a new model that has not yet
                // been audited. Only a complete, consistent audit may escape.
                // Nested read paths are refinement only: this last audit asks
                // the bit-level question alone, as it did before they were
                // refined, and model validation still judges them.
                let residual = self.check_array_fc_violations_with(
                    model,
                    lits,
                    cross_pairs,
                    cegar_next_var as usize,
                    &mut already_covered,
                    NestedReadPaths::Skip,
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
                lits,
                cross_pairs,
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

            solve_result = self.solve_sat_in_budget_chain(solver, spent);
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
            // #abv-subst-model-retry: an audit that could not establish
            // functional consistency withholds the candidate, which rejects
            // it as surely as a gate does, so it arms the preprocessing-free
            // re-solve like every other rejection of a substitution-lane
            // model (`check_sat/bv_subst_retry.rs`). A stop (deadline,
            // resource, memory, interrupt) is not a rejection and arms
            // nothing. Measured on the store-chain fuzz file q8822_246 (z3:
            // sat): its first solve ends here, and its `sat` came from that
            // re-solve, which only the validation failure on the solver's own
            // `distinct_const_array` axiom used to arm; that axiom now
            // evaluates exactly (#aufbv-const-array-equality).
            if self.bv_subst_lane {
                self.bv_subst_model_rejected = true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::executor::Executor;
    use crate::executor_types::UnknownReason;

    #[test]
    fn an_incomplete_audit_of_a_substitution_solve_arms_the_preprocessing_free_retry() {
        let mut executor = Executor::new();
        executor.bv_subst_lane = true;
        executor.note_incomplete_array_fc_audit();
        assert!(executor.bv_subst_model_rejected);
        assert_eq!(
            executor.last_unknown_reason,
            Some(UnknownReason::Incomplete)
        );
    }

    #[test]
    fn an_incomplete_audit_without_substitution_arms_nothing() {
        let mut executor = Executor::new();
        executor.note_incomplete_array_fc_audit();
        assert!(!executor.bv_subst_model_rejected);
        assert_eq!(
            executor.last_unknown_reason,
            Some(UnknownReason::Incomplete)
        );
    }

    #[test]
    fn an_audit_cut_short_by_a_stop_arms_nothing() {
        for stop in [
            UnknownReason::Timeout,
            UnknownReason::ResourceLimit,
            UnknownReason::MemoryLimit,
            UnknownReason::Interrupted,
        ] {
            let mut executor = Executor::new();
            executor.bv_subst_lane = true;
            executor.last_unknown_reason = Some(stop);
            executor.note_incomplete_array_fc_audit();
            assert!(!executor.bv_subst_model_rejected, "{stop:?}");
            assert_eq!(executor.last_unknown_reason, Some(stop));
        }
    }
}
