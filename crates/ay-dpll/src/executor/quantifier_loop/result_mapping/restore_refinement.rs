// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Result adoption for restored-quantifier MBQI refinement probes.

use super::*;

impl Executor {
    /// Adopt a checked replacement model, a definitive refutation, its
    /// fail-closed artifact downgrade, or an error from refinement. Only a
    /// fully restored `None` may continue with the predecessor model.
    pub(super) fn adopt_skipped_quantifier_refinement(
        &mut self,
        pre_restore_assertions: &[TermId],
        category: LogicCategory,
        final_result: &mut Result<SolveResult>,
    ) -> bool {
        let Some(refinement_result) =
            self.try_skipped_quantifier_mbqi_refinement(pre_restore_assertions, category)
        else {
            return false;
        };

        self.apply_skipped_quantifier_refinement_result(refinement_result, final_result);
        true
    }

    /// Check the grant after restoring the original hard roots. The authored
    /// window alone is insufficient here: the active stack must agree with it
    /// and this route does not transfer assumption or optimization queries.
    pub(super) fn restored_refinement_sat_model_is_current(&self) -> bool {
        if self.last_assumptions.is_some()
            || !self.ctx.objectives().is_empty()
            || !self.ctx.soft_constraints().is_empty()
        {
            return false;
        }
        let Ok(roots) = self.independent_gate_query_roots() else {
            return false;
        };
        self.ctx.assertions == roots
            && self.has_checked_model_bound_full_domain_sat_authority(&roots)
    }

    fn apply_skipped_quantifier_refinement_result(
        &mut self,
        refinement_result: Result<SolveResult>,
        final_result: &mut Result<SolveResult>,
    ) {
        match refinement_result {
            Ok(result @ (SolveResult::Unsat(_) | SolveResult::Unknown)) => {
                self.last_result = Some(result.clone());
                *final_result = Ok(result);
            }
            Err(error) => *final_result = Err(error),
            Ok(SolveResult::Sat) if self.restored_refinement_sat_model_is_current() => {
                self.last_result = Some(SolveResult::Sat);
                *final_result = Ok(SolveResult::Sat);
            }
            Ok(SolveResult::Sat) => {
                // A bare or stale probe verdict cannot replace the model.
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                self.last_result = Some(SolveResult::Unknown);
                *final_result = Ok(SolveResult::Unknown);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn artifact_downgrade_is_terminal_executor_state() {
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::unsat());
        exec.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
        let mut final_result = Ok(SolveResult::Sat);
        exec.apply_skipped_quantifier_refinement_result(
            Ok(SolveResult::Unknown),
            &mut final_result,
        );
        assert!(matches!(final_result, Ok(SolveResult::Unknown)));
        assert!(matches!(exec.last_result, Some(SolveResult::Unknown)));
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::QuantifierUnhandled)
        );
    }

    #[test]
    fn restored_refinement_cannot_adopt_an_unsealed_sat_result() {
        let mut exec = Executor::new();
        // Routing/validation markers alone do not name a checked model.
        exec.last_model_validated = true;
        exec.bv_quantifier_full_domain_proof = true;
        let mut result = Ok(SolveResult::Sat);
        exec.apply_skipped_quantifier_refinement_result(Ok(SolveResult::Sat), &mut result);
        assert!(matches!(result, Ok(SolveResult::Unknown)));
        assert!(matches!(exec.last_result, Some(SolveResult::Unknown)));
    }
}
