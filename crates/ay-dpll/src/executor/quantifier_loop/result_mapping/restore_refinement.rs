// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Result adoption for restored-quantifier MBQI refinement probes.

use super::*;

impl Executor {
    /// Adopt a definitive refutation, its fail-closed artifact downgrade, or
    /// an error from a disposable restored-quantifier refinement probe. The
    /// downgrade is terminal because that path consumed the predecessor state;
    /// only a fully restored `None` may continue to a SAT-certification arm.
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
            Ok(SolveResult::Sat) => {
                // The probe currently restores and maps inner SAT to `None`.
                // If that contract ever changes, do not risk continuing from
                // an unclassified state: stop at the fail-closed verdict.
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
}
