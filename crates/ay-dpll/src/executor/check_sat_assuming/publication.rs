// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ownership of SAT/Unknown publication across named-core retries.

use super::{Executor, Result, SolveResult, TermId};

/// Which public boundary owns SAT emission for an assumption solve.
///
/// Direct `check-sat-assuming` calls emit locally. Plain `check-sat`'s named
/// core redirect is already inside the outer solve pipeline, so it must return
/// a bare proposal and let that pipeline consume any affine certificate model
/// exactly once after the original assertion stack is restored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum AssumptionSatPublication {
    EmitHere,
    DeferToPlainCheckSat,
}

impl Executor {
    pub(super) fn publish_or_defer_assumption_sat(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        match publication {
            AssumptionSatPublication::EmitHere => {
                self.emit_sat_verdict(SolveResult::Sat, assumptions)
            }
            AssumptionSatPublication::DeferToPlainCheckSat => {
                self.last_sat_certificate = None;
                if self.ctx.assertions.is_empty() && assumptions.is_empty() {
                    self.last_model = Some(crate::executor::model::Model::empty());
                    self.last_model_validated = true;
                }
                Ok(SolveResult::Sat)
            }
        }
    }

    /// Publish a caller-visible Unknown, or retain a nested named-core
    /// strategy's provisional classification for its equivalent-query rescue.
    pub(super) fn finalize_assumption_unknown(
        &mut self,
        publication: AssumptionSatPublication,
    ) -> SolveResult {
        if publication == AssumptionSatPublication::EmitHere {
            self.finalize_unknown_publication(SolveResult::Unknown)
        } else {
            SolveResult::Unknown
        }
    }

    /// A nested strategy's Unknown must not revoke the enclosing query epoch.
    pub(super) fn finalize_assumption_result(
        &mut self,
        result: SolveResult,
        publication: AssumptionSatPublication,
    ) -> SolveResult {
        if result.is_unknown() {
            self.finalize_assumption_unknown(publication)
        } else {
            self.finalize_unknown_publication(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor_types::UnknownOrigin;

    #[test]
    fn deferred_publication_carries_ground_candidate_to_outer_sat_funnel() {
        let mut exec = Executor::new();
        let named_assertion = exec.ctx.terms.true_term();
        exec.last_model = Some(crate::executor::model::Model::empty());
        exec.last_model_validated = false;

        let proposed = exec
            .publish_or_defer_assumption_sat(
                &[named_assertion],
                AssumptionSatPublication::DeferToPlainCheckSat,
            )
            .expect("deferred publication does not error");

        assert_eq!(proposed, SolveResult::Sat);
        assert!(exec.last_model.is_some());
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());

        // Plain check-sat restores the original named assertion stack before
        // consuming the proposal through its sole public SAT funnel.
        exec.ctx.assertions.push(named_assertion);
        let emitted = exec
            .emit_sat_verdict(proposed, &[])
            .expect("outer SAT funnel does not error");
        assert_eq!(emitted, SolveResult::Sat);
        assert!(exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_some());
    }

    #[test]
    fn named_core_attempt_defers_unknown_revocation_to_outer_boundary() {
        let mut exec = Executor::new();
        exec.begin_external_decision_query(false);
        exec.bind_unsat_query_assumptions(&[]);
        assert!(exec.unsat_query_epoch.is_some());
        exec.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);

        let provisional = exec.finish_check_sat_assuming_result(
            &[],
            SolveResult::Unknown,
            AssumptionSatPublication::DeferToPlainCheckSat,
        );
        assert_eq!(provisional, SolveResult::Unknown);
        assert!(
            exec.unsat_query_epoch.is_some(),
            "an internal strategy must not revoke its enclosing public query"
        );
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert!(exec.last_model.is_none());

        let published = exec.finalize_unknown_publication(provisional);
        assert_eq!(published, SolveResult::Unknown);
        assert!(exec.unsat_query_epoch.is_none());
        assert_eq!(
            exec.unknown_origin(),
            Some(UnknownOrigin::IncompleteSolverLane)
        );
    }
}
