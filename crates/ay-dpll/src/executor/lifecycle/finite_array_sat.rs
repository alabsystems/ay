// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownOrigin};

impl Executor {
    /// Fail closed when a provisional SAT was obtained before exact finite-array
    /// expansion finished for the current external decision query.
    ///
    /// The finite-array generator may emit a sound prefix when its deterministic
    /// aggregate budget is exhausted. That prefix can still authorize UNSAT, but
    /// never SAT. Every route that can observe such a provisional SAT funnels
    /// through this transition so no model, validation marker, result token, or
    /// quantified-SAT grant survives the downgrade while an internal retry is
    /// still deciding what to do next.
    ///
    /// Returns `true` exactly when `provisional_sat` was revoked.
    pub(in crate::executor) fn revoke_provisional_sat_if_finite_array_incomplete(
        &mut self,
        provisional_sat: bool,
    ) -> bool {
        if !provisional_sat || self.finite_array_expansion.is_complete() {
            return false;
        }

        // Keep one artifact-revocation policy. Besides the obvious model and
        // validation fields, the canonical publisher retires proofs, cores,
        // SAT/UNSAT transport, quantifier grants, trace provenance, and
        // optimization artifacts that a hand-maintained subset can miss.
        self.publish_unknown_from_origin(UnknownOrigin::DeterministicResourceBudget);
        true
    }

    /// Apply [`Self::revoke_provisional_sat_if_finite_array_incomplete`] to a
    /// solver proposal while preserving non-SAT verdicts and executor errors.
    pub(in crate::executor) fn fail_close_incomplete_finite_array_sat(
        &mut self,
        result: Result<SolveResult>,
    ) -> Result<SolveResult> {
        if matches!(&result, Ok(SolveResult::Sat))
            && self.revoke_provisional_sat_if_finite_array_incomplete(true)
        {
            Ok(SolveResult::Unknown)
        } else {
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Executor, SolveResult, UnknownOrigin};
    use crate::executor::model::Model;
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::Proof;

    #[test]
    fn incomplete_finite_array_sat_uses_canonical_artifact_revocation() {
        let mut executor = Executor::new();
        executor.finite_array_expansion.candidate_scan_truncated = true;
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model = Some(Model::empty());
        executor.last_model_validated = true;
        executor.last_sat_certificate = None;
        executor.last_assumptions = Some(Vec::new());
        executor.last_assumption_core = Some(Vec::new());
        executor.last_proof = Some(Proof::new());
        executor.last_negations = Some(HashMap::default());
        executor.proof_check_ok = true;
        executor.last_bv_drat_self_cert = true;

        assert!(executor.revoke_provisional_sat_if_finite_array_incomplete(true));

        assert!(executor.last_result_is_unknown());
        assert_eq!(
            executor.unknown_origin(),
            Some(UnknownOrigin::DeterministicResourceBudget)
        );
        assert!(executor.last_model.is_none());
        assert!(!executor.last_model_validated);
        assert!(executor.last_assumptions.is_none());
        assert!(executor.last_assumption_core.is_none());
        assert!(executor.last_proof.is_none());
        assert!(executor.last_negations.is_none());
        assert!(!executor.proof_check_ok);
        assert!(!executor.last_bv_drat_self_cert);
    }
}
