// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Session ownership and policy for affine-aggregation replay artifacts.

use super::*;

impl BabSession {
    /// Exact affine-aggregation replay artifact produced by the last check.
    ///
    /// An unsupported inner proof can still export a source-checked primal
    /// point, but makes no optimality or infeasibility claim on its own.
    #[must_use]
    pub fn affine_aggregation_certificate(&self) -> Option<&crate::AffineAggregationCertificate> {
        self.affine_aggregation_certificate.as_ref()
    }

    pub(super) fn clear_affine_evidence(&mut self) {
        self.affine_aggregation_certificate = None;
        self.affine_aggregation_verification = None;
        crate::presolve::implied_free::clear_pending_certificate();
    }

    /// Drain, pair, and independently replay the artifact from native search.
    ///
    /// Affine aggregation keeps reduced-frame proof indices out of `Outcome`.
    /// Retain its side artifact only when the claim agrees with the raw verdict
    /// and a threshold-free rebuild of the ordered transform verifies against
    /// this session's source model.
    pub(super) fn capture_affine_certificate(&mut self, raw: &Outcome) {
        let Some(certificate) = crate::presolve::implied_free::take_pending_certificate() else {
            return;
        };
        let paired = matches!(
            (certificate.claim(), raw),
            (
                crate::AffineAggregationClaim::Infeasible,
                Outcome::Infeasible { .. }
            ) | (
                crate::AffineAggregationClaim::Optimal { .. },
                Outcome::Optimal { .. }
            ) | (
                crate::AffineAggregationClaim::Feasible,
                Outcome::Optimal { .. } | Outcome::Feasible { .. }
            )
        );
        if !paired {
            return;
        }
        if let Ok(verification) = certificate.verify(&self.model) {
            self.affine_aggregation_verification = Some(verification);
            self.affine_aggregation_certificate = Some(certificate);
        }
    }

    pub(super) fn affine_infeasibility_verified(&self) -> bool {
        self.affine_aggregation_verification
            .is_some_and(|verification| verification.infeasibility_verified)
    }
}

/// Apply the strongest independently checked native-side evidence available.
pub(super) fn finish_native_outcome(
    outcome: Outcome,
    model: &Model,
    solved: &SolvedObjective<'_>,
    opts: &SolveOpts,
    original_margin_tree_verified: bool,
    parity_infeasibility_verified: bool,
    affine_verification: Option<crate::AffineAggregationVerification>,
) -> Outcome {
    if original_margin_tree_verified {
        return outcome;
    }
    if parity_infeasibility_verified {
        return finish_exact_reduction_with_supplemental_proof(
            outcome,
            model,
            solved,
            opts,
            SupplementalProof::VerifiedParityInfeasibility,
        );
    }
    let supplemental = affine_verification.and_then(|verification| {
        if outcome.is_infeasible() && verification.infeasibility_verified {
            Some(SupplementalProof::VerifiedAffineAggregationInfeasibility)
        } else if matches!(&outcome, Outcome::Optimal { .. }) && verification.optimality_verified {
            Some(SupplementalProof::VerifiedAffineAggregationOptimality)
        } else {
            None
        }
    });
    match supplemental {
        Some(proof) => {
            finish_exact_reduction_with_supplemental_proof(outcome, model, solved, opts, proof)
        }
        None => finish(outcome, model, solved, opts),
    }
}
