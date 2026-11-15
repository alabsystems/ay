// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently checked evidence carried beside a solver outcome.

/// The supplemental artifact selected by the last completed session check's
/// infeasibility finalizer.
///
/// This is diagnostic attribution, not a certificate or verification token.
/// Independently replay the corresponding artifact against the caller's model
/// before using its evidence. Ordinary root/tree certificates are carried in
/// `Outcome` and do not have a supplemental kind here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InfeasibilityEvidenceKind {
    /// Exact SAT/ReLU projection and checked RUP refutation.
    SatRelu,
    /// Checked affine reduction with infeasibility evidence in its reduced frame.
    AffineAggregation,
    /// Exact source-row GF(2) contradiction.
    Parity,
    /// Checked network-design projection refutation.
    NetworkDesign,
    /// Exact single-row pseudo-Boolean dynamic-programming refutation.
    SingleRowDp,
    /// Exact multi-row pseudo-Boolean decision-DAG refutation.
    MultiRowBdd,
    /// Single-row refutation over a rebuilt open-domain residual.
    OpenDomainSingleRowDp,
    /// Multi-row refutation over a rebuilt open-domain residual.
    OpenDomainMultiRowBdd,
    /// Hybrid PB/LP refutation over a rebuilt open-domain residual.
    OpenDomainHybridPbLp,
    /// Integer-lifted hybrid refutation over a rebuilt open-domain residual.
    OpenDomainHybridIntegerLift,
    /// Checked binary-master / continuous-recourse cut-ledger refutation.
    HybridPbLp,
    /// Checked bounded-integer lift and nested hybrid refutation.
    HybridIntegerLift,
}

/// Most proof objects live directly in the outcome. Exact reduction artifacts
/// have typed export channels and must be named explicitly at the policy gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SupplementalProof {
    None,
    VerifiedSatReluInfeasibility,
    VerifiedBlockAngularOptimality,
    VerifiedAffineAggregationInfeasibility,
    VerifiedAffineAggregationOptimality,
    VerifiedParityInfeasibility,
    VerifiedNetworkDesignInfeasibility,
    VerifiedNetworkDesignOptimality,
    VerifiedSingleMachineSchedulingOptimality,
    VerifiedSingleRowDpInfeasibility,
    VerifiedMultiRowBddInfeasibility,
    VerifiedOpenDomainSingleRowDpInfeasibility,
    VerifiedOpenDomainMultiRowBddInfeasibility,
    VerifiedOpenDomainHybridPbLpInfeasibility,
    VerifiedOpenDomainHybridIntegerLiftInfeasibility,
    VerifiedHybridPbLpInfeasibility,
    VerifiedHybridIntegerLiftInfeasibility,
}

impl SupplementalProof {
    pub(super) fn infeasibility_kind(self) -> Option<InfeasibilityEvidenceKind> {
        use InfeasibilityEvidenceKind as Kind;
        Some(match self {
            Self::VerifiedSatReluInfeasibility => Kind::SatRelu,
            Self::VerifiedAffineAggregationInfeasibility => Kind::AffineAggregation,
            Self::VerifiedParityInfeasibility => Kind::Parity,
            Self::VerifiedNetworkDesignInfeasibility => Kind::NetworkDesign,
            Self::VerifiedSingleRowDpInfeasibility => Kind::SingleRowDp,
            Self::VerifiedMultiRowBddInfeasibility => Kind::MultiRowBdd,
            Self::VerifiedOpenDomainSingleRowDpInfeasibility => Kind::OpenDomainSingleRowDp,
            Self::VerifiedOpenDomainMultiRowBddInfeasibility => Kind::OpenDomainMultiRowBdd,
            Self::VerifiedOpenDomainHybridPbLpInfeasibility => Kind::OpenDomainHybridPbLp,
            Self::VerifiedOpenDomainHybridIntegerLiftInfeasibility => {
                Kind::OpenDomainHybridIntegerLift
            }
            Self::VerifiedHybridPbLpInfeasibility => Kind::HybridPbLp,
            Self::VerifiedHybridIntegerLiftInfeasibility => Kind::HybridIntegerLift,
            Self::None
            | Self::VerifiedBlockAngularOptimality
            | Self::VerifiedAffineAggregationOptimality
            | Self::VerifiedNetworkDesignOptimality
            | Self::VerifiedSingleMachineSchedulingOptimality => return None,
        })
    }

    pub(super) fn certifies_infeasibility(self) -> bool {
        matches!(
            self,
            Self::VerifiedSatReluInfeasibility
                | Self::VerifiedAffineAggregationInfeasibility
                | Self::VerifiedParityInfeasibility
                | Self::VerifiedNetworkDesignInfeasibility
                | Self::VerifiedSingleRowDpInfeasibility
                | Self::VerifiedMultiRowBddInfeasibility
                | Self::VerifiedOpenDomainSingleRowDpInfeasibility
                | Self::VerifiedOpenDomainMultiRowBddInfeasibility
                | Self::VerifiedOpenDomainHybridPbLpInfeasibility
                | Self::VerifiedOpenDomainHybridIntegerLiftInfeasibility
                | Self::VerifiedHybridPbLpInfeasibility
                | Self::VerifiedHybridIntegerLiftInfeasibility
        )
    }

    pub(super) fn certifies_optimality(self) -> bool {
        matches!(
            self,
            Self::VerifiedBlockAngularOptimality
                | Self::VerifiedAffineAggregationOptimality
                | Self::VerifiedNetworkDesignOptimality
                | Self::VerifiedSingleMachineSchedulingOptimality
        )
    }
}
