// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently checked evidence carried beside a solver outcome.

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
