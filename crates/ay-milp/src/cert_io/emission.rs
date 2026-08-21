// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Everything the emitter needs beyond the [`Outcome`] itself.
pub struct EmitCtx<'a> {
    /// The POST-read model the certificate's indices refer to.
    pub model: &'a Model,
    /// The exact text handed to [`crate::read_mps`] (post-decompression).
    pub model_text: &'a str,
    /// Column names, for the witness block. Empty is allowed (`-` is written).
    pub col_names: &'a [String],
    /// The reader's integralising objective scale.
    pub obj_scale: &'a BigRational,
    /// Free-form provenance appended to the `solver` line.
    pub provenance: &'a str,
    /// Replay claims recorded by the solve, if any.
    pub replay_claims: &'a [ReplayClaim],
    /// Exact source-to-reduced affine replay, with proof kept in its own frame.
    pub affine_aggregation_certificate: Option<&'a AffineAggregationCertificate>,
    /// Source-row GF(2) contradiction produced by the parity route.
    pub parity_infeasibility_certificate: Option<&'a ParityInfeasibilityCertificate>,
    /// Model-bound RUP refutation of an exact SAT/ReLU projection.
    pub sat_relu_infeasibility_certificate: Option<&'a SatReluInfeasibilityCertificate>,
    /// Model-bound exact refutation of a rebuilt Hoffman projection.
    pub network_design_infeasibility_certificate: Option<&'a NetworkDesignInfeasibilityCertificate>,
    /// Model-bound exact refutation of the strict-better Hoffman-master face.
    pub network_design_optimality_certificate: Option<&'a NetworkDesignOptimalityCertificate>,
    /// Model-bound exact Lagrangian proof for an integral block-angular model.
    pub block_angular_optimality_certificate: Option<&'a BlockAngularOptimalityCertificate>,
    /// Model-bound exact optimum of a recognized single-machine scheduling model.
    pub single_machine_scheduling_optimality_certificate:
        Option<&'a SingleMachineSchedulingOptimalityCertificate>,
    /// Independently replayable exact single-row PB infeasibility proof, when
    /// the corresponding route owned this outcome.
    pub single_row_dp_infeasibility_certificate: Option<&'a SingleRowDpInfeasibilityCertificate>,
    /// Independently replayable exact general PB infeasibility decision DAG,
    /// when the corresponding route owned this outcome.
    pub multi_row_bdd_infeasibility_certificate: Option<&'a MultiRowBddInfeasibilityCertificate>,
    /// Single-row PB proof over an exact, deterministically rebuilt
    /// open-domain residual.
    pub open_domain_single_row_dp_infeasibility_certificate:
        Option<&'a SingleRowDpInfeasibilityCertificate>,
    /// General PB proof over an exact, deterministically rebuilt open-domain
    /// residual.
    pub open_domain_multi_row_bdd_infeasibility_certificate:
        Option<&'a MultiRowBddInfeasibilityCertificate>,
    /// Hybrid proof over an exact, deterministically rebuilt open-domain residual.
    pub open_domain_hybrid_pb_lp_infeasibility_certificate:
        Option<&'a HybridPbLpInfeasibilityCertificate>,
    /// Integer-lifted hybrid proof over a rebuilt open-domain residual.
    pub open_domain_hybrid_integer_lift_infeasibility_certificate:
        Option<&'a HybridIntegerLiftInfeasibilityCertificate>,
    /// Exact hybrid PB/LP cut ledger plus final PB refutation.
    pub hybrid_pb_lp_infeasibility_certificate: Option<&'a HybridPbLpInfeasibilityCertificate>,
    /// Exact general-integer radix-lift wrapper around a hybrid refutation.
    pub hybrid_integer_lift_infeasibility_certificate:
        Option<&'a HybridIntegerLiftInfeasibilityCertificate>,
    /// Cap on the emitted certificate size in bytes. A block that would
    /// overflow it is DROPPED with an explicit `truncated` record and its claim
    /// is DOWNGRADED to `NONE` — never silently shortened.
    pub max_bytes: Option<usize>,
}

/// One claim as the emitter decided it. Constructed only by this module, and
/// only from the presence of a Rust value — the kind is never a caller's word.
pub(super) struct EmittedClaim {
    pub(super) name: &'static str,
    pub(super) kind: EvidenceKind,
    pub(super) source: Option<String>,
}
