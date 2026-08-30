// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CertIoError {
    /// A record was malformed.
    #[error("line {line}: {msg}")]
    Malformed {
        /// 1-based line number.
        line: usize,
        /// What went wrong.
        msg: String,
    },
    /// A record labelled a claim with an evidence kind its backing object
    /// cannot support — e.g. `SUCCINCT` naming a replay block. THIS IS A
    /// PARSE ERROR, not a verification failure: the format must make
    /// mislabelling ungrammatical.
    #[error("line {line}: evidence kind {kind} cannot be backed by `{source_token}`")]
    MislabelledEvidence {
        /// 1-based line number.
        line: usize,
        /// The kind token that was written.
        kind: String,
        /// The source token that was named.
        source_token: String,
    },
    /// A rational field exceeded the exact-arithmetic ceiling of the proof
    /// format that owns it.  This is separate from malformed syntax so callers
    /// can distinguish a bounded fail-closed rejection from a grammar error.
    #[error("line {line}: {field} exceeds the {max_bits}-bit rational limit")]
    RationalBitLimit {
        /// 1-based line number.
        line: usize,
        /// Name of the bounded proof field.
        field: String,
        /// Maximum numerator or denominator magnitude, in bits.
        max_bits: usize,
    },
}

/// The model-identity header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Header {
    /// SHA-256 of the model text.
    pub file_digest: String,
    /// Length of the model text in bytes.
    pub file_bytes: usize,
    /// SHA-256 of the v1 canonical model.
    pub canon_digest: String,
    /// Row count as claimed.
    pub rows: usize,
    /// Column count as claimed.
    pub cols: usize,
    /// Integral-column count as claimed.
    pub intcols: usize,
    /// Objective direction as claimed.
    pub sense: Sense,
    /// The reader's integralising objective scale as claimed.
    pub obj_scale: BigRational,
    /// The `solver` line, verbatim.
    pub solver: String,
}

/// A parsed claim record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedClaim {
    /// Claim name (`primal`, `dual`, `infeasible`, `unbounded`).
    pub name: String,
    /// Evidence kind.
    pub kind: EvidenceKind,
    /// Backing source token, when the record named one.
    pub source: Option<String>,
}

/// A parsed `rootdual` block: a bound on the model's optimum, together with
/// the residual the emitter says it leaves unproved.
///
/// Both fields are ASSERTIONS. The certificate is re-verified against the
/// model and `gap` is RE-DERIVED from `certificate.bound` and the verdict
/// line; a record whose two numbers disagree is refused rather than believed,
/// which is what stops an emitter understating how much of its own optimum is
/// unproved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootDualBoundRecord {
    /// The bound object: positive multipliers whose oriented combination is
    /// the model's own objective, priced at the model's own bounds.
    pub certificate: OptimalityCertificate,
    /// The residual to the claimed optimum, in the model's frame, as the
    /// emitter recorded it.
    pub gap: BigRational,
}

/// A parsed `.ayc` file. NOTHING here is trusted: it is a set of assertions
/// for [`check`] to re-derive.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Certificate {
    /// The header assertions.
    pub header: Header,
    /// The verdict word (`optimal`, `feasible`, `infeasible`, ...).
    pub verdict: String,
    /// The claimed objective value, in the frame named on the verdict line.
    pub value: Option<BigRational>,
    /// The frame of `value`.
    pub value_frame: String,
    /// Per-claim evidence records.
    pub claims: Vec<ParsedClaim>,
    /// The witness point, when a witness block was present.
    pub witness: Option<Vec<BigRational>>,
    /// The root Farkas certificate, when present.
    pub farkas: Option<FarkasCertificate>,
    /// The optimality certificate, when present.
    pub optcert: Option<OptimalityCertificate>,
    /// The ROOT DUAL BOUND, when present. A SEPARATE field from `optcert` on
    /// purpose: an `optcert` under the `dual` claim asserts that its bound IS
    /// the optimum, while this one asserts only that the optimum is no better
    /// than its bound. Reading one as the other would turn a partial
    /// certificate into a complete-looking one, which is the single failure
    /// this whole lane exists to prevent.
    pub root_dual_bound: Option<RootDualBoundRecord>,
    /// Whether the optimality certificate was marked trivial by the emitter
    /// (re-derived by [`check`], never trusted).
    pub optcert_trivial: bool,
    /// The whole-tree infeasibility certificate, when present.
    pub tree: Option<MilpInfeasibilityCertificate>,
    /// The whole-tree OPTIMALITY split tree, when present. A SEPARATE field
    /// from `tree` on purpose: the two carry opposite claims, and a bound tree
    /// read as a proof of emptiness would be fatal rather than merely vacuous.
    pub opt_tree: Option<OptTreeNode>,
    /// Exact source-to-reduced affine replay, including reduced-frame proof.
    pub affine_aggregation: Option<AffineAggregationCertificate>,
    /// Exact GF(2) source-row contradiction, when present.
    pub parity_infeasibility: Option<ParityInfeasibilityCertificate>,
    /// Exact SAT/ReLU projection plus RUP refutation, when present.
    pub sat_relu_infeasibility: Option<SatReluInfeasibilityCertificate>,
    /// Exact PB refutation over a deterministically rebuilt Hoffman master.
    pub network_design_infeasibility: Option<NetworkDesignInfeasibilityCertificate>,
    /// Exact strict-better-face refutation over a rebuilt Hoffman master.
    pub network_design_optimality: Option<NetworkDesignOptimalityCertificate>,
    /// Exact Lagrangian proof over a rebuilt block-angular decomposition.
    pub block_angular_optimality: Option<BlockAngularOptimalityCertificate>,
    /// Exact sequence plus bounded DP replay for single-machine scheduling.
    pub single_machine_scheduling_optimality: Option<SingleMachineSchedulingOptimalityCertificate>,
    /// Exact single-row PB reachability proof, when present.
    pub single_row_dp: Option<SingleRowDpInfeasibilityCertificate>,
    /// Exact general PB residual-state decision DAG, when present.
    pub multi_row_bdd: Option<MultiRowBddInfeasibilityCertificate>,
    /// Exact single-row proof over a rebuilt open-domain residual.
    pub open_domain_dp: Option<SingleRowDpInfeasibilityCertificate>,
    /// Exact general PB proof over a rebuilt open-domain residual.
    pub open_domain_bdd: Option<MultiRowBddInfeasibilityCertificate>,
    /// Hybrid proof over a rebuilt open-domain residual.
    pub open_domain_hybrid_pb_lp: Option<HybridPbLpInfeasibilityCertificate>,
    /// Integer-lifted hybrid proof over a rebuilt open-domain residual.
    pub open_domain_hybrid_integer_lift: Option<HybridIntegerLiftInfeasibilityCertificate>,
    /// Exact binary-master/continuous-recourse cut-ledger refutation.
    pub hybrid_pb_lp: Option<HybridPbLpInfeasibilityCertificate>,
    /// Exact bounded general-integer lift around a hybrid refutation.
    pub hybrid_integer_lift: Option<HybridIntegerLiftInfeasibilityCertificate>,
    /// Replay claims, keyed by claim id.
    pub replay: Vec<ReplayClaim>,
    /// Records the emitter marked explicitly unchecked.
    pub unchecked: Vec<String>,
    /// Records the emitter marked truncated.
    pub truncated: Vec<String>,
    /// The `reason` line for an `unknown` verdict.
    pub reason: Option<String>,
    /// Whether the trailing `%END` digest matched the body.
    pub end_digest_ok: bool,
}

/// The source tokens that may back a `SUCCINCT` claim. Anything else on a
/// `SUCCINCT` record is a parse error.
pub(super) const SUCCINCT_SOURCES: &[&str] = &[
    "witness",
    "farkas",
    "optcert",
    "root-dual-bound",
    "tree",
    "optimality-tree",
    "sat-relu-rup",
    "affine-aggregation",
    "parity-gf2",
    "network-design-infeasibility",
    "network-design-optimality",
    "block-angular-optimality",
    "single-machine-scheduling-optimality",
    "single-row-dp",
    "multi-row-bdd",
    "open-domain-dp",
    "open-domain-bdd",
    "open-domain-hybrid-pb-lp",
    "open-domain-hybrid-integer-lift",
    "hybrid-pb-lp",
    "hybrid-integer-lift",
];
/// Source tokens a `NONE` record may carry, explaining WHY it is none.
/// `trivial-optcert` remains readable for artifacts from the legacy emitter;
/// new empty-multiplier zero-objective bounds are `SUCCINCT optcert`.
pub(super) const NONE_SOURCES: &[&str] = &["trivial-optcert", "truncated"];
