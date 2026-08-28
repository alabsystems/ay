// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Native SIMD and bounds-check-elided hot-path boundary; unsafe sites are
// individually justified beside the operation.
#![allow(unsafe_code)]
#![deny(unsafe_op_in_unsafe_fn)]

//! # ay-milp: a MILP/LP engine with a typed in-process API
//!
//! The crate exposes a solver-neutral [`Model`] plus reusable [`LpSession`]
//! and [`BabSession`] surfaces. Its float-first search paths are separated
//! from exact-rational validation so callers receive typed outcomes and can
//! independently check exported evidence.
//!
//! ## API guarantees
//!
//! 1. **Witnesses are checked before publication.** Session-produced primal
//!    points, objective values, and attached certificates are re-checked
//!    against the caller's [`Model`]. A failed check becomes
//!    [`Outcome::Unknown`] with [`UnknownReason::WitnessRejected`]. This does
//!    not make every search claim independently certifiable.
//!    [`Outcome::evidence_shape`] is deliberately non-authoritative;
//!    [`Outcome::check_against`] returns a sealed [`CheckedOutcome`] only after
//!    exact validation against a particular model.
//! 2. **Evidence is data.** [`FarkasCertificate`] / [`OptimalityCertificate`]
//!    are values with independent `verify(&Model)` that re-checks the exact
//!    arithmetic with no solver state.
//! 3. **Rigorous bounds flag.** [`Outcome::Bound`] marks `rigorous` only for
//!    directed-rounding-corrected or exact bounds.
//! 4. **Deadlines and determinism.** [`SolveOpts`] deadlines are honored
//!    inside solve loops; determinism gives run-to-run identical outcomes.
//! 5. **`Model: Send + Sync + Clone`**; sessions are `Send`.
//! 6. **Evidence can LEAVE the process.** [`cert_io`] serialises a verdict's
//!    evidence as `.ayc` — exact rationals, bound to a digest of the model
//!    text AND of the canonical post-read model — with the EVIDENCE KIND
//!    stated per claim (`SUCCINCT` / `REPLAY` / `NONE`). The kind is derived
//!    from the Rust type that is present, never chosen; [`cert_io::check`]
//!    re-parses the model itself and reserves the word "verified".
//! 7. **Session validation is always on.** Every session exit crosses a
//!    fail-closed validation boundary; the general path is `finish` ->
//!    `validate_witnesses`, while typed sibling finalizers enforce the
//!    corresponding checks. Primal points and objective values are re-derived,
//!    attached certificates are verified, and bounds may not contradict their
//!    witnesses. Public or recombined outcomes cross the same kind of boundary
//!    explicitly through [`Outcome::check_against`].
//!
//! ## Solver paths
//!
//! [`LpSession`] and continuous [`BabSession`] models use a
//! Dutertre–de Moura bounded-variable simplex over exact rationals and can
//! produce model-level certificates. Integral models use the native
//! branch-and-bound engine; closing an integrality gap is a search claim unless
//! a whole-tree artifact covers it. With the `smt` feature enabled, an
//! in-process ay-dpll lowering provides an exact QF_LRA fallback for binary
//! columns represented as 0/1 disjunctions.

#[doc(hidden)]
pub mod acensus;
pub mod attrib;
mod bab;
mod block_angular_route;
mod cardinality_branch;
/// Decision census for MECHANISM D (node-rate steering). Inert without `--features dcensus`.
pub mod dcensus;
pub mod debug_flags;
pub mod engine_cli;
#[doc(hidden)]
pub use bab::{
    bump_lu_diff_on_model,
    bump_lu_diff_on_model_lanes,
    diag_bump_lu_diff,
    diag_dump_root_basis,
    diag_exact_probe,
    diag_float_lp,
    // The flagged variant: a caller with parsed engine flags MUST use this one,
    // or the LP-only lane measures the compiled default under the flag's name.
    diag_float_lp_with,
    diag_pin_probe,
    diag_presolve,
    diag_refine_probe,
    // W0 measurement: root dual bound before/after the cut loop, no branching.
    diag_root_closure,
    diag_root_closure_with,
    // P0 instrument: nodes-to-proof, the load-invariant search metric.
    drought_dives_launched,
    nodes_explored,
    reset_drought_dives,
    reset_nodes_explored,
    // The Gurobi-comparable decomposition of the same instrument: `nodes_explored`
    // includes heuristic sub-MIP trees, `Model.NodeCount` does not. ADDITIVE — the
    // frozen counter above keeps every value it ever reported.
    root_nodes_explored,
    submip_nodes_explored,
    BumpLuDiff,
    // STAGE-0 COLD-CLONE READINESS PoC (inert to the serial path; see bab.rs):
    // driven only by tests/parallel_ready.rs.
    NodeBound,
    NodeLpProbe,
};
mod cert;
pub mod cert_io;
// THE COMMON CURRENCY: what a lane may claim, how strong the evidence behind it
// has to be, and the one function (`claim::may_close`) that decides whether a
// lane is allowed to end the solve or must stand behind the anchor.
mod claim;
pub mod compare;
// Reduced-frame -> caller-frame certificate translation, called from the
// `expand_*_outcome` functions in `bab.rs`.
mod cert_lift;
mod certify;
// Exact-arithmetic measurement scaffold (not a shipped API): returns a text
// report only, driven by the `sealed_scale_rational_weak_row` example.
#[doc(hidden)]
pub use certify::sealed_scale::diag_sealed_scale_rational_weak_row;
mod cuts;
mod direct_cnf;
// DUAL FIXING BY LOCK COUNTING. Deliberately NOT part of `presolve`: it is the
// one reduction in the crate that cuts off feasible points (see its header).
mod dualfix;
/// Full-size dual-fix campaign; see [`dualfix::diag_dualfix_campaign_at_scale`].
/// Exposed for `examples/dualfix_campaign.rs` so the campaign is a runnable
/// target rather than an `#[ignore]`d test that never runs.
#[doc(hidden)]
pub use dualfix::diag_dualfix_campaign_at_scale;
/// One-line census of what dual fixing does to a model, without solving it:
/// integer columns free before, after propagation alone (the `DualReductions=0`
/// arm), and after the full fixpoint. Measurement scaffold for `ay-milp diag
/// dualfix`, not a shipped API.
///
/// Runs under the DEFAULT engine profile. Every caller that has parsed engine
/// flags wants [`diag_dualfix_with`] instead — see its note.
#[doc(hidden)]
#[must_use]
pub fn diag_dualfix(model: &Model, secs: f64) -> String {
    diag_dualfix_with(model, secs, &SolveOpts::new())
}

/// [`diag_dualfix`] under a caller's own [`SolveOpts`] — the variant a flagged
/// harness or CLI lane calls.
///
/// WHY IT EXISTS (the same dead-flag family as [`diag_float_lp_with`] and
/// [`diag_root_closure_with`]). `dualfix::dual_fix` opens with the reduction's
/// only kill switch, `tune::on(Knob::NoDualfix)`, which resolves through `tune`'s
/// CALLER layer — the layer a real solve installs at its entry point from
/// `opts.engine().profile()` and this diagnostic never installed. So
/// `ay-milp diag dualfix --no-dualfix` could not have turned the rule off: the
/// flag would have parsed and reached nothing. `ay-milp diag` was refusing the
/// flag outright for exactly that reason, which was the safe half of the repair;
/// this is the other half.
///
/// MEASURED, release binary + `target-cpu=native`, `ay-milp diag dualfix <m> 20`:
///
/// | model | flag | line |
/// |---|---|---|
/// | `p0548` | (none) | `DUALFIX gate=off rows=176 cols=548 int_before=548 int_prop_only=532 int_after=477 fixings=55 to_upper=2 to_lower=53 rounds=3 max_den_bits=1` |
/// | `p0548` | `--no-dualfix` | `DUALFIX gate=off rows=176 cols=548 fixings=0 DECLINED` |
/// | `p0282` | (none) | `… int_after=202 fixings=80 to_upper=0 to_lower=80 rounds=2 …` |
/// | `p0282` | `--no-dualfix` | `DUALFIX gate=off rows=241 cols=282 fixings=0 DECLINED` |
///
/// Pick a model where the rule actually FIRES when re-checking this: on a model
/// that declines for another reason (inexact coefficients, a marked margin row,
/// nothing to fix) both arms print the same `DECLINED` line and the control is
/// vacuous — `benchmarks/milp-ny/safenlp/safenlp_medical_1739_feas.mps` is one
/// such, and it is the first thing this control was tried on.
///
/// The zero-opts wrapper above pins the historical default-profile behaviour.
#[doc(hidden)]
#[must_use]
pub fn diag_dualfix_with(model: &Model, secs: f64, opts: &SolveOpts) -> String {
    let _tuned = tune::activate_caller(opts.engine().profile());
    dualfix::diag_line(model, secs)
}
mod error;
mod exact;
mod hybrid_integer_lift;
mod hybrid_pb_lp;
#[doc(hidden)]
pub use block_angular_route::diag_block_angular;
pub use block_angular_route::{
    verify_optimality_certificate as verify_block_angular_optimality_certificate,
    BlockAngularOptimalityCertificate,
};
pub use hybrid_integer_lift::HybridIntegerLiftInfeasibilityCertificate;
pub use hybrid_pb_lp::HybridPbLpInfeasibilityCertificate;
mod knobs;
pub use knobs::{
    env_audit, Bucket, Deprecation, EnvAudit, Knob, Route, Routed, ZeroIgnored, ALLOW_UNKNOWN_ENV,
    DEPRECATED, KNOBS, ROUTED, ZERO_IGNORED,
};
mod lattice;
mod local_census;
mod lu;
mod margin;
#[doc(hidden)]
pub use margin::{diag_margin_reframe, diag_margin_reframe_with, margin_profile_line};
mod model;
mod mps;
mod network_design_benders;
mod network_design_pb;
mod network_design_route;
pub use network_design_route::{
    verify_infeasibility_certificate as verify_network_design_infeasibility_certificate,
    verify_optimality_certificate as verify_network_design_optimality_certificate,
    NetworkDesignInfeasibilityCertificate, NetworkDesignOptimalityCertificate,
};
mod ns;
mod open_domain;
mod open_domain_route;
mod opts;
mod outcome;
mod parity;
pub use parity::{verify_parity_infeasibility_certificate, ParityInfeasibilityCertificate};
// The first pattern-count tranche is deliberately classifier-only.  Production
// wiring follows only after exact pricing/frontier proof support exists.
#[allow(dead_code)]
mod pattern_count_route;
mod pb_route;
/// Model-bound replay for the PB projection proof artifacts a routed solve
/// publishes on [`BabSession`].
///
/// These verdicts do not travel on `Outcome::Infeasible { cert, tree_cert }` —
/// a PB decision DAG is neither a Farkas combination nor a case-split tree — so
/// a consumer that must re-check a routed INFEASIBLE reads the artifact off the
/// session and replays it here, against its OWN `Model`. Each entry point
/// rebuilds the exact projection from that model rather than trusting the
/// artifact's embedded copy, which is what makes it evidence about one model
/// instead of a self-report.
pub use pb_route::{
    verify_multi_row_infeasibility_certificate as verify_multi_row_bdd_infeasibility_certificate,
    verify_single_row_infeasibility_certificate as verify_single_row_dp_infeasibility_certificate,
};
mod pb_translate;
mod presolve;
#[cfg(test)]
mod presolve_adversarial;
mod probe;
mod sat_relu;
pub use sat_relu::{
    verify_infeasibility_certificate as verify_sat_relu_infeasibility_certificate,
    SatReluInfeasibilityCertificate, SatReluInfeasibilityVerificationError,
};
mod sat_route;
mod scheduling_route;
pub use scheduling_route::{
    verify_optimality_certificate as verify_single_machine_scheduling_optimality_certificate,
    SingleMachineSchedulingOptimalityCertificate,
};
mod opt_cert;
pub mod sepstat;
mod session;
mod simplex;
#[cfg(feature = "smt")]
mod smt;
mod symmetry;
mod tree_cert;
mod tune;
// The SHIPPED `tune::env_layer` arm is the frozen `OnceLock` snapshot, and a
// unit test cannot reach it: under `cfg(test)` that fn compiles to a live read.
// This is the seam `tests/env_layer_snapshot.rs` uses to assert about the arm
// releases actually run. Read-only and knob-name-addressed; it installs nothing.
#[doc(hidden)]
// B38: diag_env_layer/EnvLayerProbe removed with the env snapshot layer.
pub use cert::{
    BoundSide, CertificateError, CertifiedRow, FactRef, FarkasCertificate, Multiplier,
    OptimalityCertificate,
};
pub use error::{MilpError, ModelError};
pub use model::{Col, ColKind, Model, PointViolation, Row, Sense};
pub use mps::{read_mps, MpsError, MpsProblem};
pub use opt_cert::{
    derive_optimality_tree, derive_optimality_tree_reported, verify_optimality_tree_bound,
    MilpOptimalityCertificate, OptTreeBranch, OptTreeDecline, OptTreeNode, OptTreeReport,
    OptimalityTreeBudget, OPT_TREE_FLOAT_ITERS_PER_UNIT, OPT_TREE_RIM_BUILD_COST,
    OPT_TREE_RIM_ITER_COST,
};
pub use opts::{
    EngineConfigError, EngineEconomics, FixedAssignmentTreeWarmStart, FlipSolveMode, SolveOpts,
    TallColdDualMode,
};
pub use outcome::{CheckedOutcome, EvidenceShape, Outcome, OutcomeCheckError, UnknownReason};
pub use presolve::{
    AffineAggregationCertificate, AffineAggregationCertificateError, AffineAggregationClaim,
    AffineAggregationInnerProof, AffineAggregationVerification, AffineRecovery,
};
/// The SHIPPED continuous float lane, measured directly — the honest
/// counterpart of the [`diag_float_lp`] scaffold, which is one cold walk with
/// no ladder and whose status and objective are not solver behaviour.
#[doc(hidden)]
pub use session::diag_shipped_float_lp;
pub use session::{
    AdaptiveFiveLeafCombTargetFsbReport, AdaptiveFourLeafCombTargetFsbReport,
    AdaptiveThreeLeafTargetFsbReport, BabSession, CertifiedAdaptiveFiveLeafComb,
    CertifiedAdaptiveFourLeafComb, CertifiedAdaptiveThreeLeafHarvest,
    CertifiedAdaptiveThreeLeafTree, CertifiedBinaryAssignmentTree, CertifiedBinaryTreeHarvest,
    CertifiedSplitHarvest, LpSession, ObbtOpts, ObbtReport, TargetFsbOpts, TargetFsbPrefixOpts,
    TargetFsbReport, MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES, MAX_TARGET_FSB_CANDIDATES,
    MAX_TARGET_FSB_PREFIX_CANDIDATES,
};
pub use simplex::{
    enable_iter_ledger, iter_ledger_line, px_profile_line, rt_profile_line, sb_profile_line,
    upd_profile_line,
};
pub use tree_cert::{MilpInfeasibilityCertificate, TreeNode};
