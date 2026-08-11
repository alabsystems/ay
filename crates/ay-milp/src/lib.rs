// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! # ay-milp: a MILP/LP engine with a typed in-process API
//!
//! The crate exposes a solver-neutral [`Model`] plus reusable [`LpSession`]
//! and [`BabSession`] surfaces. Its float-first search paths are separated
//! from exact-rational validation so callers receive typed outcomes and can
//! independently check exported evidence.
//!
//! ## API guarantees
//!
//! 1. **No silent wrong values.** Anything unwarranted is
//!    [`Outcome::Unknown`] with a [`UnknownReason`] — wrong-optimum classes
//!    are unrepresentable.
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
//! 7. **Self-validation is always on.** Every verdict leaves a session through
//!    `finish` -> `validate_witnesses`, INDEPENDENT of
//!    [`SolveOpts::require_certificates`]: `check_point`, exact value
//!    re-derivation, `cert.verify`, a bound-crossing test, and (on a
//!    continuous model) a dual bound that must MEET the primal. A verdict
//!    whose own witness does not hold up is withheld as
//!    [`UnknownReason::WitnessRejected`], never returned.
//!
//! ## Solver paths
//!
//! [`LpSession`] and continuous [`BabSession`] models use a
//! Dutertre–de Moura bounded-variable simplex over exact rationals. Their
//! verdicts are exact and can carry model-level certificates. Integral models
//! use the native branch-and-bound engine; with the `smt` feature enabled, an
//! in-process ay-dpll lowering provides an exact QF_LRA fallback for binary
//! columns represented as 0/1 disjunctions.

mod bab;
mod block_angular_route;
mod cardinality_branch;
#[doc(hidden)]
pub use bab::{
    bump_lu_diff_on_model,
    bump_lu_diff_on_model_lanes,
    diag_bump_lu_diff,
    diag_dump_root_basis,
    diag_exact_probe,
    diag_float_lp,
    diag_pin_probe,
    diag_presolve,
    diag_refine_probe,
    // W0 measurement: root dual bound before/after the cut loop, no branching.
    diag_root_closure,
    // P0 instrument: nodes-to-proof, the load-invariant search metric.
    nodes_explored,
    reset_nodes_explored,
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
#[doc(hidden)]
#[must_use]
pub fn diag_dualfix(model: &Model, secs: f64) -> String {
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
mod lu;
mod margin;
#[doc(hidden)]
pub use margin::diag_margin_reframe;
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
pub use tune::{diag_env_layer, EnvLayerProbe};

pub use cert::{
    BoundSide, CertificateError, CertifiedRow, FactRef, FarkasCertificate, Multiplier,
    OptimalityCertificate,
};
pub use error::{MilpError, ModelError};
pub use model::{Col, ColKind, Model, PointViolation, Row, Sense};
pub use mps::{read_mps, MpsError, MpsProblem};
pub use opts::{EngineConfigError, EngineEconomics, FixedAssignmentTreeWarmStart, SolveOpts};
pub use outcome::{Outcome, Trust, UnknownReason};
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
    iter_ledger_line, px_profile_line, rt_profile_line, sb_profile_line, upd_profile_line,
};
pub use tree_cert::{MilpInfeasibilityCertificate, TreeNode};
