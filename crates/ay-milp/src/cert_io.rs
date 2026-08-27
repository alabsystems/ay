// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `.ayc` — the AY Certificate format: the exit certificates never had.
//!
//! [`FarkasCertificate`] / [`OptimalityCertificate`] /
//! [`MilpInfeasibilityCertificate`] already hold evidence AS DATA with
//! an independent `verify(&Model)`. What was missing was a way for that data to
//! LEAVE THE PROCESS. Typed evidence was verified in-process and then dropped,
//! so no consumer could re-check an evidenced claim without re-running the
//! solver — the exact thing a certificate exists to avoid.
//!
//! # The honesty requirement
//!
//! Not everything this solver proves is succinctly certifiable, and this format
//! is built so that pretending otherwise is UNGRAMMATICAL. Every CLAIM (not
//! every verdict — an `Optimal` is TWO claims) carries exactly one evidence
//! kind:
//!
//! * `SUCCINCT` — an exported object whose verification is a bounded exact
//!   rational recomputation against the model alone, independent of the search.
//! * `REPLAY` — no exported object exists; re-verification means re-running the
//!   solver. The lattice device's "the objective-0 face is EMPTY" is an
//!   exhaustive enumeration over up to 4e9 nodes with no short witness.
//! * `NONE` — trust only. `Optimal` on an integral model with a nonzero
//!   objective has NO dual-side object in this build, and says so.
//!
//! The kind is NEVER chosen by the emitter. It is derived from the Rust type
//! that is present: `Some(FarkasCertificate)` or a typed
//! `SingleRowDpInfeasibilityCertificate` is `SUCCINCT` by construction, only a
//! [`ReplayClaim`] can produce `REPLAY`, and a bare `Outcome::Infeasible {
//! cert: None, tree_cert: None }` without a typed side artifact has no path to
//! anything but `NONE`. The PARSER enforces the same invariant on input: a
//! record labelling a replay block `SUCCINCT` is rejected as malformed, not
//! merely failed at verification time.
//!
//! # Why text, not serde
//!
//! `serde` is available in this workspace (and `num-bigint` even carries its
//! `serde` feature), so this is a choice, not a constraint. `num-bigint`'s
//! serde representation is a sign plus a `u32` limb vector: lossless, but
//! version-coupled and unreadable. A certificate must outlive `num-bigint`
//! 0.4. Rationals are written as canonical `numer/denom` decimal, reduced,
//! `denom >= 1`, `denom == 1` elided. Any language with a bignum can read it,
//! it diffs, and it greps.
//!
//! # Two digests, and the second is the subtle one
//!
//! * `model file` binds the model TEXT this certificate was produced from
//!   (post-decompression, i.e. exactly the bytes handed to [`crate::read_mps`]).
//!   It is the durable anchor and cannot drift.
//! * `model canon v1` binds the MODEL the certificate's indices actually refer
//!   to. This is necessary because [`crate::read_mps`] is not the identity: it
//!   multiplies the objective by `obj_scale` and may store rounded `f64`
//!   coefficients alongside an exact side-store. A `FactRef::RowBound { row }`
//!   indexes the POST-read model, so the canonical digest is taken over the
//!   exact side-store values, never the `f64` proxies.
//!
//! Because the two frames differ, every value record names its frame: `file`
//! (the units the input file is written in) or `model` (post-`obj_scale`).

use std::collections::BTreeSet;
use std::fmt::{self, Write as _};
use std::sync::Arc;
use std::time::Instant;

use ay_pb_core::{
    decode_multi_row_bdd_infeasibility_certificate_json,
    decode_single_row_dp_infeasibility_certificate_json,
    encode_multi_row_bdd_infeasibility_certificate_json,
    encode_single_row_dp_infeasibility_certificate_json, MultiRowBddInfeasibilityCertificate,
    SingleRowDpInfeasibilityCertificate,
};
use ay_sat::{Literal, RupStep, Variable};
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use sha2::{Digest, Sha256};

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate};
use crate::hybrid_integer_lift::{
    decode_hybrid_integer_lift_infeasibility_certificate_json,
    encode_hybrid_integer_lift_infeasibility_certificate_json,
    verify_hybrid_integer_lift_infeasibility_certificate,
};
use crate::hybrid_pb_lp::{
    decode_hybrid_pb_lp_infeasibility_certificate_json,
    encode_hybrid_pb_lp_infeasibility_certificate_json,
    verify_hybrid_pb_lp_infeasibility_certificate,
};
use crate::model::{exact, Col, ColKind, Model, Row, Sense};
use crate::opt_cert::{verify_optimality_tree_bound, MilpOptimalityCertificate, OptTreeNode};
use crate::outcome::{Outcome, UnknownReason};
use crate::presolve::implied_free::{
    validate_certificate_payload_caps, AffineAggregationAnalysis, AffineAggregationCaps,
    AnalysisBound, MAX_AFFINE_PROOF_MULTIPLIERS, MAX_AFFINE_TREE_DEPTH, MAX_AFFINE_TREE_NODES,
    MAX_ANALYSIS_COLS, MAX_ANALYSIS_ROWS, MAX_ELIMINATIONS, MAX_RATIONAL_BITS, MAX_RECOVERY_TERMS,
    MAX_ROW_TERMS,
};
use crate::tree_cert::{MilpInfeasibilityCertificate, TreeNode};
use crate::{
    AffineAggregationCertificate, AffineAggregationCertificateError, AffineAggregationClaim,
    AffineAggregationInnerProof, AffineAggregationVerification, AffineRecovery,
    BlockAngularOptimalityCertificate, HybridIntegerLiftInfeasibilityCertificate,
    HybridPbLpInfeasibilityCertificate, NetworkDesignInfeasibilityCertificate,
    NetworkDesignOptimalityCertificate, ParityInfeasibilityCertificate,
    SatReluInfeasibilityCertificate, SingleMachineSchedulingOptimalityCertificate,
};

/// The format version this build emits and the only one it reads.
pub const AYC_VERSION: u32 = 1;
const MAX_AYC_INPUT_BYTES: usize = 512 * 1024 * 1024;
const MAX_AYC_INPUT_LINES: usize = 8_000_000;

/// How a claim is backed.
///
/// Ordering matters only for reporting; the values are never parsed from
/// caller-controlled data without the block-presence checks in [`parse`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvidenceKind {
    /// An exported object with a bounded exact re-check against the model.
    Succinct,
    /// No exported object: re-verification is re-running the solver.
    Replay,
    /// Trust only.
    None,
}

impl EvidenceKind {
    /// The wire token.
    #[must_use]
    pub fn token(self) -> &'static str {
        match self {
            Self::Succinct => "SUCCINCT",
            Self::Replay => "REPLAY",
            Self::None => "NONE",
        }
    }

    fn from_token(t: &str) -> Option<Self> {
        match t {
            "SUCCINCT" => Some(Self::Succinct),
            "REPLAY" => Some(Self::Replay),
            "NONE" => Some(Self::None),
            _ => None,
        }
    }
}

/// A claim whose only re-verification is re-running the solver.
///
/// Every field exists to keep the escape hatch honest. `tcb` names the code
/// that must be trusted; `nondeterminism` states out loud that a re-run may not
/// reproduce the object (the lattice device's BKZ budget is a fraction of
/// REMAINING WALL CLOCK, so a different machine or `--time-limit` yields a
/// different reduced basis and a different sweep).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayClaim {
    /// Claim identifier, e.g. `objective-face-empty`.
    pub claim: String,
    /// Which device produced it, e.g. `lattice-cvp`.
    pub device: String,
    /// The method, e.g. `ahl-hnf-lll+bkz+schnorr-euchner`.
    pub method: String,
    /// The arithmetic the pruning rests on.
    pub arithmetic: String,
    /// Nodes visited by the exhaustive sweep, when counted (`None` = not
    /// instrumented).
    pub nodes_visited: Option<u64>,
    /// The node budget the sweep would have declined at.
    pub node_budget: u64,
    /// `exhausted` or `capped`.
    pub outcome: String,
    /// Sources of run-to-run divergence, one token each.
    pub nondeterminism: Vec<String>,
    /// A command line that re-attempts the claim.
    pub reproduce: String,
    /// The trusted computing base: the file that must be trusted.
    pub tcb: String,
}

/// THE REPLAY LEDGER: how a device that proved something UNCERTIFIABLY tells
/// the emitter so.
///
/// A device deep in the search cannot return a certificate it does not have,
/// and it must not be able to launder its result into one. So it files a
/// [`ReplayClaim`] here instead. The ledger is a THREAD-LOCAL, drained by
/// [`crate::BabSession::check`] into the session that produced it — not a
/// process-global, because a process-global would let one solve's trust
/// annotation attach to another solve's verdict.
///
/// The invariant this preserves: there is no code path from a device's
/// "I exhausted a search" to `EvidenceKind::Succinct`. Filing here is the ONLY
/// way to be reported at all, and filing here can only ever produce `REPLAY`.
pub(crate) mod ledger {
    use std::cell::RefCell;

    use super::ReplayClaim;

    thread_local! {
        static PENDING: RefCell<Vec<ReplayClaim>> = const { RefCell::new(Vec::new()) };
    }

    /// File a replay claim against the solve running on this thread.
    pub(crate) fn record(claim: ReplayClaim) {
        PENDING.with(|p| p.borrow_mut().push(claim));
    }

    /// Drain the ledger. Called once, by the session, at the end of a solve.
    pub(crate) fn take() -> Vec<ReplayClaim> {
        PENDING.with(|p| std::mem::take(&mut *p.borrow_mut()))
    }
}

mod check_claims;
mod check_dual;
mod check_infeasible;
mod check_policy;
mod check_primal;
mod checking;
mod checking_main;
mod digest;
mod emission;
mod emission_affine;
mod emission_basic;
mod emission_main;
mod emission_routes;
mod emit_infeasible;
mod emit_optimal;
mod parse_affine;
mod parse_affine_inner;
mod parse_basic;
mod parse_blocks;
mod parse_opt_tree;
mod parse_proofs;
mod parse_replay;
mod parse_routes;
mod parse_sat_relu;
mod parse_state;
mod parse_tree;
mod parsing;
mod parsing_main;
mod wire;

use check_claims::*;
use check_dual::*;
use check_infeasible::*;
use check_policy::*;
use check_primal::*;
use checking_main::*;
use digest::*;
use emission::*;
use emission_affine::*;
use emission_basic::*;
use emission_main::*;
use emission_routes::*;
use emit_infeasible::*;
use emit_optimal::*;
use parse_affine::*;
use parse_affine_inner::*;
use parse_basic::*;
use parse_blocks::*;
use parse_opt_tree::*;
use parse_proofs::*;
use parse_replay::*;
use parse_routes::*;
use parse_sat_relu::*;
use parse_state::*;
use parse_tree::*;
use parsing::*;
use wire::*;

pub use checking::{CheckReport, CheckStatus, ClaimReport, ClaimStanding};
pub use checking_main::check;
pub(crate) use digest::canonical_digest_bytes_bounded;
pub use digest::{canonical_digest, canonical_model_v1, sha256_hex};
pub use emission::EmitCtx;
pub use emission_main::emit;
pub use parsing::{CertIoError, Certificate, Header, ParsedClaim};
pub use parsing_main::parse;

#[cfg(test)]
mod tests;
