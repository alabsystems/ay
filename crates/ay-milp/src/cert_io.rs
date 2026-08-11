// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `.ayc` — the AY Certificate format: the exit certificates never had.
//!
//! [`FarkasCertificate`] / [`OptimalityCertificate`] /
//! [`MilpInfeasibilityCertificate`] already hold evidence AS DATA with
//! an independent `verify(&Model)`. What was missing was a way for that data to
//! LEAVE THE PROCESS. Everything the engine proved was verified in-process and
//! then dropped, so no consumer could re-check a verdict without re-running the
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
use crate::outcome::{Outcome, UnknownReason};
use crate::tree_cert::{MilpInfeasibilityCertificate, TreeNode};
use crate::{
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

// ---------------------------------------------------------------------------
// Exact rationals on the wire
// ---------------------------------------------------------------------------

/// Canonical decimal `numer/denom`, reduced, `denom >= 1`, `denom == 1` elided.
fn fmt_rat(r: &BigRational) -> String {
    if r.denom().is_one() {
        r.numer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// Parse a wire rational. Rejects a zero/negative denominator and a
/// non-reduced fraction: the wire form is CANONICAL, so `2/4` is malformed
/// rather than silently normalised. That keeps the `%END` digest a function of
/// the value.
fn parse_rat(s: &str) -> Option<BigRational> {
    let s = s.trim();
    match s.split_once('/') {
        Some((n, d)) => {
            let n: BigInt = n.parse().ok()?;
            let d: BigInt = d.parse().ok()?;
            if !d.is_positive() || d.is_one() {
                return None;
            }
            if n.gcd(&d) != BigInt::one() {
                return None;
            }
            Some(BigRational::new_raw(n, d))
        }
        None => Some(BigRational::from_integer(s.parse().ok()?)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundedRatParseError {
    Malformed,
    BitLimit,
}

/// Maximum decimal digits needed to spell any integer whose magnitude uses at
/// most `bit_cap` bits.  `30103 / 100000` is a strict upper bound on
/// `log10(2)`, so this preflight never rejects an integer that satisfies the
/// binary cap.  The exact `BigInt::bits` check below rejects the few values
/// admitted by the rational approximation but lying just above the cap.
fn max_decimal_digits_for_bits(bit_cap: usize) -> Option<usize> {
    const LOG10_2_UPPER_NUMERATOR: usize = 30_103;
    const LOG10_2_UPPER_DENOMINATOR: usize = 100_000;

    if bit_cap == 0 {
        return Some(1);
    }
    bit_cap
        .checked_mul(LOG10_2_UPPER_NUMERATOR)?
        .checked_add(LOG10_2_UPPER_DENOMINATOR - 1)
        .map(|scaled| scaled / LOG10_2_UPPER_DENOMINATOR)
}

/// Parse one integer without ever constructing a value materially larger than
/// `bit_cap`.  Length is checked before digit validation and `BigInt` parsing,
/// so an adversarial megabyte-scale token remains a borrowed string plus a
/// typed rejection rather than a megabyte-scale bignum.
fn parse_bigint_bounded(s: &str, bit_cap: usize) -> Result<BigInt, BoundedRatParseError> {
    let digits = s
        .strip_prefix('-')
        .or_else(|| s.strip_prefix('+'))
        .unwrap_or(s);
    let digit_cap = max_decimal_digits_for_bits(bit_cap).ok_or(BoundedRatParseError::BitLimit)?;
    if digits.is_empty() || digits.len() > digit_cap {
        return Err(if digits.is_empty() {
            BoundedRatParseError::Malformed
        } else {
            BoundedRatParseError::BitLimit
        });
    }
    if !digits.bytes().all(|digit| digit.is_ascii_digit()) {
        return Err(BoundedRatParseError::Malformed);
    }
    let value = s
        .parse::<BigInt>()
        .map_err(|_| BoundedRatParseError::Malformed)?;
    if value.bits() > bit_cap as u64 {
        return Err(BoundedRatParseError::BitLimit);
    }
    Ok(value)
}

/// Bounded counterpart of [`parse_rat`] for proof formats whose verifier has
/// an explicit exact-value ceiling.  Both operands are bounded before the gcd,
/// and the canonical wire rules remain identical to the unbounded parser.
fn parse_rat_bounded(s: &str, bit_cap: usize) -> Result<BigRational, BoundedRatParseError> {
    let s = s.trim();
    match s.split_once('/') {
        Some((n, d)) => {
            let n = parse_bigint_bounded(n, bit_cap)?;
            let d = parse_bigint_bounded(d, bit_cap)?;
            if !d.is_positive() || d.is_one() || n.gcd(&d) != BigInt::one() {
                return Err(BoundedRatParseError::Malformed);
            }
            Ok(BigRational::new_raw(n, d))
        }
        None => Ok(BigRational::from_integer(parse_bigint_bounded(s, bit_cap)?)),
    }
}

fn sense_token(s: Sense) -> &'static str {
    match s {
        Sense::Minimize => "min",
        Sense::Maximize => "max",
    }
}

fn parse_sense(t: &str) -> Option<Sense> {
    match t {
        "min" => Some(Sense::Minimize),
        "max" => Some(Sense::Maximize),
        _ => None,
    }
}

fn side_token(s: BoundSide) -> &'static str {
    match s {
        BoundSide::Lower => "lower",
        BoundSide::Upper => "upper",
    }
}

fn parse_side(t: &str) -> Option<BoundSide> {
    match t {
        "lower" => Some(BoundSide::Lower),
        "upper" => Some(BoundSide::Upper),
        _ => None,
    }
}

/// An optional exact bound on the wire: `-inf` / `+inf` for an absent side.
fn fmt_bound(v: Option<&BigRational>, upper: bool) -> String {
    v.map_or_else(
        || if upper { "+inf".into() } else { "-inf".into() },
        fmt_rat,
    )
}

// ---------------------------------------------------------------------------
// Digests
// ---------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// SHA-256 of arbitrary bytes, lowercase hex.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

/// The canonicalisation rule, version 1.
///
/// EVERY value is taken from the exact side-store when one exists — never from
/// the `f64` proxy — because that store is what the certificate verifier reads.
/// A digest over the proxies would bind a model the proof is not about.
///
/// This rule is FROZEN. A future change gets `v2` alongside; `v1` never moves,
/// or every certificate ever written stops matching.
fn write_canonical_model_v1(writer: &mut impl fmt::Write, model: &Model) -> fmt::Result {
    writeln!(writer, "ayc-canon-v1")?;
    writeln!(writer, "sense {}", sense_token(model.sense()))?;
    writeln!(writer, "objective {}", u8::from(model.has_objective()))?;
    writeln!(writer, "offset {}", fmt_rat(&model.obj_offset_exact()))?;
    writeln!(writer, "cols {}", model.num_cols())?;
    for j in 0..model.num_cols() {
        let c = Col(j as u32);
        let (lb, ub) = model.col_bounds(c);
        let kind = match model.col_kind(c) {
            ColKind::Binary => "b",
            ColKind::Integer => "i",
            ColKind::Continuous => "c",
        };
        let objf = model.obj_coeff(c);
        // Frozen canonical-v1 rule: the importer records objective overrides
        // only for nonzero advice coefficients, so stored zero encodes exact
        // zero on every admitted wire model. Preserve that historical byte
        // encoding; arbitrary transformed models would require canonical v2.
        let obj = if objf == 0.0 {
            BigRational::zero()
        } else {
            model.obj_coeff_exact_at(j as u32, objf)
        };
        writeln!(
            writer,
            "col {j} {kind} {} {} {}",
            fmt_bound(exact(lb).as_ref(), false),
            fmt_bound(exact(ub).as_ref(), true),
            fmt_rat(&obj)
        )?;
    }
    writeln!(writer, "rows {}", model.num_rows())?;
    for i in 0..model.num_rows() {
        let (coeffs, lb, ub) = model.row(Row(i as u32));
        write!(
            writer,
            "row {i} {} {} {}",
            fmt_bound(model.row_lb_exact(i, lb).as_ref(), false),
            fmt_bound(model.row_ub_exact(i, ub).as_ref(), true),
            coeffs.len()
        )?;
        // `Model::row` guarantees sorted, duplicate-free, zero-free.
        for &(c, a) in coeffs {
            write!(writer, " {c} {}", fmt_rat(&model.row_coeff_exact(i, c, a)))?;
        }
        writer.write_char('\n')?;
    }
    Ok(())
}

/// Materialize canonical model v1 exactly as it is hashed and written in AYC.
#[must_use]
pub fn canonical_model_v1(model: &Model) -> String {
    let mut text = String::new();
    // `String` implements an infallible `fmt::Write` sink.
    let _ = write_canonical_model_v1(&mut text, model);
    text
}

struct CanonicalDigestWriter {
    digest: Sha256,
    bytes: usize,
    max_bytes: Option<usize>,
    deadline: Option<Instant>,
    failed: bool,
}

impl CanonicalDigestWriter {
    fn new(max_bytes: Option<usize>, deadline: Option<Instant>) -> Self {
        Self {
            digest: Sha256::new(),
            bytes: 0,
            max_bytes,
            deadline,
            failed: false,
        }
    }

    fn finish(self) -> Option<[u8; 32]> {
        if self.failed
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return None;
        }
        Some(self.digest.finalize().into())
    }
}

impl fmt::Write for CanonicalDigestWriter {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let Some(next) = self.bytes.checked_add(text.len()) else {
            self.failed = true;
            return Err(fmt::Error);
        };
        if self.max_bytes.is_some_and(|limit| next > limit)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.failed = true;
            return Err(fmt::Error);
        }
        self.digest.update(text.as_bytes());
        self.bytes = next;
        Ok(())
    }
}

/// Stream canonical v1 directly into SHA-256 under an absolute deadline and
/// byte cap. No canonical-model `String` is materialized.
pub(crate) fn canonical_digest_bytes_bounded(
    model: &Model,
    deadline: Option<Instant>,
    max_bytes: usize,
) -> Option<[u8; 32]> {
    let mut writer = CanonicalDigestWriter::new(Some(max_bytes), deadline);
    write_canonical_model_v1(&mut writer, model).ok()?;
    writer.finish()
}

/// The `model canon v1` digest.
#[must_use]
pub fn canonical_digest(model: &Model) -> String {
    let digest = canonical_digest_bytes(model);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

pub(crate) fn canonical_digest_bytes(model: &Model) -> [u8; 32] {
    let mut writer = CanonicalDigestWriter::new(None, None);
    // With neither a byte cap nor a deadline, the sink can fail only if the
    // canonical length overflows `usize`, impossible for an addressable model.
    let _ = write_canonical_model_v1(&mut writer, model);
    writer.digest.finalize().into()
}

fn emitted_model_canon_digest(
    model: &Model,
    outcome: &Outcome,
    sat_relu: Option<&SatReluInfeasibilityCertificate>,
) -> String {
    // The SAT/ReLU certificate is constructed only after the bounded producer
    // has replayed its RUP DAG, and its private constructor binds the exact
    // canonical-model digest before the session can publish the refutation.
    // Reuse that retained digest when this is the evidence `emit` will write;
    // hashing the full model again here used to duplicate verdict-critical
    // work on every SAT/ReLU UNSAT. A manually assembled, mismatched EmitCtx
    // remains fail-closed: the public checker re-derives this header digest
    // from the supplied model text and rejects the mismatch.
    if matches!(
        outcome,
        Outcome::Infeasible {
            cert: None,
            tree_cert: None
        }
    ) {
        if let Some(certificate) = sat_relu {
            return digest_hex(certificate.model_canon_sha256());
        }
    }
    canonical_digest(model)
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

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
struct EmittedClaim {
    name: &'static str,
    kind: EvidenceKind,
    source: Option<String>,
}

/// Serialize an outcome as a `.ayc` certificate.
///
/// Emission is total: every verdict produces a certificate, including verdicts
/// the solver could not prove. `evidence dual NONE` on a MILP optimum is a
/// FEATURE — one line saying "this exact point attains the value; we cannot
/// show you why nothing beats it" is strictly more useful than emitting
/// nothing.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn emit(ctx: &EmitCtx<'_>, outcome: &Outcome) -> String {
    let mut claims: Vec<EmittedClaim> = Vec::new();
    let mut blocks = String::new();
    let mut extras = String::new();
    let mut truncated: Vec<String> = Vec::new();

    // A block is admitted only if it fits the byte cap; otherwise the claim it
    // would have backed is downgraded, loudly.
    let cap = ctx.max_bytes;
    // `truncated` is a PARAMETER, not a capture. Capturing it mutably made the
    // closure hold a mutable borrow for its whole lifetime, which collided with the
    // codec paths below that record their own `truncated` entries directly (they
    // have no byte count to report, so they cannot go through `admit`). Passing it
    // in keeps one writer at a time and needs no interior mutability.
    let admit =
        |blocks: &mut String, truncated: &mut Vec<String>, body: String, what: &str| -> bool {
            if let Some(cap) = cap {
                if blocks.len() + body.len() > cap {
                    truncated.push(format!("truncated {what} bytes={} cap={cap}", body.len()));
                    return false;
                }
            }
            blocks.push_str(&body);
            true
        };

    let verdict = match outcome {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            // PRIMAL: a witness is always succinctly checkable — plug the point
            // into the original file and check every row exactly, plus
            // integrality. This is the half that today's CLI could NOT emit for
            // an `Optimal` at all.
            let body = witness_block(ctx, model_values);
            if admit(&mut blocks, &mut truncated, body, "witness") {
                claims.push(EmittedClaim {
                    name: "primal",
                    kind: EvidenceKind::Succinct,
                    source: Some("witness".into()),
                });
            } else {
                claims.push(EmittedClaim {
                    name: "primal",
                    kind: EvidenceKind::None,
                    source: Some("truncated".into()),
                });
            }

            // DUAL: derived from the type that is present. Nothing else.
            match cert {
                Some(oc) => {
                    let trivial = is_trivial_optcert(oc);
                    let body = optcert_block(oc, trivial);
                    if admit(&mut blocks, &mut truncated, body, "optcert") {
                        claims.push(EmittedClaim {
                            name: "dual",
                            // An empty-multiplier certificate for an exactly
                            // zero variable objective is a real universal
                            // bound. It says nothing about feasibility by
                            // itself, but the separately checked primal claim
                            // supplies that half; together they prove the
                            // optimal verdict exactly, including its offset.
                            kind: EvidenceKind::Succinct,
                            source: Some("optcert".into()),
                        });
                    } else {
                        claims.push(EmittedClaim {
                            name: "dual",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
                None => {
                    if let Some(certificate) = ctx.block_angular_optimality_certificate {
                        let body = block_angular_optimality_block(certificate);
                        let admitted = admit(
                            &mut blocks,
                            &mut truncated,
                            body,
                            "block-angular-optimality",
                        );
                        claims.push(EmittedClaim {
                            name: "dual",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "block-angular-optimality".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    } else if let Some(certificate) =
                        ctx.single_machine_scheduling_optimality_certificate
                    {
                        let body = single_machine_scheduling_optimality_block(certificate);
                        let admitted = admit(
                            &mut blocks,
                            &mut truncated,
                            body,
                            "single-machine-scheduling-optimality",
                        );
                        claims.push(EmittedClaim {
                            name: "dual",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "single-machine-scheduling-optimality".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    } else if let Some(certificate) = ctx.network_design_optimality_certificate {
                        match network_design_optimality_block(certificate) {
                            Some(body) => {
                                let admitted = admit(
                                    &mut blocks,
                                    &mut truncated,
                                    body,
                                    "network-design-optimality",
                                );
                                claims.push(EmittedClaim {
                                    name: "dual",
                                    kind: if admitted {
                                        EvidenceKind::Succinct
                                    } else {
                                        EvidenceKind::None
                                    },
                                    source: Some(if admitted {
                                        "network-design-optimality".into()
                                    } else {
                                        "truncated".into()
                                    }),
                                });
                            }
                            None => {
                                truncated.push(
                                    "truncated network-design-optimality bytes=unavailable \
                                     cap=codec"
                                        .to_owned(),
                                );
                                claims.push(EmittedClaim {
                                    name: "dual",
                                    kind: EvidenceKind::None,
                                    source: Some("truncated".into()),
                                });
                            }
                        }
                    } else {
                        claims.push(dual_claim_from_replay(
                            ctx,
                            &[
                                "objective-face-empty",
                                "pb-projection-optimal",
                                "pb-portfolio-projection-optimal",
                                "network-design-projection-optimal",
                                "open-domain-cap-optimal",
                                "hybrid-pb-lp-optimal",
                            ],
                        ));
                    }
                }
            }
            format!(
                "verdict optimal value={} frame=file",
                fmt_rat(&(value / ctx.obj_scale))
            )
        }
        Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound,
        } => {
            let body = witness_block(ctx, model_values);
            if admit(&mut blocks, &mut truncated, body, "witness") {
                claims.push(EmittedClaim {
                    name: "primal",
                    kind: EvidenceKind::Succinct,
                    source: Some("witness".into()),
                });
            } else {
                claims.push(EmittedClaim {
                    name: "primal",
                    kind: EvidenceKind::None,
                    source: Some("truncated".into()),
                });
            }
            // The interrupted-tree dual bound is a bare rational with no
            // multipliers: `Outcome::Feasible` documents that it is "not
            // independently checkable". It is recorded as UNCHECKED so a
            // consumer sees the number without the checker ever blessing it.
            if let Some(db) = dual_bound {
                let _ = writeln!(
                    extras,
                    "unchecked dual_bound={} frame=file",
                    fmt_rat(&(db / ctx.obj_scale))
                );
            }
            claims.push(EmittedClaim {
                name: "dual",
                kind: EvidenceKind::None,
                source: None,
            });
            let value = ctx.model.objective_value_at(model_values);
            format!(
                "verdict feasible value={} frame=file incumbent_only={}",
                fmt_rat(&(&value / ctx.obj_scale)),
                u8::from(*incumbent_only)
            )
        }
        Outcome::Infeasible { cert, tree_cert } => {
            // Root Farkas is PREFERRED when present: one combination to check
            // instead of a whole tree.
            if let Some(fc) = cert {
                let body = farkas_block(fc);
                if admit(&mut blocks, &mut truncated, body, "farkas") {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::Succinct,
                        source: Some("farkas".into()),
                    });
                } else {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::None,
                        source: Some("truncated".into()),
                    });
                }
            } else if let Some(tc) = tree_cert {
                let body = tree_block(tc);
                if admit(&mut blocks, &mut truncated, body, "tree") {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::Succinct,
                        source: Some("tree".into()),
                    });
                } else {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::None,
                        source: Some("truncated".into()),
                    });
                }
            } else if let Some(certificate) = ctx.sat_relu_infeasibility_certificate {
                let codec_limit = cap.map_or(MAX_SAT_RELU_RUP_BYTES, |limit| {
                    limit
                        .saturating_sub(blocks.len())
                        .min(MAX_SAT_RELU_RUP_BYTES)
                });
                match sat_relu_rup_block(certificate, codec_limit) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "sat-relu-rup");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "sat-relu-rup".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated
                            .push("truncated sat-relu-rup bytes=unavailable cap=codec".to_owned());
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(certificate) = ctx.parity_infeasibility_certificate {
                let body = parity_infeasibility_block(certificate);
                if admit(&mut blocks, &mut truncated, body, "parity-gf2") {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::Succinct,
                        source: Some("parity-gf2".into()),
                    });
                } else {
                    claims.push(EmittedClaim {
                        name: "infeasible",
                        kind: EvidenceKind::None,
                        source: Some("truncated".into()),
                    });
                }
            } else if let Some(certificate) = ctx.network_design_infeasibility_certificate {
                match network_design_infeasibility_block(certificate) {
                    Some(body) => {
                        let admitted = admit(
                            &mut blocks,
                            &mut truncated,
                            body,
                            "network-design-infeasibility",
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "network-design-infeasibility".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated network-design-infeasibility bytes=unavailable cap=codec"
                                .to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(dp) = ctx.single_row_dp_infeasibility_certificate {
                match single_row_dp_block(dp) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "single-row-dp");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "single-row-dp".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated
                            .push("truncated single-row-dp bytes=unavailable cap=codec".to_owned());
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(bdd) = ctx.multi_row_bdd_infeasibility_certificate {
                match multi_row_bdd_block(bdd) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "multi-row-bdd");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "multi-row-bdd".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated
                            .push("truncated multi-row-bdd bytes=unavailable cap=codec".to_owned());
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(dp) = ctx.open_domain_single_row_dp_infeasibility_certificate {
                match open_domain_dp_block(dp) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "open-domain-dp");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "open-domain-dp".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated open-domain-dp bytes=unavailable cap=codec".to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(bdd) = ctx.open_domain_multi_row_bdd_infeasibility_certificate {
                match open_domain_bdd_block(bdd) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "open-domain-bdd");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "open-domain-bdd".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated open-domain-bdd bytes=unavailable cap=codec".to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(certificate) = ctx.open_domain_hybrid_pb_lp_infeasibility_certificate
            {
                match open_domain_hybrid_pb_lp_block(certificate) {
                    Some(body) => {
                        let admitted = admit(
                            &mut blocks,
                            &mut truncated,
                            body,
                            "open-domain-hybrid-pb-lp",
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "open-domain-hybrid-pb-lp".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated open-domain-hybrid-pb-lp bytes=unavailable cap=codec"
                                .to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(certificate) =
                ctx.open_domain_hybrid_integer_lift_infeasibility_certificate
            {
                match open_domain_hybrid_integer_lift_block(certificate) {
                    Some(body) => {
                        let admitted = admit(
                            &mut blocks,
                            &mut truncated,
                            body,
                            "open-domain-hybrid-integer-lift",
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "open-domain-hybrid-integer-lift".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated open-domain-hybrid-integer-lift bytes=unavailable cap=codec"
                                .to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(certificate) = ctx.hybrid_pb_lp_infeasibility_certificate {
                match hybrid_pb_lp_block(certificate) {
                    Some(body) => {
                        let admitted = admit(&mut blocks, &mut truncated, body, "hybrid-pb-lp");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "hybrid-pb-lp".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated
                            .push("truncated hybrid-pb-lp bytes=unavailable cap=codec".to_owned());
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else if let Some(certificate) = ctx.hybrid_integer_lift_infeasibility_certificate {
                match hybrid_integer_lift_block(certificate) {
                    Some(body) => {
                        let admitted =
                            admit(&mut blocks, &mut truncated, body, "hybrid-integer-lift");
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: if admitted {
                                EvidenceKind::Succinct
                            } else {
                                EvidenceKind::None
                            },
                            source: Some(if admitted {
                                "hybrid-integer-lift".into()
                            } else {
                                "truncated".into()
                            }),
                        });
                    }
                    None => {
                        truncated.push(
                            "truncated hybrid-integer-lift bytes=unavailable cap=codec".to_owned(),
                        );
                        claims.push(EmittedClaim {
                            name: "infeasible",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
            } else {
                claims.push(infeasible_claim_from_replay(ctx));
            }
            "verdict infeasible".to_string()
        }
        Outcome::Unbounded => {
            // A ray IS succinctly certifiable; this build has no ray
            // certificate type, so the honest report is NONE.
            claims.push(EmittedClaim {
                name: "unbounded",
                kind: EvidenceKind::None,
                source: None,
            });
            "verdict unbounded".to_string()
        }
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => {
            let _ = writeln!(
                extras,
                "unchecked dual_bound={} frame=file rigorous={}",
                fmt_rat(&(dual_bound / ctx.obj_scale)),
                u8::from(*rigorous)
            );
            claims.push(EmittedClaim {
                name: "dual",
                kind: EvidenceKind::None,
                source: None,
            });
            "verdict bound".to_string()
        }
        Outcome::Unknown { reason } => {
            // `WitnessRejected` is a SOLVER BUG SIGNAL. Its detail is emitted,
            // never swallowed.
            let _ = writeln!(extras, "reason {}", unknown_reason_line(reason));
            "verdict unknown".to_string()
        }
        // `Outcome` is `#[non_exhaustive]`: a future verdict must be REPORTED
        // rather than silently dropped, and must carry no claims (so the
        // checker reports UNVERIFIED, never VERIFIED).
        #[allow(unreachable_patterns)]
        other => format!("verdict other detail={}", sanitize(&format!("{other:?}"))),
    };

    // Every replay claim recorded by the solve is emitted, whether or not a
    // claim references it: `--list-replay-claims` over a corpus is how a
    // regression from PROVABLE to TRUSTED becomes visible.
    for rc in ctx.replay_claims {
        let body = replay_block(rc);
        let _ = admit(&mut blocks, &mut truncated, body, "replay");
    }

    let mut out = String::new();
    let _ = writeln!(out, "%AYC {AYC_VERSION}");
    let _ = writeln!(
        out,
        "model file sha256:{} bytes={} form=text",
        sha256_hex(ctx.model_text.as_bytes()),
        ctx.model_text.len()
    );
    let _ = writeln!(
        out,
        "model canon v1 sha256:{}",
        emitted_model_canon_digest(ctx.model, outcome, ctx.sat_relu_infeasibility_certificate)
    );
    let intcols = (0..ctx.model.num_cols())
        .filter(|&j| ctx.model.col_kind(Col(j as u32)).is_integral())
        .count();
    let _ = writeln!(
        out,
        "model shape rows={} cols={} intcols={intcols} sense={} obj_scale={}",
        ctx.model.num_rows(),
        ctx.model.num_cols(),
        sense_token(ctx.model.sense()),
        fmt_rat(ctx.obj_scale)
    );
    let _ = writeln!(
        out,
        "solver ay-milp {} {}",
        env!("CARGO_PKG_VERSION"),
        sanitize(ctx.provenance)
    );
    let _ = writeln!(out, "{verdict}");
    for c in &claims {
        match &c.source {
            Some(s) => {
                let _ = writeln!(out, "evidence {} {} {s}", c.name, c.kind.token());
            }
            None => {
                let _ = writeln!(out, "evidence {} {}", c.name, c.kind.token());
            }
        }
    }
    out.push_str(&extras);
    for t in &truncated {
        let _ = writeln!(out, "{t}");
    }
    out.push_str(&blocks);
    let digest = sha256_hex(out.as_bytes());
    let _ = writeln!(out, "%END sha256:{digest}");
    out
}

/// A dual claim from the replay ledger, or `NONE`. There is no third option
/// and no way for a caller to ask for `SUCCINCT` here.
fn dual_claim_from_replay(ctx: &EmitCtx<'_>, wanted: &[&str]) -> EmittedClaim {
    if let Some(rc) = ctx
        .replay_claims
        .iter()
        .find(|r| wanted.contains(&r.claim.as_str()))
    {
        EmittedClaim {
            name: "dual",
            kind: EvidenceKind::Replay,
            source: Some(rc.claim.clone()),
        }
    } else {
        EmittedClaim {
            name: "dual",
            kind: EvidenceKind::None,
            source: None,
        }
    }
}

fn infeasible_claim_from_replay(ctx: &EmitCtx<'_>) -> EmittedClaim {
    if let Some(rc) = ctx.replay_claims.iter().find(|r| {
        r.claim == "feasibility-face-empty"
            || r.claim == "coset-inconsistent"
            || r.claim == "sat-relu-cnf-unsat"
            || r.claim == "direct-cnf-unsat"
            || r.claim == "pb-projection-infeasible"
            || r.claim == "pb-portfolio-projection-infeasible"
            || r.claim == "network-design-projection-infeasible"
            || r.claim == "open-domain-projection-infeasible"
            || r.claim == "hybrid-pb-lp-infeasible"
    }) {
        EmittedClaim {
            name: "infeasible",
            kind: EvidenceKind::Replay,
            source: Some(rc.claim.clone()),
        }
    } else {
        EmittedClaim {
            name: "infeasible",
            kind: EvidenceKind::None,
            source: None,
        }
    }
}

/// Whether an optimality certificate is the exact empty-multiplier bound for
/// an identically-zero variable objective. The marker is diagnostic only: with
/// a separately verified feasible point, this bound proves the optimum.
fn is_trivial_optcert(oc: &OptimalityCertificate) -> bool {
    oc.bound.is_zero() && oc.objective.iter().all(|(_, a)| a.is_zero())
}

fn unknown_reason_line(r: &UnknownReason) -> String {
    match r {
        UnknownReason::Timeout => "timeout".into(),
        UnknownReason::Interrupted => "interrupted".into(),
        UnknownReason::IterationLimit => "iteration-limit".into(),
        UnknownReason::MemoryLimit => "memory-limit".into(),
        UnknownReason::CertificateUnavailable => "certificate-unavailable".into(),
        UnknownReason::SolverIncomplete { detail } => {
            format!("solver-incomplete detail={}", sanitize(detail))
        }
        // The one reason that means the SOLVER IS WRONG. Never swallowed.
        UnknownReason::WitnessRejected { detail } => {
            format!("witness-rejected detail={}", sanitize(detail))
        }
        // `UnknownReason` is `#[non_exhaustive]`.
        #[allow(unreachable_patterns)]
        other => format!("other detail={}", sanitize(&format!("{other:?}"))),
    }
}

/// Collapse anything that could forge a record boundary.
fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect::<String>()
        .trim()
        .to_string()
}

fn witness_block(ctx: &EmitCtx<'_>, values: &[BigRational]) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "witness cols={}", values.len());
    for (j, v) in values.iter().enumerate() {
        let name = ctx.col_names.get(j).map_or("-", String::as_str);
        let _ = writeln!(s, "x {j} {name} {}", fmt_rat(v));
    }
    let _ = writeln!(s, "end");
    s
}

fn write_multipliers(s: &mut String, mults: &[Multiplier]) {
    for m in mults {
        match m.fact {
            FactRef::RowBound { row, side } => {
                let _ = writeln!(
                    s,
                    "mult row {} {} {}",
                    row.index(),
                    side_token(side),
                    fmt_rat(&m.coeff)
                );
            }
            FactRef::ColBound { col, side } => {
                let _ = writeln!(
                    s,
                    "mult col {} {} {}",
                    col.index(),
                    side_token(side),
                    fmt_rat(&m.coeff)
                );
            }
            // `FactRef` is `#[non_exhaustive]`: a future variant must not be
            // silently dropped into a shorter, still-verifying certificate.
            #[allow(unreachable_patterns)]
            _ => {
                let _ = writeln!(s, "mult unsupported");
            }
        }
    }
}

fn farkas_block(fc: &FarkasCertificate) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "farkas mults={}", fc.multipliers.len());
    write_multipliers(&mut s, &fc.multipliers);
    let _ = writeln!(s, "end");
    s
}

fn optcert_block(oc: &OptimalityCertificate, trivial: bool) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "optcert sense={} bound={} frame=model trivial={}",
        sense_token(oc.sense),
        fmt_rat(&oc.bound),
        u8::from(trivial)
    );
    // The certificate names its OWN objective: `tighten_col_bounds` produces
    // certificates over per-column objectives, and a checker that assumed the
    // model's objective would bless a bound on a different function.
    for (c, a) in &oc.objective {
        let _ = writeln!(s, "obj {c} {}", fmt_rat(a));
    }
    write_multipliers(&mut s, &oc.multipliers);
    let _ = writeln!(s, "end");
    s
}

fn tree_block(tc: &MilpInfeasibilityCertificate) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "tree");
    // Explicit pre-order. `split` consumes exactly two following nodes (lo then
    // hi); `leaf` runs to its `endleaf`. Written iteratively — a certificate is
    // input data and its depth must not be the writer's stack limit.
    let mut stack: Vec<&TreeNode> = vec![&tc.root];
    while let Some(node) = stack.pop() {
        match node {
            TreeNode::Split { col, cut, lo, hi } => {
                let _ = writeln!(s, "split {} {}", col.index(), fmt_rat(cut));
                stack.push(hi);
                stack.push(lo);
            }
            TreeNode::Leaf { farkas } => {
                let _ = writeln!(s, "leaf");
                write_multipliers(&mut s, &farkas.multipliers);
                let _ = writeln!(s, "endleaf");
            }
        }
    }
    let _ = writeln!(s, "end");
    s
}

fn parity_infeasibility_block(certificate: &ParityInfeasibilityCertificate) -> String {
    let mut block = String::new();
    let _ = writeln!(block, "parity-gf2 rows={}", certificate.rows().len());
    for &row in certificate.rows() {
        let _ = writeln!(block, "row {row}");
    }
    let _ = writeln!(block, "end");
    block
}

const MAX_SAT_RELU_RUP_BYTES: usize = 64 * 1024 * 1024;
const MAX_SAT_RELU_RUP_VARS: usize = 1_000_000;
const MAX_SAT_RELU_RUP_ORIGINALS: usize = 2_000_000;
const MAX_SAT_RELU_RUP_STEPS: usize = 2_000_000;
const MAX_SAT_RELU_RUP_LITERALS: usize = 8_000_000;
const MAX_SAT_RELU_RUP_HINTS: usize = 8_000_000;
const MAX_SAT_RELU_RUP_ITEMS_PER_STEP: usize = 1_048_576;

fn resolution_literal_token(literal: Literal) -> Option<i32> {
    let variable = i32::try_from(literal.variable().index())
        .ok()?
        .checked_add(1)?;
    Some(if literal.is_positive() {
        variable
    } else {
        -variable
    })
}

fn digest_hex(digest: &[u8; 32]) -> String {
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

fn sat_relu_rup_structure_is_canonical(certificate: &SatReluInfeasibilityCertificate) -> bool {
    let derived = certificate.derived();
    let Some(last) = derived.last() else {
        return false;
    };
    if last.id != certificate.empty_clause_id() || !last.clause.is_empty() {
        return false;
    }

    let mut previous = certificate.num_original_clauses() as u64;
    for (index, step) in derived.iter().enumerate() {
        if step.id <= previous
            || step
                .clause
                .iter()
                .any(|literal| literal.variable().index() >= certificate.num_vars())
        {
            return false;
        }
        if step.rup_hints.iter().any(|&hint| {
            hint == 0
                || hint >= step.id
                || (hint > certificate.num_original_clauses() as u64
                    && derived[..index]
                        .binary_search_by_key(&hint, |known| known.id)
                        .is_err())
        }) {
            return false;
        }
        previous = step.id;
    }
    true
}

fn sat_relu_rup_block(
    certificate: &SatReluInfeasibilityCertificate,
    byte_limit: usize,
) -> Option<String> {
    let byte_limit = byte_limit.min(MAX_SAT_RELU_RUP_BYTES);
    let derived_literals = certificate
        .derived()
        .iter()
        .try_fold(0usize, |total, step| total.checked_add(step.clause.len()))?;
    let hints = certificate
        .derived()
        .iter()
        .try_fold(0usize, |total, step| {
            total.checked_add(step.rup_hints.len())
        })?;
    if certificate.format() != 1
        || certificate.num_vars() > MAX_SAT_RELU_RUP_VARS
        || certificate.num_original_clauses() > MAX_SAT_RELU_RUP_ORIGINALS
        || certificate.derived().len() > MAX_SAT_RELU_RUP_STEPS
        || derived_literals > MAX_SAT_RELU_RUP_LITERALS
        || hints > MAX_SAT_RELU_RUP_HINTS
        || certificate.empty_clause_id() > u64::from(u32::MAX)
        || !sat_relu_rup_structure_is_canonical(certificate)
        || certificate.derived().iter().any(|step| {
            step.id == 0
                || step.id > u64::from(u32::MAX)
                || step.clause.len() > MAX_SAT_RELU_RUP_ITEMS_PER_STEP
                || step.rup_hints.len() > MAX_SAT_RELU_RUP_ITEMS_PER_STEP
        })
    {
        return None;
    }

    let mut block = String::new();
    let _ = writeln!(
        block,
        "sat-relu-rup format={} model=sha256:{} cnf=sha256:{} vars={} originals={} \
         steps={} derived_lits={} hints={} empty={}",
        certificate.format(),
        digest_hex(certificate.model_canon_sha256()),
        digest_hex(certificate.cnf_sha256()),
        certificate.num_vars(),
        certificate.num_original_clauses(),
        certificate.derived().len(),
        derived_literals,
        hints,
        certificate.empty_clause_id(),
    );
    if block.len() > byte_limit {
        return None;
    }
    for step in certificate.derived() {
        let _ = write!(block, "step {} lits={}", step.id, step.clause.len());
        for &literal in &step.clause {
            let _ = write!(block, " {}", resolution_literal_token(literal)?);
            if block.len() > byte_limit {
                return None;
            }
        }
        let _ = write!(block, " hints={}", step.rup_hints.len());
        for hint in &step.rup_hints {
            let _ = write!(block, " {hint}");
            if block.len() > byte_limit {
                return None;
            }
        }
        block.push('\n');
        if block.len() > byte_limit {
            return None;
        }
    }
    let _ = writeln!(block, "end");
    (block.len() <= byte_limit).then_some(block)
}

fn single_row_dp_block(certificate: &SingleRowDpInfeasibilityCertificate) -> Option<String> {
    let encoded = encode_single_row_dp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "single-row-dp json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn multi_row_bdd_block(certificate: &MultiRowBddInfeasibilityCertificate) -> Option<String> {
    let encoded = encode_multi_row_bdd_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "multi-row-bdd json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn open_domain_dp_block(certificate: &SingleRowDpInfeasibilityCertificate) -> Option<String> {
    let encoded = encode_single_row_dp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "open-domain-dp json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn open_domain_bdd_block(certificate: &MultiRowBddInfeasibilityCertificate) -> Option<String> {
    let encoded = encode_multi_row_bdd_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "open-domain-bdd json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn network_design_infeasibility_block(
    certificate: &NetworkDesignInfeasibilityCertificate,
) -> Option<String> {
    let (kind, encoded) = match crate::network_design_route::infeasibility_refutation(certificate) {
        crate::network_design_route::NetworkDesignPbRefutationRef::SingleRow(proof) => (
            "single-row",
            encode_single_row_dp_infeasibility_certificate_json(proof).ok()?,
        ),
        crate::network_design_route::NetworkDesignPbRefutationRef::MultiRow(proof) => (
            "multi-row",
            encode_multi_row_bdd_infeasibility_certificate_json(proof).ok()?,
        ),
    };
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(
        block,
        "network-design-infeasibility kind={kind} json_bytes={}",
        encoded.len()
    );
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn network_design_optimality_block(
    certificate: &NetworkDesignOptimalityCertificate,
) -> Option<String> {
    let (value, proof) = crate::network_design_route::optimality_parts(certificate);
    match proof {
        crate::network_design_route::NetworkDesignOptimalityProofRef::StrictBetter(proof) => {
            let encoded = encode_multi_row_bdd_infeasibility_certificate_json(proof).ok()?;
            let json = std::str::from_utf8(&encoded).ok()?;
            let mut block = String::new();
            let _ = writeln!(
                block,
                "network-design-optimality value={} frame=model json_bytes={}",
                fmt_rat(value),
                encoded.len()
            );
            let _ = writeln!(block, "{json}");
            let _ = writeln!(block, "end");
            Some(block)
        }
        crate::network_design_route::NetworkDesignOptimalityProofRef::PatternCount(proof) => {
            let width = proof.blocks.first()?.len();
            if proof.blocks.len() < 2
                || width == 0
                || proof.blocks.iter().any(|block| block.len() != width)
            {
                return None;
            }
            let mut block = String::new();
            let _ = writeln!(
                block,
                "network-design-optimality value={} frame=model kind=pattern-count \
                 pb_value={} blocks={} width={}",
                fmt_rat(value),
                proof.pb_value,
                proof.blocks.len(),
                width
            );
            for variables in &proof.blocks {
                block.push_str("block");
                for variable in variables {
                    let _ = write!(block, " {variable}");
                }
                block.push('\n');
            }
            let _ = writeln!(block, "end");
            Some(block)
        }
    }
}

fn block_angular_optimality_block(certificate: &BlockAngularOptimalityCertificate) -> String {
    let (value, multipliers, minimizers) =
        crate::block_angular_route::certificate_parts(certificate);
    let mut block = String::new();
    let _ = writeln!(
        block,
        "block-angular-optimality value={} frame=model masters={} blocks={}",
        fmt_rat(value),
        multipliers.len(),
        minimizers.len()
    );
    for (row, multiplier) in multipliers {
        let _ = writeln!(block, "master {row} {}", fmt_rat(multiplier));
    }
    for pattern in minimizers {
        if let Some((amounts, exits)) = crate::block_angular_route::source_pattern_parts(pattern) {
            let _ = write!(block, "source width={}", amounts.len());
            for amount in amounts {
                let _ = write!(block, " {amount}");
            }
            block.push_str(" exits");
            for exit in exits {
                let _ = write!(block, " {exit}");
            }
            block.push('\n');
        } else if let Some(exit) = crate::block_angular_route::initial_pattern_exit(pattern) {
            let _ = writeln!(block, "initial exit={exit}");
        }
    }
    let _ = writeln!(block, "end");
    block
}

fn single_machine_scheduling_optimality_block(
    certificate: &SingleMachineSchedulingOptimalityCertificate,
) -> String {
    let (value, sequence) = crate::scheduling_route::optimality_parts(certificate);
    let mut block = String::new();
    let _ = writeln!(
        block,
        "single-machine-scheduling-optimality value={} frame=model jobs={}",
        fmt_rat(value),
        sequence.len()
    );
    block.push_str("sequence");
    for column in sequence {
        let _ = write!(block, " {column}");
    }
    block.push('\n');
    let _ = writeln!(block, "end");
    block
}

fn hybrid_pb_lp_block(certificate: &HybridPbLpInfeasibilityCertificate) -> Option<String> {
    hybrid_pb_lp_named_block("hybrid-pb-lp", certificate)
}

fn open_domain_hybrid_pb_lp_block(
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Option<String> {
    hybrid_pb_lp_named_block("open-domain-hybrid-pb-lp", certificate)
}

fn hybrid_pb_lp_named_block(
    label: &str,
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_hybrid_pb_lp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "{label} json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn hybrid_integer_lift_block(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    hybrid_integer_lift_named_block("hybrid-integer-lift", certificate)
}

fn open_domain_hybrid_integer_lift_block(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    hybrid_integer_lift_named_block("open-domain-hybrid-integer-lift", certificate)
}

fn hybrid_integer_lift_named_block(
    label: &str,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_hybrid_integer_lift_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "{label} json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

fn replay_block(rc: &ReplayClaim) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "replay {}", sanitize(&rc.claim));
    let _ = writeln!(s, "device {}", sanitize(&rc.device));
    let _ = writeln!(s, "method {}", sanitize(&rc.method));
    let _ = writeln!(s, "arithmetic {}", sanitize(&rc.arithmetic));
    let _ = writeln!(
        s,
        "nodes-visited {}",
        rc.nodes_visited
            .map_or_else(|| "unknown".into(), |n| n.to_string())
    );
    let _ = writeln!(s, "node-budget {}", rc.node_budget);
    let _ = writeln!(s, "outcome {}", sanitize(&rc.outcome));
    for n in &rc.nondeterminism {
        let _ = writeln!(s, "nondeterminism {}", sanitize(n));
    }
    let _ = writeln!(s, "reproduce {}", sanitize(&rc.reproduce));
    let _ = writeln!(s, "tcb {}", sanitize(&rc.tcb));
    let _ = writeln!(s, "end");
    s
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Why a `.ayc` file could not be read.
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
    /// Whether the optimality certificate was marked trivial by the emitter
    /// (re-derived by [`check`], never trusted).
    pub optcert_trivial: bool,
    /// The whole-tree infeasibility certificate, when present.
    pub tree: Option<MilpInfeasibilityCertificate>,
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
const SUCCINCT_SOURCES: &[&str] = &[
    "witness",
    "farkas",
    "optcert",
    "tree",
    "sat-relu-rup",
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
const NONE_SOURCES: &[&str] = &["trivial-optcert", "truncated"];

/// Parse a `.ayc` certificate.
///
/// # Errors
/// Returns [`CertIoError`] on a malformed record, an unknown version, or a
/// mislabelled evidence record, and when a proof-owned exact value exceeds that
/// proof format's declared arithmetic bound.
#[allow(clippy::too_many_lines)]
pub fn parse(text: &str) -> Result<Certificate, CertIoError> {
    if text.len() > MAX_AYC_INPUT_BYTES {
        return Err(CertIoError::Malformed {
            line: 1,
            msg: "AYC input exceeds the 512 MiB parser cap".into(),
        });
    }
    let line_count = text
        .bytes()
        .try_fold(1usize, |count, byte| {
            if byte == b'\n' {
                count.checked_add(1)
            } else {
                Some(count)
            }
        })
        .ok_or_else(|| CertIoError::Malformed {
            line: 1,
            msg: "AYC line count overflows usize".into(),
        })?;
    if line_count > MAX_AYC_INPUT_LINES {
        return Err(CertIoError::Malformed {
            line: 1,
            msg: "AYC input exceeds the 8,000,000-line parser cap".into(),
        });
    }
    let mut header = Header {
        file_digest: String::new(),
        file_bytes: 0,
        canon_digest: String::new(),
        rows: 0,
        cols: 0,
        intcols: 0,
        sense: Sense::Minimize,
        obj_scale: BigRational::one(),
        solver: String::new(),
    };
    let mut verdict = String::new();
    let mut value = None;
    let mut value_frame = String::new();
    let mut claims: Vec<ParsedClaim> = Vec::new();
    let mut witness = None;
    let mut farkas = None;
    let mut optcert = None;
    let mut optcert_trivial = false;
    let mut tree = None;
    let mut parity_infeasibility = None;
    let mut sat_relu_infeasibility = None;
    let mut network_design_infeasibility = None;
    let mut network_design_optimality = None;
    let mut block_angular_optimality = None;
    let mut single_machine_scheduling_optimality = None;
    let mut single_row_dp = None;
    let mut multi_row_bdd = None;
    let mut open_domain_dp = None;
    let mut open_domain_bdd = None;
    let mut open_domain_hybrid_pb_lp = None;
    let mut open_domain_hybrid_integer_lift = None;
    let mut hybrid_pb_lp = None;
    let mut hybrid_integer_lift = None;
    let mut replay: Vec<ReplayClaim> = Vec::new();
    let mut unchecked = Vec::new();
    let mut truncated = Vec::new();
    let mut reason = None;
    let mut end_digest_ok = false;
    let mut saw_version = false;

    let lines: Vec<&str> = text.lines().collect();
    let mut i = 0usize;
    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_string(),
    };
    while i < lines.len() {
        let raw = lines[i];
        let l = raw.trim();
        if l.is_empty() || l.starts_with('#') {
            i += 1;
            continue;
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        match f[0] {
            "%AYC" => {
                let v: u32 = f
                    .get(1)
                    .and_then(|s| s.parse().ok())
                    .ok_or_else(|| bad(i, "malformed %AYC version"))?;
                if v != AYC_VERSION {
                    return Err(bad(i, &format!("unsupported format version {v}")));
                }
                saw_version = true;
                i += 1;
            }
            "model" => {
                match f.get(1).copied() {
                    Some("file") => {
                        header.file_digest = strip_sha(f.get(2).copied().unwrap_or_default())
                            .ok_or_else(|| bad(i, "malformed model file digest"))?;
                        header.file_bytes = kv_usize(&f, "bytes")
                            .ok_or_else(|| bad(i, "malformed model file bytes"))?;
                    }
                    Some("canon") => {
                        if f.get(2) != Some(&"v1") {
                            return Err(bad(i, "unsupported canonicalisation rule"));
                        }
                        header.canon_digest = strip_sha(f.get(3).copied().unwrap_or_default())
                            .ok_or_else(|| bad(i, "malformed canon digest"))?;
                    }
                    Some("shape") => {
                        header.rows = kv_usize(&f, "rows").ok_or_else(|| bad(i, "shape rows"))?;
                        header.cols = kv_usize(&f, "cols").ok_or_else(|| bad(i, "shape cols"))?;
                        header.intcols =
                            kv_usize(&f, "intcols").ok_or_else(|| bad(i, "shape intcols"))?;
                        header.sense = kv(&f, "sense")
                            .and_then(parse_sense)
                            .ok_or_else(|| bad(i, "shape sense"))?;
                        header.obj_scale = kv(&f, "obj_scale")
                            .and_then(parse_rat)
                            .ok_or_else(|| bad(i, "shape obj_scale"))?;
                    }
                    _ => return Err(bad(i, "unknown model record")),
                }
                i += 1;
            }
            "solver" => {
                header.solver = l.to_string();
                i += 1;
            }
            "verdict" => {
                verdict = f
                    .get(1)
                    .ok_or_else(|| bad(i, "verdict has no word"))?
                    .to_string();
                if let Some(v) = kv(&f, "value") {
                    value = Some(parse_rat(v).ok_or_else(|| bad(i, "malformed verdict value"))?);
                    value_frame = kv(&f, "frame")
                        .ok_or_else(|| bad(i, "verdict value has no frame"))?
                        .to_string();
                }
                i += 1;
            }
            "evidence" => {
                let name = f.get(1).ok_or_else(|| bad(i, "evidence has no claim"))?;
                let kind = f
                    .get(2)
                    .and_then(|t| EvidenceKind::from_token(t))
                    .ok_or_else(|| bad(i, "evidence has no kind"))?;
                let source = f.get(3).map(|s| (*s).to_string());
                // THE SAFETY PROPERTY OF THE WHOLE FORMAT. A record cannot
                // label a replay claim (or anything else) SUCCINCT: the source
                // token set for each kind is closed and checked HERE, so a
                // hand-edited file that promotes trust to proof is rejected as
                // malformed rather than being verified and reported as passing.
                match kind {
                    EvidenceKind::Succinct => {
                        let s = source
                            .as_deref()
                            .ok_or_else(|| bad(i, "SUCCINCT evidence names no source"))?;
                        if !SUCCINCT_SOURCES.contains(&s) {
                            return Err(CertIoError::MislabelledEvidence {
                                line: i + 1,
                                kind: "SUCCINCT".into(),
                                source_token: s.into(),
                            });
                        }
                    }
                    EvidenceKind::Replay => {
                        let s = source
                            .as_deref()
                            .ok_or_else(|| bad(i, "REPLAY evidence names no claim"))?;
                        if SUCCINCT_SOURCES.contains(&s) {
                            return Err(CertIoError::MislabelledEvidence {
                                line: i + 1,
                                kind: "REPLAY".into(),
                                source_token: s.into(),
                            });
                        }
                    }
                    EvidenceKind::None => {
                        if let Some(s) = source.as_deref() {
                            if !NONE_SOURCES.contains(&s) {
                                return Err(CertIoError::MislabelledEvidence {
                                    line: i + 1,
                                    kind: "NONE".into(),
                                    source_token: s.into(),
                                });
                            }
                        }
                    }
                }
                claims.push(ParsedClaim {
                    name: (*name).to_string(),
                    kind,
                    source,
                });
                i += 1;
            }
            "unchecked" => {
                unchecked.push(l.to_string());
                i += 1;
            }
            "truncated" => {
                truncated.push(l.to_string());
                i += 1;
            }
            "reason" => {
                reason = Some(l["reason".len()..].trim().to_string());
                i += 1;
            }
            "witness" => {
                let (vals, next) = parse_witness(&lines, i)?;
                witness = Some(vals);
                i = next;
            }
            "farkas" => {
                let (mults, next) = parse_mults(&lines, i + 1, "end")?;
                farkas = Some(FarkasCertificate { multipliers: mults });
                i = next;
            }
            "optcert" => {
                let (oc, trivial, next) = parse_optcert(&lines, i)?;
                optcert = Some(oc);
                optcert_trivial = trivial;
                i = next;
            }
            "tree" => {
                let (t, next) = parse_tree(&lines, i + 1)?;
                tree = Some(MilpInfeasibilityCertificate { root: t });
                i = next;
            }
            "parity-gf2" => {
                if parity_infeasibility.is_some() {
                    return Err(bad(i, "duplicate parity-gf2 block"));
                }
                let (certificate, next) = parse_parity_infeasibility(&lines, i)?;
                parity_infeasibility = Some(certificate);
                i = next;
            }
            "sat-relu-rup" => {
                if sat_relu_infeasibility.is_some() {
                    return Err(bad(i, "duplicate sat-relu-rup block"));
                }
                let (certificate, next) = parse_sat_relu_rup(&lines, i)?;
                sat_relu_infeasibility = Some(certificate);
                i = next;
            }
            "network-design-infeasibility" => {
                if network_design_infeasibility.is_some() {
                    return Err(bad(i, "duplicate network-design-infeasibility block"));
                }
                let kind = kv(&f, "kind")
                    .ok_or_else(|| bad(i, "network-design-infeasibility has no kind="))?;
                let (json, next) = parse_json_body(&lines, i, "network-design-infeasibility")?;
                let certificate = match kind {
                    "single-row" => {
                        let proof =
                            decode_single_row_dp_infeasibility_certificate_json(json.as_bytes())
                                .map_err(|error| CertIoError::Malformed {
                                    line: i + 2,
                                    msg: format!(
                                        "network-design single-row JSON rejected: {error}"
                                    ),
                                })?;
                        crate::network_design_route::infeasibility_from_single_row(proof)
                    }
                    "multi-row" => {
                        let proof =
                            decode_multi_row_bdd_infeasibility_certificate_json(json.as_bytes())
                                .map_err(|error| CertIoError::Malformed {
                                    line: i + 2,
                                    msg: format!("network-design multi-row JSON rejected: {error}"),
                                })?;
                        crate::network_design_route::infeasibility_from_multi_row(proof)
                    }
                    _ => return Err(bad(i, "unknown network-design refutation kind")),
                };
                network_design_infeasibility = Some(certificate);
                i = next;
            }
            "network-design-optimality" => {
                if network_design_optimality.is_some() {
                    return Err(bad(i, "duplicate network-design-optimality block"));
                }
                if kv(&f, "frame") != Some("model") {
                    return Err(bad(
                        i,
                        "network-design optimality value must use frame=model",
                    ));
                }
                let proof_value = kv(&f, "value")
                    .and_then(parse_rat)
                    .ok_or_else(|| bad(i, "network-design-optimality has invalid value="))?;
                match kv(&f, "kind").unwrap_or("multi-row") {
                    // `kind` was absent from the original v1 encoding. Keep
                    // accepting that exact wire form while making the new
                    // repeated-block proof explicitly discriminated.
                    "multi-row" => {
                        let (json, next) = parse_json_body(&lines, i, "network-design-optimality")?;
                        let proof =
                            decode_multi_row_bdd_infeasibility_certificate_json(json.as_bytes())
                                .map_err(|error| CertIoError::Malformed {
                                    line: i + 2,
                                    msg: format!(
                                        "network-design optimality JSON rejected: {error}"
                                    ),
                                })?;
                        network_design_optimality =
                            Some(crate::network_design_route::optimality_from_strict_better(
                                proof_value,
                                proof,
                            ));
                        i = next;
                    }
                    "pattern-count" => {
                        let (proof, next) = parse_network_design_pattern_count(&lines, i)?;
                        network_design_optimality =
                            Some(crate::network_design_route::optimality_from_pattern_count(
                                proof_value,
                                proof,
                            ));
                        i = next;
                    }
                    _ => return Err(bad(i, "unknown network-design optimality proof kind")),
                }
            }
            "block-angular-optimality" => {
                if block_angular_optimality.is_some() {
                    return Err(bad(i, "duplicate block-angular-optimality block"));
                }
                let (certificate, next) = parse_block_angular_optimality(&lines, i)?;
                block_angular_optimality = Some(certificate);
                i = next;
            }
            "single-machine-scheduling-optimality" => {
                if single_machine_scheduling_optimality.is_some() {
                    return Err(bad(
                        i,
                        "duplicate single-machine-scheduling-optimality block",
                    ));
                }
                let (certificate, next) = parse_single_machine_scheduling_optimality(&lines, i)?;
                single_machine_scheduling_optimality = Some(certificate);
                i = next;
            }
            "single-row-dp" => {
                let (proof, next) = parse_single_row_dp(&lines, i)?;
                single_row_dp = Some(proof);
                i = next;
            }
            "multi-row-bdd" => {
                let (proof, next) = parse_multi_row_bdd(&lines, i)?;
                multi_row_bdd = Some(proof);
                i = next;
            }
            "open-domain-dp" => {
                let (proof, next) = parse_single_row_dp(&lines, i)?;
                open_domain_dp = Some(proof);
                i = next;
            }
            "open-domain-bdd" => {
                let (proof, next) = parse_multi_row_bdd(&lines, i)?;
                open_domain_bdd = Some(proof);
                i = next;
            }
            "open-domain-hybrid-pb-lp" => {
                if open_domain_hybrid_pb_lp.is_some() {
                    return Err(bad(i, "duplicate open-domain-hybrid-pb-lp block"));
                }
                let (json, next) = parse_json_body(&lines, i, "open-domain-hybrid-pb-lp")?;
                let proof = decode_hybrid_pb_lp_infeasibility_certificate_json(json.as_bytes())
                    .map_err(|error| CertIoError::Malformed {
                        line: i + 2,
                        msg: format!("open-domain-hybrid-pb-lp JSON rejected: {error}"),
                    })?;
                open_domain_hybrid_pb_lp = Some(proof);
                i = next;
            }
            "open-domain-hybrid-integer-lift" => {
                if open_domain_hybrid_integer_lift.is_some() {
                    return Err(bad(i, "duplicate open-domain-hybrid-integer-lift block"));
                }
                let (json, next) = parse_json_body(&lines, i, "open-domain-hybrid-integer-lift")?;
                let proof =
                    decode_hybrid_integer_lift_infeasibility_certificate_json(json.as_bytes())
                        .map_err(|error| CertIoError::Malformed {
                            line: i + 2,
                            msg: format!("open-domain-hybrid-integer-lift JSON rejected: {error}"),
                        })?;
                open_domain_hybrid_integer_lift = Some(proof);
                i = next;
            }
            "hybrid-pb-lp" => {
                if hybrid_pb_lp.is_some() {
                    return Err(bad(i, "duplicate hybrid-pb-lp block"));
                }
                let (proof, next) = parse_hybrid_pb_lp(&lines, i)?;
                hybrid_pb_lp = Some(proof);
                i = next;
            }
            "hybrid-integer-lift" => {
                if hybrid_integer_lift.is_some() {
                    return Err(bad(i, "duplicate hybrid-integer-lift block"));
                }
                let (proof, next) = parse_hybrid_integer_lift(&lines, i)?;
                hybrid_integer_lift = Some(proof);
                i = next;
            }
            "replay" => {
                let (rc, next) = parse_replay(&lines, i)?;
                replay.push(rc);
                i = next;
            }
            "%END" => {
                let want = strip_sha(f.get(1).copied().unwrap_or_default())
                    .ok_or_else(|| bad(i, "malformed %END digest"))?;
                // Everything above this line, byte for byte.
                let mut body_len = 0usize;
                for l in &lines[..i] {
                    body_len += l.len() + 1;
                }
                let body = &text[..body_len.min(text.len())];
                end_digest_ok = sha256_hex(body.as_bytes()) == want;
                i += 1;
            }
            other => return Err(bad(i, &format!("unknown record `{other}`"))),
        }
    }
    if !saw_version {
        return Err(bad(0, "not an AYC certificate (no %AYC banner)"));
    }
    Ok(Certificate {
        header,
        verdict,
        value,
        value_frame,
        claims,
        witness,
        farkas,
        optcert,
        optcert_trivial,
        tree,
        parity_infeasibility,
        sat_relu_infeasibility,
        network_design_infeasibility,
        network_design_optimality,
        block_angular_optimality,
        single_machine_scheduling_optimality,
        single_row_dp,
        multi_row_bdd,
        open_domain_dp,
        open_domain_bdd,
        open_domain_hybrid_pb_lp,
        open_domain_hybrid_integer_lift,
        hybrid_pb_lp,
        hybrid_integer_lift,
        replay,
        unchecked,
        truncated,
        reason,
        end_digest_ok,
    })
}

fn strip_sha(t: &str) -> Option<String> {
    let h = t.strip_prefix("sha256:")?;
    if h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit()) {
        Some(h.to_string())
    } else {
        None
    }
}

fn kv<'a>(f: &[&'a str], key: &str) -> Option<&'a str> {
    f.iter()
        .find_map(|t| t.split_once('=').filter(|(k, _)| *k == key).map(|(_, v)| v))
}

fn kv_usize(f: &[&str], key: &str) -> Option<usize> {
    kv(f, key).and_then(|v| v.parse().ok())
}

fn parse_parity_infeasibility(
    lines: &[&str],
    start: usize,
) -> Result<(ParityInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_rows = kv_usize(&head, "rows").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "parity-gf2 has no rows=".into(),
    })?;
    let mut rows = Vec::with_capacity(expected_rows);
    let mut i = start + 1;
    while i < lines.len() {
        let line = lines[i].trim();
        if line == "end" {
            if rows.len() != expected_rows {
                return Err(CertIoError::Malformed {
                    line: start + 1,
                    msg: format!(
                        "parity-gf2 declares {expected_rows} rows, carries {}",
                        rows.len()
                    ),
                });
            }
            return Ok((ParityInfeasibilityCertificate::from_rows(rows), i + 1));
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() != 2 || fields[0] != "row" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed parity-gf2 row record".into(),
            });
        }
        let row = fields[1]
            .parse::<u32>()
            .map_err(|_| CertIoError::Malformed {
                line: i + 1,
                msg: "malformed parity-gf2 row index".into(),
            })?;
        if rows.last().is_some_and(|&previous| previous >= row) {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "parity-gf2 row indices are not strictly increasing".into(),
            });
        }
        rows.push(row);
        if rows.len() > expected_rows {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "parity-gf2 carries more rows than declared".into(),
            });
        }
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start + 1,
        msg: "parity-gf2 block not terminated".into(),
    })
}

fn parse_resolution_literal(
    token: &str,
    num_vars: usize,
    line: usize,
) -> Result<Literal, CertIoError> {
    let signed = token.parse::<i64>().map_err(|_| CertIoError::Malformed {
        line,
        msg: "malformed sat-relu-rup literal".into(),
    })?;
    let magnitude = signed
        .checked_abs()
        .filter(|value| *value > 0)
        .ok_or_else(|| CertIoError::Malformed {
            line,
            msg: "sat-relu-rup literal is zero or out of range".into(),
        })?;
    let index = usize::try_from(magnitude - 1).map_err(|_| CertIoError::Malformed {
        line,
        msg: "sat-relu-rup variable index does not fit usize".into(),
    })?;
    if index >= num_vars {
        return Err(CertIoError::Malformed {
            line,
            msg: format!("sat-relu-rup variable {index} is outside vars={num_vars}"),
        });
    }
    let variable = Variable::new(u32::try_from(index).map_err(|_| CertIoError::Malformed {
        line,
        msg: "sat-relu-rup variable index does not fit u32".into(),
    })?);
    Ok(if signed > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    })
}

fn parse_digest32(token: &str) -> Option<[u8; 32]> {
    let hex = token.strip_prefix("sha256:")?;
    if hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    let mut digest = [0u8; 32];
    for (index, byte) in digest.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).ok()?;
    }
    Some(digest)
}

fn push_parsed_value<T>(
    values: &mut Vec<T>,
    value: T,
    line: usize,
    what: &str,
) -> Result<(), CertIoError> {
    if values.len() == values.capacity() {
        values.try_reserve(1).map_err(|_| CertIoError::Malformed {
            line,
            msg: format!("sat-relu-rup could not allocate {what}"),
        })?;
    }
    values.push(value);
    Ok(())
}

fn parse_sat_relu_rup(
    lines: &[&str],
    start: usize,
) -> Result<(SatReluInfeasibilityCertificate, usize), CertIoError> {
    let malformed = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    if lines[start].len() > 4096 {
        return Err(malformed(start, "sat-relu-rup header exceeds 4096 bytes"));
    }
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let format = kv(&head, "format")
        .and_then(|token| token.parse::<u32>().ok())
        .ok_or_else(|| malformed(start, "sat-relu-rup has no valid format="))?;
    let model_canon_sha256 = kv(&head, "model")
        .and_then(parse_digest32)
        .ok_or_else(|| malformed(start, "sat-relu-rup has no canonical model digest"))?;
    let cnf_sha256 = kv(&head, "cnf")
        .and_then(parse_digest32)
        .ok_or_else(|| malformed(start, "sat-relu-rup has no canonical CNF digest"))?;
    let num_vars =
        kv_usize(&head, "vars").ok_or_else(|| malformed(start, "sat-relu-rup has no vars="))?;
    let original_count = kv_usize(&head, "originals")
        .ok_or_else(|| malformed(start, "sat-relu-rup has no originals="))?;
    let step_count =
        kv_usize(&head, "steps").ok_or_else(|| malformed(start, "sat-relu-rup has no steps="))?;
    let expected_derived_literals = kv_usize(&head, "derived_lits")
        .ok_or_else(|| malformed(start, "sat-relu-rup has no derived_lits="))?;
    let expected_hints =
        kv_usize(&head, "hints").ok_or_else(|| malformed(start, "sat-relu-rup has no hints="))?;
    let empty_clause_id = kv(&head, "empty")
        .and_then(|token| token.parse::<u64>().ok())
        .ok_or_else(|| malformed(start, "sat-relu-rup has no valid empty="))?;
    if format != 1
        || num_vars > MAX_SAT_RELU_RUP_VARS
        || original_count > MAX_SAT_RELU_RUP_ORIGINALS
        || step_count > MAX_SAT_RELU_RUP_STEPS
        || expected_derived_literals > MAX_SAT_RELU_RUP_LITERALS
        || expected_hints > MAX_SAT_RELU_RUP_HINTS
        || empty_clause_id == 0
        || empty_clause_id > u64::from(u32::MAX)
    {
        return Err(malformed(
            start,
            "sat-relu-rup header exceeds parser resource limits",
        ));
    }

    let body_end = start
        .checked_add(step_count)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| malformed(start, "sat-relu-rup line count overflows"))?;
    if body_end >= lines.len() {
        return Err(malformed(start, "sat-relu-rup body is truncated"));
    }
    let mut block_bytes = 0usize;
    for (offset, line) in lines[start..=body_end].iter().enumerate() {
        if line.len() > MAX_SAT_RELU_RUP_BYTES / 2 {
            return Err(malformed(
                start + offset,
                "sat-relu-rup record exceeds the per-line byte cap",
            ));
        }
        block_bytes = block_bytes
            .checked_add(line.len().saturating_add(1))
            .ok_or_else(|| malformed(start, "sat-relu-rup byte count overflows"))?;
        if block_bytes > MAX_SAT_RELU_RUP_BYTES {
            return Err(malformed(start, "sat-relu-rup block exceeds 64 MiB"));
        }
    }

    let mut cursor = start + 1;
    let mut derived = Vec::new();
    let mut known_derived_ids = Vec::new();
    let mut derived_literals = 0usize;
    let mut hint_count = 0usize;
    for _ in 0..step_count {
        let line = lines
            .get(cursor)
            .ok_or_else(|| malformed(cursor, "sat-relu-rup steps are truncated"))?;
        let mut fields = line.split_whitespace();
        if fields.next() != Some("step") {
            return Err(malformed(cursor, "expected sat-relu-rup step record"));
        }
        let id = fields
            .next()
            .and_then(|token| token.parse::<u64>().ok())
            .ok_or_else(|| malformed(cursor, "sat-relu-rup step has invalid id"))?;
        if id <= original_count as u64
            || id > u64::from(u32::MAX)
            || known_derived_ids
                .last()
                .is_some_and(|previous| *previous >= id)
        {
            return Err(malformed(
                cursor,
                "sat-relu-rup step id is not a positive monotone derived id",
            ));
        }
        let literal_count = fields
            .next()
            .and_then(|token| token.strip_prefix("lits="))
            .and_then(|token| token.parse::<usize>().ok())
            .ok_or_else(|| malformed(cursor, "sat-relu-rup step has invalid lits="))?;
        if literal_count > MAX_SAT_RELU_RUP_ITEMS_PER_STEP {
            return Err(malformed(cursor, "sat-relu-rup step has too many literals"));
        }
        let mut clause = Vec::new();
        for _ in 0..literal_count {
            let token = fields
                .next()
                .ok_or_else(|| malformed(cursor, "sat-relu-rup step literals are truncated"))?;
            let literal = parse_resolution_literal(token, num_vars, cursor + 1)?;
            push_parsed_value(&mut clause, literal, cursor + 1, "derived clause")?;
        }
        let this_hint_count = fields
            .next()
            .and_then(|token| token.strip_prefix("hints="))
            .and_then(|token| token.parse::<usize>().ok())
            .ok_or_else(|| malformed(cursor, "sat-relu-rup step has invalid hints="))?;
        if this_hint_count > MAX_SAT_RELU_RUP_ITEMS_PER_STEP {
            return Err(malformed(cursor, "sat-relu-rup step has too many hints"));
        }
        derived_literals = derived_literals
            .checked_add(literal_count)
            .ok_or_else(|| malformed(cursor, "sat-relu-rup derived literal count overflows"))?;
        hint_count = hint_count
            .checked_add(this_hint_count)
            .ok_or_else(|| malformed(cursor, "sat-relu-rup hint count overflows"))?;
        if derived_literals > expected_derived_literals || hint_count > expected_hints {
            return Err(malformed(
                cursor,
                "sat-relu-rup carries more proof data than declared",
            ));
        }
        let mut rup_hints = Vec::new();
        for _ in 0..this_hint_count {
            let hint = fields
                .next()
                .and_then(|token| token.parse::<u64>().ok())
                .ok_or_else(|| malformed(cursor, "sat-relu-rup step has an invalid hint id"))?;
            let known = hint > 0
                && hint < id
                && (hint <= original_count as u64
                    || known_derived_ids.binary_search(&hint).is_ok());
            if !known || hint > u64::from(u32::MAX) {
                return Err(malformed(
                    cursor,
                    "sat-relu-rup step references an unknown or forward hint",
                ));
            }
            push_parsed_value(&mut rup_hints, hint, cursor + 1, "RUP hints")?;
        }
        if fields.next().is_some() {
            return Err(malformed(cursor, "sat-relu-rup step has trailing tokens"));
        }
        push_parsed_value(
            &mut derived,
            RupStep {
                id,
                clause,
                rup_hints,
            },
            cursor + 1,
            "derived steps",
        )?;
        push_parsed_value(&mut known_derived_ids, id, cursor + 1, "derived IDs")?;
        cursor += 1;
    }
    if derived_literals != expected_derived_literals || hint_count != expected_hints {
        return Err(malformed(
            start,
            "sat-relu-rup aggregate counts do not match the body",
        ));
    }
    if lines.get(cursor).map(|line| line.trim()) != Some("end") {
        return Err(malformed(cursor, "sat-relu-rup block not terminated"));
    }
    let Some(last) = derived.last() else {
        return Err(malformed(start, "sat-relu-rup has no derived steps"));
    };
    if last.id != empty_clause_id || !last.clause.is_empty() {
        return Err(malformed(
            cursor,
            "sat-relu-rup final step is not the named empty clause",
        ));
    }
    Ok((
        SatReluInfeasibilityCertificate::from_wire_parts(
            format,
            model_canon_sha256,
            cnf_sha256,
            num_vars,
            original_count,
            derived,
            empty_clause_id,
        ),
        cursor + 1,
    ))
}

fn parse_witness(lines: &[&str], start: usize) -> Result<(Vec<BigRational>, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let n = kv_usize(&head, "cols").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "witness has no cols=".into(),
    })?;
    let mut vals = Vec::with_capacity(n);
    let mut i = start + 1;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == "end" {
            i += 1;
            break;
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        // `x <index> <name> <value>` — the index is checked against position so
        // a reordered or dropped record cannot silently shift the point.
        if f.len() != 4 || f[0] != "x" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed witness record".into(),
            });
        }
        if f[1].parse::<usize>().ok() != Some(vals.len()) {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "witness column index out of order".into(),
            });
        }
        vals.push(parse_rat(f[3]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed witness value".into(),
        })?);
        i += 1;
    }
    if vals.len() != n {
        return Err(CertIoError::Malformed {
            line: start + 1,
            msg: format!("witness declares {n} columns, carries {}", vals.len()),
        });
    }
    Ok((vals, i))
}

fn parse_single_row_dp(
    lines: &[&str],
    start: usize,
) -> Result<(SingleRowDpInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "single-row-dp has no json_bytes=".into(),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "single-row-dp JSON body is absent".into(),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "single-row-dp JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: "single-row-dp block not terminated".into(),
        });
    }
    let certificate = decode_single_row_dp_infeasibility_certificate_json(json_line.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("single-row-dp JSON rejected: {error}"),
        })?;
    Ok((certificate, start + 3))
}

fn parse_multi_row_bdd(
    lines: &[&str],
    start: usize,
) -> Result<(MultiRowBddInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "multi-row-bdd has no json_bytes=".into(),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "multi-row-bdd JSON body is absent".into(),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "multi-row-bdd JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: "multi-row-bdd block not terminated".into(),
        });
    }
    let certificate = decode_multi_row_bdd_infeasibility_certificate_json(json_line.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("multi-row-bdd JSON rejected: {error}"),
        })?;
    Ok((certificate, start + 3))
}

fn parse_single_machine_scheduling_optimality(
    lines: &[&str],
    start: usize,
) -> Result<(SingleMachineSchedulingOptimalityCertificate, usize), CertIoError> {
    let malformed = |line: usize, msg: String| CertIoError::Malformed { line, msg };
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    if kv(&head, "frame") != Some("model") {
        return Err(malformed(
            start + 1,
            "single-machine scheduling value must use frame=model".into(),
        ));
    }
    let value = kv(&head, "value").and_then(parse_rat).ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling block has invalid value=".into(),
        )
    })?;
    let jobs = kv_usize(&head, "jobs").ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling block has invalid jobs=".into(),
        )
    })?;
    let sequence_line = lines.get(start + 1).ok_or_else(|| {
        malformed(
            start + 2,
            "single-machine scheduling sequence is absent".into(),
        )
    })?;
    let fields: Vec<&str> = sequence_line.split_whitespace().collect();
    let expected_fields = jobs.checked_add(1).ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling jobs= overflows the sequence length".into(),
        )
    })?;
    if fields.first().copied() != Some("sequence") || fields.len() != expected_fields {
        return Err(malformed(
            start + 2,
            format!(
                "single-machine scheduling sequence has {} jobs, header declares {jobs}",
                fields.len().saturating_sub(1)
            ),
        ));
    }
    let sequence = fields[1..]
        .iter()
        .map(|token| {
            token.parse::<u32>().map_err(|_| {
                malformed(
                    start + 2,
                    format!("single-machine scheduling column `{token}` is not a u32"),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(malformed(
            start + 3,
            "single-machine scheduling block not terminated".into(),
        ));
    }
    Ok((
        crate::scheduling_route::optimality_from_parts(value, sequence),
        start + 3,
    ))
}

fn parse_json_body<'a>(
    lines: &'a [&'a str],
    start: usize,
    label: &str,
) -> Result<(&'a str, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: format!("{label} has no json_bytes="),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: format!("{label} JSON body is absent"),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "{label} JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: format!("{label} block not terminated"),
        });
    }
    Ok((json_line, start + 3))
}

fn parse_network_design_pattern_count(
    lines: &[&str],
    start: usize,
) -> Result<
    (
        crate::pattern_count_route::PatternCountOptimalityCertificate,
        usize,
    ),
    CertIoError,
> {
    // These are wire-parser allocation guards, kept at the exact classifier's
    // public envelope. Replay independently re-applies the production caps.
    const MAX_BLOCKS: usize = 16;
    const MAX_WIDTH: usize = 96;

    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let block_count = kv_usize(&head, "blocks")
        .filter(|count| (2..=MAX_BLOCKS).contains(count))
        .ok_or_else(|| bad(start, "network-design pattern count has invalid blocks="))?;
    let width = kv_usize(&head, "width")
        .filter(|width| (1..=MAX_WIDTH).contains(width))
        .ok_or_else(|| bad(start, "network-design pattern count has invalid width="))?;
    let pb_value = kv(&head, "pb_value")
        .and_then(|value| value.parse::<i128>().ok())
        .ok_or_else(|| bad(start, "network-design pattern count has invalid pb_value="))?;

    let mut blocks = Vec::with_capacity(block_count);
    let mut seen = BTreeSet::new();
    for block_index in 0..block_count {
        let line_index = start + 1 + block_index;
        let line = lines
            .get(line_index)
            .ok_or_else(|| bad(line_index, "network-design pattern block is absent"))?;
        let max_line_bytes = 5usize
            .checked_add(
                width
                    .checked_mul(11)
                    .ok_or_else(|| bad(line_index, "network-design pattern block is too wide"))?,
            )
            .ok_or_else(|| bad(line_index, "network-design pattern block is too wide"))?;
        if line.len() > max_line_bytes {
            return Err(bad(
                line_index,
                "network-design pattern block exceeds its bounded wire width",
            ));
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.first() != Some(&"block") || fields.len() != width + 1 {
            return Err(bad(
                line_index,
                "network-design pattern block has the wrong width",
            ));
        }
        let mut variables = Vec::with_capacity(width);
        for token in &fields[1..] {
            let variable = token
                .parse::<u32>()
                .ok()
                .filter(|&value| value != 0)
                .ok_or_else(|| {
                    bad(
                        line_index,
                        "network-design pattern block has an invalid PB variable",
                    )
                })?;
            if !seen.insert(variable) {
                return Err(bad(
                    line_index,
                    "network-design pattern block repeats a PB variable",
                ));
            }
            variables.push(variable);
        }
        blocks.push(variables);
    }
    let end = start + 1 + block_count;
    if lines.get(end).map(|line| line.trim()) != Some("end") {
        return Err(bad(
            end,
            "network-design pattern-count block not terminated",
        ));
    }
    Ok((
        crate::pattern_count_route::PatternCountOptimalityCertificate { blocks, pb_value },
        end + 1,
    ))
}

fn parse_block_angular_optimality(
    lines: &[&str],
    start: usize,
) -> Result<(BlockAngularOptimalityCertificate, usize), CertIoError> {
    const MAX_MASTERS: usize = 64;
    const MAX_BLOCKS: usize = 128;
    const MAX_WIDTH: usize = 8;

    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let bounded_rat = |line: usize, field: &str, token: &str| {
        parse_rat_bounded(token, crate::block_angular_route::MAX_RATIONAL_BITS).map_err(|error| {
            match error {
                BoundedRatParseError::Malformed => bad(line, &format!("invalid {field}")),
                BoundedRatParseError::BitLimit => CertIoError::RationalBitLimit {
                    line: line + 1,
                    field: field.to_owned(),
                    max_bits: crate::block_angular_route::MAX_RATIONAL_BITS,
                },
            }
        })
    };
    let header: Vec<&str> = lines[start].split_whitespace().collect();
    if kv(&header, "frame") != Some("model") {
        return Err(bad(
            start,
            "block-angular optimality value must use frame=model",
        ));
    }
    let value = bounded_rat(
        start,
        "block-angular optimum value",
        kv(&header, "value").ok_or_else(|| bad(start, "block-angular-optimality has no value="))?,
    )?;
    let master_count = kv_usize(&header, "masters")
        .filter(|count| *count <= MAX_MASTERS)
        .ok_or_else(|| bad(start, "block-angular master count exceeds format cap"))?;
    let block_count = kv_usize(&header, "blocks")
        .filter(|count| *count <= MAX_BLOCKS)
        .ok_or_else(|| bad(start, "block-angular block count exceeds format cap"))?;

    let mut line = start + 1;
    let mut multipliers = Vec::with_capacity(master_count);
    for _ in 0..master_count {
        let fields: Vec<&str> = lines
            .get(line)
            .ok_or_else(|| bad(line, "truncated block-angular master list"))?
            .split_whitespace()
            .collect();
        if fields.len() != 3 || fields[0] != "master" {
            return Err(bad(line, "malformed block-angular master record"));
        }
        let row = fields[1]
            .parse::<u32>()
            .map_err(|_| bad(line, "invalid block-angular master row"))?;
        let multiplier = bounded_rat(line, "block-angular master multiplier", fields[2])?;
        multipliers.push((row, multiplier));
        line += 1;
    }

    let mut minimizers = Vec::with_capacity(block_count);
    for _ in 0..block_count {
        let fields: Vec<&str> = lines
            .get(line)
            .ok_or_else(|| bad(line, "truncated block-angular minimizer list"))?
            .split_whitespace()
            .collect();
        match fields.first().copied() {
            Some("source") => {
                let width = kv_usize(&fields, "width")
                    .filter(|width| (1..=MAX_WIDTH).contains(width))
                    .ok_or_else(|| bad(line, "invalid block-angular source width"))?;
                if fields.len() != 3 + 2 * width || fields[2 + width] != "exits" {
                    return Err(bad(line, "malformed block-angular source minimizer"));
                }
                let amounts = fields[2..2 + width]
                    .iter()
                    .map(|value| {
                        value
                            .parse::<i64>()
                            .map_err(|_| bad(line, "invalid source amount"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let exits = fields[3 + width..]
                    .iter()
                    .map(|value| {
                        value
                            .parse::<u8>()
                            .map_err(|_| bad(line, "invalid source exit"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                minimizers.push(crate::block_angular_route::source_pattern(amounts, exits));
            }
            Some("initial") => {
                if fields.len() != 2 {
                    return Err(bad(line, "malformed block-angular initial minimizer"));
                }
                let exit = kv(&fields, "exit")
                    .and_then(|value| value.parse::<u8>().ok())
                    .ok_or_else(|| bad(line, "invalid initial exit"))?;
                minimizers.push(crate::block_angular_route::certified_initial_pattern(exit));
            }
            _ => return Err(bad(line, "unknown block-angular minimizer record")),
        }
        line += 1;
    }
    if lines.get(line).map(|value| value.trim()) != Some("end") {
        return Err(bad(line, "block-angular-optimality block has no end"));
    }
    Ok((
        crate::block_angular_route::certificate_from_parts(value, multipliers, minimizers),
        line + 1,
    ))
}

fn parse_hybrid_pb_lp(
    lines: &[&str],
    start: usize,
) -> Result<(HybridPbLpInfeasibilityCertificate, usize), CertIoError> {
    let (json, next) = parse_json_body(lines, start, "hybrid-pb-lp")?;
    let certificate =
        decode_hybrid_pb_lp_infeasibility_certificate_json(json.as_bytes()).map_err(|error| {
            CertIoError::Malformed {
                line: start + 2,
                msg: format!("hybrid-pb-lp JSON rejected: {error}"),
            }
        })?;
    Ok((certificate, next))
}

fn parse_hybrid_integer_lift(
    lines: &[&str],
    start: usize,
) -> Result<(HybridIntegerLiftInfeasibilityCertificate, usize), CertIoError> {
    let (json, next) = parse_json_body(lines, start, "hybrid-integer-lift")?;
    let certificate = decode_hybrid_integer_lift_infeasibility_certificate_json(json.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("hybrid-integer-lift JSON rejected: {error}"),
        })?;
    Ok((certificate, next))
}

fn parse_mults(
    lines: &[&str],
    start: usize,
    terminator: &str,
) -> Result<(Vec<Multiplier>, usize), CertIoError> {
    let mut mults = Vec::new();
    let mut i = start;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == terminator {
            return Ok((mults, i + 1));
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() != 5 || f[0] != "mult" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: format!("malformed multiplier record `{l}`"),
            });
        }
        let idx: u32 = f[2].parse().map_err(|_| CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier index".into(),
        })?;
        let side = parse_side(f[3]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier side".into(),
        })?;
        let fact = match f[1] {
            "row" => FactRef::RowBound {
                row: Row(idx),
                side,
            },
            "col" => FactRef::ColBound {
                col: Col(idx),
                side,
            },
            _ => {
                return Err(CertIoError::Malformed {
                    line: i + 1,
                    msg: "multiplier names neither row nor col".into(),
                })
            }
        };
        let coeff = parse_rat(f[4]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier coefficient".into(),
        })?;
        mults.push(Multiplier { fact, coeff });
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start,
        msg: format!("block not terminated by `{terminator}`"),
    })
}

fn parse_optcert(
    lines: &[&str],
    start: usize,
) -> Result<(OptimalityCertificate, bool, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let bad = |msg: &str| CertIoError::Malformed {
        line: start + 1,
        msg: msg.to_string(),
    };
    let sense = kv(&head, "sense")
        .and_then(parse_sense)
        .ok_or_else(|| bad("optcert sense"))?;
    let bound = kv(&head, "bound")
        .and_then(parse_rat)
        .ok_or_else(|| bad("optcert bound"))?;
    let trivial = kv(&head, "trivial") == Some("1");
    let mut objective = Vec::new();
    let mut i = start + 1;
    while i < lines.len() {
        let l = lines[i].trim();
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.first() != Some(&"obj") {
            break;
        }
        if f.len() != 3 {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed obj record".into(),
            });
        }
        let c: u32 = f[1].parse().map_err(|_| CertIoError::Malformed {
            line: i + 1,
            msg: "malformed obj column".into(),
        })?;
        let a = parse_rat(f[2]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed obj coefficient".into(),
        })?;
        objective.push((c, a));
        i += 1;
    }
    let (multipliers, next) = parse_mults(lines, i, "end")?;
    Ok((
        OptimalityCertificate {
            sense,
            objective,
            bound,
            multipliers,
        },
        trivial,
        next,
    ))
}

fn parse_tree(lines: &[&str], start: usize) -> Result<(TreeNode, usize), CertIoError> {
    // Iterative pre-order reconstruction: a certificate is input data, so its
    // depth must not be this parser's stack limit. Each frame is a pending
    // split plus the children seen so far (lo first, then hi).
    let mut frames: Vec<(Col, BigRational, Vec<TreeNode>)> = Vec::new();
    let mut root: Option<TreeNode> = None;
    let mut i = start;
    while i < lines.len() {
        let l = lines[i].trim();
        let f: Vec<&str> = l.split_whitespace().collect();
        let node = match f.first().copied() {
            Some("split") => {
                if f.len() != 3 {
                    return Err(CertIoError::Malformed {
                        line: i + 1,
                        msg: "malformed split record".into(),
                    });
                }
                let c: usize = f[1].parse().map_err(|_| CertIoError::Malformed {
                    line: i + 1,
                    msg: "malformed split column".into(),
                })?;
                let cut = parse_rat(f[2]).ok_or(CertIoError::Malformed {
                    line: i + 1,
                    msg: "malformed split cut".into(),
                })?;
                frames.push((Col(c as u32), cut, Vec::new()));
                i += 1;
                continue;
            }
            Some("leaf") => {
                let (mults, next) = parse_mults(lines, i + 1, "endleaf")?;
                i = next;
                TreeNode::Leaf {
                    farkas: FarkasCertificate { multipliers: mults },
                }
            }
            Some("end") => {
                i += 1;
                break;
            }
            _ => {
                return Err(CertIoError::Malformed {
                    line: i + 1,
                    msg: format!("malformed tree record `{l}`"),
                })
            }
        };
        // Fold the completed node into its parent, closing any parent whose two
        // children are now present.
        let mut done = node;
        loop {
            match frames.last_mut() {
                None => {
                    root = Some(done);
                    break;
                }
                Some((_, _, kids)) => {
                    kids.push(done);
                    if kids.len() < 2 {
                        break;
                    }
                    let (col, cut, kids) = frames.pop().expect("frame present");
                    let mut it = kids.into_iter();
                    let lo = it.next().expect("lo child");
                    let hi = it.next().expect("hi child");
                    done = TreeNode::Split {
                        col,
                        cut,
                        lo: Box::new(lo),
                        hi: Box::new(hi),
                    };
                }
            }
        }
    }
    match (root, frames.is_empty()) {
        (Some(r), true) => Ok((r, i)),
        _ => Err(CertIoError::Malformed {
            line: start,
            msg: "tree block is not a complete binary pre-order".into(),
        }),
    }
}

fn parse_replay(lines: &[&str], start: usize) -> Result<(ReplayClaim, usize), CertIoError> {
    let claim = lines[start].trim()["replay".len()..].trim().to_string();
    let mut rc = ReplayClaim {
        claim,
        device: String::new(),
        method: String::new(),
        arithmetic: String::new(),
        nodes_visited: None,
        node_budget: 0,
        outcome: String::new(),
        nondeterminism: Vec::new(),
        reproduce: String::new(),
        tcb: String::new(),
    };
    let mut i = start + 1;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == "end" {
            return Ok((rc, i + 1));
        }
        let (k, v) = l.split_once(char::is_whitespace).unwrap_or((l, ""));
        let v = v.trim().to_string();
        match k {
            "device" => rc.device = v,
            "method" => rc.method = v,
            "arithmetic" => rc.arithmetic = v,
            "nodes-visited" => rc.nodes_visited = v.parse().ok(),
            "node-budget" => rc.node_budget = v.parse().unwrap_or(0),
            "outcome" => rc.outcome = v,
            "nondeterminism" => rc.nondeterminism.push(v),
            "reproduce" => rc.reproduce = v,
            "tcb" => rc.tcb = v,
            other => {
                return Err(CertIoError::Malformed {
                    line: i + 1,
                    msg: format!("unknown replay record `{other}`"),
                })
            }
        }
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start + 1,
        msg: "replay block not terminated".into(),
    })
}

// ---------------------------------------------------------------------------
// The independent checker
// ---------------------------------------------------------------------------

/// The checker's verdict. The word VERIFIED is RESERVED.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStatus {
    /// Every claim is SUCCINCT and every block re-verified. Exit 0.
    Verified,
    /// SOME claim re-verified exactly and nothing was refuted, but at least
    /// one claim is REPLAY or NONE. Exit 11.
    ///
    /// This is a REFINEMENT OF [`Self::Unverified`], never of
    /// [`Self::Verified`]: it is a non-zero exit, it means the certificate as
    /// a whole is not proven, and no flag turns it into exit 0.
    ///
    /// # Why it exists
    ///
    /// A generic MILP optimum can carry an exactly checked primal point while
    /// having no exported proof that nothing beats it. A consumer must be able
    /// to distinguish that useful checked half from a file where nothing
    /// checked out, without upgrading the unproved optimum to `Verified`.
    ///
    /// Splitting the code, rather than upgrading the aggregate, is what keeps
    /// this honest: "some evidence checked out" and "this verdict is proven"
    /// are different statements and now have different exit codes.
    Partial,
    /// NOTHING re-verified: every claim is REPLAY or NONE. Exit 10.
    Unverified,
    /// A SUCCINCT block failed to verify. Exit 20.
    Refuted,
    /// A digest, shape, or the model itself did not match. Exit 30.
    Mismatch,
}

impl CheckStatus {
    /// The process exit code this status reserves.
    #[must_use]
    pub fn exit_code(self) -> i32 {
        match self {
            Self::Verified => 0,
            Self::Partial => 11,
            Self::Unverified => 10,
            Self::Refuted => 20,
            Self::Mismatch => 30,
        }
    }

    /// The status word.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Verified => "VERIFIED",
            Self::Partial => "PARTIAL",
            Self::Unverified => "UNVERIFIED",
            Self::Refuted => "REFUTED",
            Self::Mismatch => "MISMATCH",
        }
    }
}

/// One claim's independent re-check.
#[derive(Debug, Clone)]
pub struct ClaimReport {
    /// The claim's name.
    pub name: String,
    /// The kind the certificate asserted.
    pub kind: EvidenceKind,
    /// Whether this checker re-derived it. NEVER true for a REPLAY or NONE
    /// claim, whatever the certificate says.
    pub verified: bool,
    /// Human-readable detail.
    pub detail: String,
}

impl ClaimReport {
    /// This claim's standing, as one of the THREE outcomes a consumer must be
    /// able to tell apart.
    ///
    /// The pair `(kind, verified)` already encodes it, but only if the reader
    /// knows that `SUCCINCT` + `!verified` means the exported block was
    /// CHECKED AND FOUND WRONG, while `NONE`/`REPLAY` + `!verified` means
    /// there was nothing to check. Conflating those two is exactly the
    /// mistake this method exists to prevent.
    #[must_use]
    pub fn standing(&self) -> ClaimStanding {
        match (self.verified, self.kind) {
            (true, _) => ClaimStanding::Verified,
            (false, EvidenceKind::Succinct) => ClaimStanding::Refuted,
            (false, _) => ClaimStanding::Unbacked,
        }
    }
}

/// What a single claim's re-check established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimStanding {
    /// An exported object was re-derived exactly against the model.
    Verified,
    /// An exported SUCCINCT object was checked and DID NOT hold.
    Refuted,
    /// Nothing to check: the claim carries `NONE` or `REPLAY` evidence.
    Unbacked,
}

/// The checker's full report.
#[derive(Debug, Clone)]
pub struct CheckReport {
    /// The overall status.
    pub status: CheckStatus,
    /// Per-claim breakdown.
    pub claims: Vec<ClaimReport>,
    /// Notes about the model binding and anything the checker refused.
    pub notes: Vec<String>,
}

impl CheckReport {
    /// Claim names in a given standing, in certificate order.
    #[must_use]
    pub fn claims_in(&self, standing: ClaimStanding) -> Vec<&str> {
        self.claims
            .iter()
            .filter(|c| c.standing() == standing)
            .map(|c| c.name.as_str())
            .collect()
    }

    /// THE CENSUS LINE: one grep-able line naming every claim by standing.
    ///
    /// The aggregate status word answers "is this verdict proven?". It cannot
    /// answer "which of the things this certificate asserts did you actually
    /// re-derive?", and that is the question a consumer holding a `PARTIAL`
    /// needs answered — a verified `primal` on a SAT verdict is a point it may
    /// rely on, whether or not the dual half exists in this build.
    ///
    /// Empty lists print `-` rather than nothing so the three fields are
    /// always present and a parser never has to distinguish "absent" from
    /// "empty".
    #[must_use]
    pub fn census(&self) -> String {
        let join = |s: ClaimStanding| {
            let v = self.claims_in(s);
            if v.is_empty() {
                "-".to_owned()
            } else {
                v.join(",")
            }
        };
        format!(
            "CLAIMS verified={} refuted={} unbacked={}",
            join(ClaimStanding::Verified),
            join(ClaimStanding::Refuted),
            join(ClaimStanding::Unbacked),
        )
    }
}

/// Independently re-check a `.ayc` certificate against the ORIGINAL MODEL TEXT.
///
/// This function RE-PARSES the model itself with [`crate::read_mps`] and
/// re-derives every number it needs. It trusts NOTHING in the certificate: the
/// shape line, the objective value, the certificate's claimed bound and its
/// claimed objective are each re-derived and compared, and a disagreement is a
/// failure rather than a fact.
///
/// A REPLAY claim is reported as NOT VERIFIED, always. It cannot reach
/// [`CheckStatus::Verified`], and no flag in this function makes it.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn check(cert_text: &str, model_text: &str) -> CheckReport {
    let mut notes = Vec::new();
    let cert = match parse(cert_text) {
        Ok(c) => c,
        Err(e) => {
            return CheckReport {
                // A malformed or MISLABELLED certificate is refuted, not
                // ignored: a checker that shrugged at a bad file would let a
                // hand-edited "SUCCINCT" through as a non-answer.
                status: CheckStatus::Refuted,
                claims: Vec::new(),
                notes: vec![format!("certificate malformed: {e}")],
            };
        }
    };

    let mut status = CheckStatus::Verified;
    // Severity order: Mismatch > Refuted > Unverified > Partial > Verified. The
    // status only ever gets WORSE, so no later check can wash out an earlier
    // failure. `Partial` is never a demotion TARGET — it is derived once, at the
    // very end, from a status that already settled on `Unverified` — but it is
    // ranked here so the order is total and this function stays exhaustive.
    fn demote(s: CheckStatus, status: &mut CheckStatus) {
        let rank = |s: CheckStatus| match s {
            CheckStatus::Verified => 0u8,
            CheckStatus::Partial => 1,
            CheckStatus::Unverified => 2,
            CheckStatus::Refuted => 3,
            CheckStatus::Mismatch => 4,
        };
        if rank(s) > rank(*status) {
            *status = s;
        }
    }

    // 1. The model text this checker was handed must be the one the
    //    certificate was written against.
    let file_digest = sha256_hex(model_text.as_bytes());
    if file_digest == cert.header.file_digest && model_text.len() == cert.header.file_bytes {
        notes.push(format!("model file digest matches (sha256:{file_digest})"));
    } else {
        notes.push(format!(
            "model file digest MISMATCH: certificate says sha256:{} bytes={}, this file is \
             sha256:{file_digest} bytes={}",
            cert.header.file_digest,
            cert.header.file_bytes,
            model_text.len()
        ));
        demote(CheckStatus::Mismatch, &mut status);
    }
    if !cert.end_digest_ok {
        notes.push("%END body digest MISMATCH (the certificate was edited)".into());
        demote(CheckStatus::Mismatch, &mut status);
    }

    // 2. Re-parse the model. The checker does its own reading; nothing about
    //    the model comes from the certificate.
    let problem = match crate::read_mps(model_text) {
        Ok(p) => p,
        Err(e) => {
            notes.push(format!("model does not parse: {e}"));
            return CheckReport {
                status: CheckStatus::Mismatch,
                claims: Vec::new(),
                notes,
            };
        }
    };
    let model = &problem.model;

    // 3. The canonical digest binds the MODEL the indices refer to.
    let canon = canonical_digest(model);
    if canon == cert.header.canon_digest {
        notes.push(format!("model canon v1 digest matches (sha256:{canon})"));
    } else {
        notes.push(format!(
            "model canon v1 digest MISMATCH: certificate says sha256:{}, re-derived sha256:{canon}",
            cert.header.canon_digest
        ));
        demote(CheckStatus::Mismatch, &mut status);
    }
    let intcols = (0..model.num_cols())
        .filter(|&j| model.col_kind(Col(j as u32)).is_integral())
        .count();
    if cert.header.rows != model.num_rows()
        || cert.header.cols != model.num_cols()
        || cert.header.intcols != intcols
        || cert.header.sense != model.sense()
        || cert.header.obj_scale != problem.obj_scale
    {
        notes.push("model shape record MISMATCH against the re-parsed model".into());
        demote(CheckStatus::Mismatch, &mut status);
    }

    // The verdict value, re-expressed in the model frame. The checker converts
    // ONCE and says so; a value on the wire in the file frame is multiplied by
    // obj_scale to compare with anything the model computes.
    let claimed_model_value = cert
        .value
        .as_ref()
        .map(|v| match cert.value_frame.as_str() {
            "file" => v * &problem.obj_scale,
            _ => v.clone(),
        });

    let mut reports = Vec::new();
    for c in &cert.claims {
        let (verified, detail) = match (c.name.as_str(), c.kind) {
            ("primal", EvidenceKind::Succinct) => check_primal(
                &cert,
                model,
                claimed_model_value.as_ref(),
                cert.verdict == "optimal" || cert.verdict == "feasible",
            ),
            ("dual", EvidenceKind::Succinct) => check_dual(
                &cert,
                model,
                claimed_model_value.as_ref(),
                c.source.as_deref(),
            ),
            ("infeasible", EvidenceKind::Succinct) => {
                check_infeasible(&cert, model, c.source.as_deref())
            }
            (_, EvidenceKind::Succinct) => (
                false,
                format!("no independent check exists for claim `{}`", c.name),
            ),
            (_, EvidenceKind::Replay) => {
                let src = c.source.clone().unwrap_or_default();
                let rc = cert.replay.iter().find(|r| r.claim == src);
                let tcb = rc.map_or("<unnamed>", |r| r.tcb.as_str());
                let nd = rc.map_or_else(String::new, |r| r.nondeterminism.join(","));
                (
                    false,
                    format!(
                        "NOT VERIFIED — this claim has no exported object. Re-verification means \
                         RE-RUNNING the solver ({src}); the trusted computing base is {tcb}\
                         {}. This checker did not check it and does not vouch for it.",
                        if nd.is_empty() {
                            String::new()
                        } else {
                            format!("; nondeterminism: {nd}")
                        }
                    ),
                )
            }
            (_, EvidenceKind::None) => {
                let why = match c.source.as_deref() {
                    Some("trivial-optcert") => {
                        " (legacy emitter metadata downgraded an empty-multiplier zero-objective \
                         bound; current emitters export that exact bound as SUCCINCT optcert)"
                    }
                    Some("truncated") => " (the backing block exceeded the emitter's size cap)",
                    _ => "",
                };
                (
                    false,
                    format!("NOT VERIFIED — no evidence of any kind was exported{why}"),
                )
            }
        };
        if !verified {
            demote(
                if c.kind == EvidenceKind::Succinct {
                    CheckStatus::Refuted
                } else {
                    CheckStatus::Unverified
                },
                &mut status,
            );
        }
        reports.push(ClaimReport {
            name: c.name.clone(),
            kind: c.kind,
            verified,
            detail,
        });
    }

    // ---------------------------------------------------------------------
    // CLAIM-SET POLICY. The obligations are dictated by the VERDICT, never by
    // whichever records happen to be in the file.
    //
    // Without this, `check` was a scanner: it validated the claims present and
    // started at `Verified`, so DELETING a line deleted the obligation it
    // named. Since `%END` is a body checksum rather than a signature, and the
    // emitter's own tamper tests re-seal it, an editor could turn any honest
    // certificate into a blessed wrong answer:
    //   * misc07  — an honest FEASIBLE 2995 certificate, the verdict word
    //     rewritten to `optimal` and the `evidence dual NONE` line dropped,
    //     checked VERIFIED / exit 0 (the true optimum is 2810);
    //   * markshare1 — dropping `evidence dual REPLAY objective-face-empty`
    //     turned an honest UNVERIFIED into VERIFIED;
    //   * `verdict infeasible` carrying a primal witness of that very model
    //     checked VERIFIED, blessing INFEASIBLE while proving a point feasible.
    //
    // So: a REQUIRED claim that is absent is REFUTED, not merely unverified —
    // its absence is the forgery. A FORBIDDEN claim contradicts the verdict and
    // is likewise refuted. An honest certificate is unaffected: the emitter
    // always writes a record for every obligation, downgrading its KIND (to
    // `NONE`/`REPLAY`) when it has nothing to export, which still demotes to
    // `Unverified` through the loop above.
    let (required, forbidden): (&[&str], &[&str]) = match cert.verdict.as_str() {
        // Both halves are claims: the point attains the value, AND nothing
        // beats it. A missing dual record is the whole misc07 attack.
        "optimal" => (&["primal", "dual"], &["infeasible"]),
        // Asserts only that the point is feasible; it makes no optimality
        // claim, so `dual` is optional here.
        "feasible" => (&["primal"], &["infeasible"]),
        // A primal witness of the model is a direct contradiction.
        "infeasible" => (&["infeasible"], &["primal", "dual"]),
        // No claim these can carry today; `unknown` asserts nothing.
        "unbounded" | "unknown" => (&[], &["primal", "dual", "infeasible"]),
        // A DUAL BOUND AND NOTHING ELSE. `Outcome::Bound` is what the solver
        // returns when the budget expires with a rigorous bound but no
        // incumbent (`session::verdict_word`), so `dual` is REQUIRED — a
        // `bound` verdict carrying no dual record at all is the same forgery
        // shape as a stripped `optimal`. `primal` is forbidden because this
        // verdict asserts there is no incumbent, and `infeasible` because a
        // finite bound contradicts it.
        //
        // This arm exists because its ABSENCE was a live defect, not a
        // hypothetical: `bound` fell through to the unrecognised-verdict trap
        // below, so every ordinary timeout-with-a-bound run was reported
        // REFUTED / exit 20 — the same alarm as a detected forgery. Found on
        // cod105 by the restored Gurobi closure benchmark, which classified it
        // INCONCLUSIVE_INVALID for this reason. An alarm that fires on honest
        // timeouts carries no information when it fires on an attack.
        "bound" => (&["dual"], &["primal", "infeasible"]),
        // FAIL CLOSED on a verdict word this checker does not recognise.
        //
        // An earlier version of this policy fell through to "no obligations"
        // here, which was itself a bypass: `Optimal`, `optimum` and `opt` all
        // dodged the table and checked VERIFIED / exit 0 on the very misc07
        // forgery the policy was written to stop (only the exact lowercase
        // `optimal` carried obligations). A checker must never treat "I do not
        // know what this claims" as "this is fine" — an unknown verdict is
        // exactly the shape a forgery takes once the known ones are closed.
        other => {
            notes.push(format!(
                "UNRECOGNISED VERDICT `{other}` — this checker cannot determine what \
                 claims that verdict requires, so it refuses rather than passing it"
            ));
            demote(CheckStatus::Refuted, &mut status);
            (&[], &[])
        }
    };
    for want in required {
        if !cert.claims.iter().any(|c| c.name == *want) {
            notes.push(format!(
                "CLAIM-SET VIOLATION: verdict `{}` requires a `{want}` claim and the \
                 certificate carries none — a required claim is missing, which is a \
                 forged or truncated certificate, not an unproven one",
                cert.verdict
            ));
            demote(CheckStatus::Refuted, &mut status);
        }
    }
    for deny in forbidden {
        if cert.claims.iter().any(|c| c.name == *deny) {
            notes.push(format!(
                "CLAIM-SET VIOLATION: verdict `{}` cannot carry a `{deny}` claim — the \
                 certificate contradicts itself",
                cert.verdict
            ));
            demote(CheckStatus::Refuted, &mut status);
        }
    }

    if reports.is_empty() {
        notes.push(format!(
            "certificate carries NO claims (verdict `{}`) — nothing to verify",
            cert.verdict
        ));
        demote(CheckStatus::Unverified, &mut status);
    }
    for u in &cert.unchecked {
        notes.push(format!("NOT VERIFIED (emitter marked unchecked): {u}"));
        demote(CheckStatus::Unverified, &mut status);
    }
    for t in &cert.truncated {
        notes.push(format!("evidence dropped by the emitter's size cap: {t}"));
    }
    if let Some(r) = &cert.reason {
        notes.push(format!("solver reason: {r}"));
    }

    // THE PARTIAL REFINEMENT, applied LAST and only to `Unverified`.
    //
    // `Unverified` was doing two jobs: "nothing here checked out" and "some of
    // this checked out exactly and some of it has no object to check". Those
    // are different facts and a consumer must be able to act on the difference
    // — see [`CheckStatus::Partial`] for the distinction that motivated it.
    //
    // The split is deliberately one-directional and cannot leak upward:
    //   * it fires ONLY on an aggregate that already settled on `Unverified`,
    //     so `Refuted` and `Mismatch` are untouched and stay unmistakable;
    //   * it requires a claim this checker itself re-derived (`verified`,
    //     which `check` never sets for a `REPLAY` or `NONE` claim);
    //   * `Verified` is not reachable from here at all, so the reservation of
    //     the word — and of exit 0 — is exactly as strong as before.
    if status == CheckStatus::Unverified && reports.iter().any(|c| c.verified) {
        status = CheckStatus::Partial;
    }

    CheckReport {
        status,
        claims: reports,
        notes,
    }
}

/// Re-check the primal half: the point is feasible for the RE-PARSED model and
/// attains the claimed value. Nothing here reads a solver summary.
fn check_primal(
    cert: &Certificate,
    model: &Model,
    claimed_model_value: Option<&BigRational>,
    needs_value: bool,
) -> (bool, String) {
    let Some(x) = &cert.witness else {
        return (false, "claim names a witness block that is absent".into());
    };
    if x.len() != model.num_cols() {
        return (
            false,
            format!(
                "witness has {} entries, the re-parsed model has {} columns",
                x.len(),
                model.num_cols()
            ),
        );
    }
    if let Err(v) = model.check_point(x) {
        return (
            false,
            format!("the point is INFEASIBLE for the model: {v:?}"),
        );
    }
    if needs_value {
        let Some(claimed) = claimed_model_value else {
            return (false, "verdict carries no value to attain".into());
        };
        let attained = model.objective_value_at(x);
        if &attained != claimed {
            return (
                false,
                format!(
                    "the point attains {} (model frame), the verdict claims {claimed}",
                    fmt_rat(&attained)
                ),
            );
        }
    }
    (
        true,
        "the point satisfies every row, column bound and integrality constraint of the re-parsed \
         model, in exact rational arithmetic, and attains the claimed value"
            .into(),
    )
}

/// Re-check the dual half of an optimality claim.
///
/// Three independent things must hold, and the last two are exactly the ones a
/// checker that trusted the solver would skip:
/// 1. the multiplier identity verifies against the model;
/// 2. the certificate bounds THE MODEL'S OWN objective, not some other linear
///    form (`tighten_col_bounds` legitimately produces certificates over other
///    objectives — one of those would verify and prove nothing here);
/// 3. the bound, plus the model's objective offset, MEETS the claimed optimum.
fn check_dual(
    cert: &Certificate,
    model: &Model,
    claimed_model_value: Option<&BigRational>,
    source: Option<&str>,
) -> (bool, String) {
    if source == Some("block-angular-optimality") {
        let Some(proof) = &cert.block_angular_optimality else {
            return (
                false,
                "claim names a block-angular-optimality block that is absent".into(),
            );
        };
        let Some(claimed) = claimed_model_value else {
            return (
                false,
                "block-angular optimality claim has no verdict value".into(),
            );
        };
        return match crate::block_angular_route::verify_optimality_certificate(
            model, claimed, proof,
        ) {
            Ok(()) => (
                true,
                "the integral conservation-chain decomposition was rebuilt from the source \
                 model, every bounded capacity tuple and chain exit was re-priced exactly, and \
                 the resulting Lagrangian lower bound meets the claimed optimum"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the block-angular optimality artifact DOES NOT verify: {error}"),
            ),
        };
    }
    if source == Some("single-machine-scheduling-optimality") {
        let Some(proof) = &cert.single_machine_scheduling_optimality else {
            return (
                false,
                "claim names a single-machine-scheduling-optimality block that is absent".into(),
            );
        };
        let Some(claimed) = claimed_model_value else {
            return (
                false,
                "single-machine scheduling claim has no verdict value".into(),
            );
        };
        return match crate::scheduling_route::verify_optimality_certificate(model, claimed, proof) {
            Ok(()) => (
                true,
                "the source scheduling formulation and sequence were rebuilt and checked in \
                 exact arithmetic, and an independent bounded subset/Pareto DP replay proved \
                 the claimed optimum"
                    .into(),
            ),
            Err(error) => (
                false,
                format!(
                    "the single-machine scheduling optimality artifact DOES NOT verify: {error}"
                ),
            ),
        };
    }
    if source == Some("network-design-optimality") {
        let Some(proof) = &cert.network_design_optimality else {
            return (
                false,
                "claim names a network-design-optimality block that is absent".into(),
            );
        };
        let Some(claimed) = claimed_model_value else {
            return (
                false,
                "network-design optimality claim has no verdict value".into(),
            );
        };
        return match crate::network_design_route::verify_optimality_certificate(
            model, claimed, proof,
        ) {
            Ok(()) => (
                true,
                "the exact Hoffman projection was rebuilt from the re-parsed model, and an \
                 independent exact PB artifact replay proved the claimed master optimum"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the network-design optimality artifact DOES NOT verify: {error}"),
            ),
        };
    }
    if source != Some("optcert") {
        return (false, "claim names an unsupported dual block".into());
    }
    let Some(oc) = &cert.optcert else {
        return (false, "claim names an optcert block that is absent".into());
    };
    if let Err(e) = oc.verify(model) {
        return (false, format!("the dual multipliers DO NOT verify: {e}"));
    }
    if oc.sense != model.sense() {
        return (false, "the certificate bounds the opposite sense".into());
    }
    // Densify both objectives and compare as functions.
    let mut cert_obj = vec![BigRational::zero(); model.num_cols()];
    for (c, a) in &oc.objective {
        match cert_obj.get_mut(*c as usize) {
            Some(slot) => *slot += a,
            None => {
                return (
                    false,
                    "the certificate's objective names a missing column".into(),
                )
            }
        }
    }
    for j in 0..model.num_cols() {
        let f = model.obj_coeff(Col(j as u32));
        let want = if f == 0.0 {
            BigRational::zero()
        } else {
            model.obj_coeff_exact_at(j as u32, f)
        };
        if cert_obj[j] != want {
            return (
                false,
                format!(
                    "the certificate bounds a DIFFERENT objective (column {j}: certificate {} vs \
                     model {})",
                    fmt_rat(&cert_obj[j]),
                    fmt_rat(&want)
                ),
            );
        }
    }
    let Some(claimed) = claimed_model_value else {
        return (
            true,
            format!(
                "the multipliers prove a valid bound of {} on the model's objective (no verdict \
                 value to meet)",
                fmt_rat(&oc.bound)
            ),
        );
    };
    // `OptimalityCertificate` deliberately excludes the model's constant
    // offset; the session folds it into the reported value. Add it back before
    // comparing, or the two numbers are in different units.
    let bound_with_offset = &oc.bound + model.obj_offset_exact();
    if &bound_with_offset != claimed {
        return (
            false,
            format!(
                "the dual bound is {} (offset included) but the verdict claims the optimum is \
                 {claimed}: this certificate does NOT prove that optimum",
                fmt_rat(&bound_with_offset)
            ),
        );
    }
    (
        true,
        "the positive multipliers combine, exactly, to the model's own objective minus the \
         claimed optimum: no feasible point can beat it"
            .into(),
    )
}

fn check_infeasible(cert: &Certificate, model: &Model, source: Option<&str>) -> (bool, String) {
    if source == Some("sat-relu-rup") {
        let Some(proof) = &cert.sat_relu_infeasibility else {
            return (
                false,
                "claim names a sat-relu-rup block that is absent".into(),
            );
        };
        return match crate::verify_sat_relu_infeasibility_certificate(model, proof, None) {
            Ok(()) => (
                true,
                "the exact SAT/ReLU CNF was rebuilt from the re-parsed source model, matched \
                 clause-for-clause, and its bounded RUP refutation independently replayed"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the SAT/ReLU resolution artifact DOES NOT verify: {error}"),
            ),
        };
    }
    if source == Some("parity-gf2") {
        let Some(proof) = &cert.parity_infeasibility else {
            return (
                false,
                "claim names a parity-gf2 block that is absent".into(),
            );
        };
        return match crate::verify_parity_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the named exact equality rows sum to even coefficients for every integral \
                 column and an odd right-hand side"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the GF(2) source-row contradiction DOES NOT verify: {error}"),
            ),
        };
    }
    if source == Some("network-design-infeasibility") {
        let Some(proof) = &cert.network_design_infeasibility else {
            return (
                false,
                "claim names a network-design-infeasibility block that is absent".into(),
            );
        };
        return match crate::network_design_route::verify_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the exact Hoffman projection was rebuilt from the re-parsed model, and its PB \
                 refutation independently replayed against that rebuilt master"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the network-design infeasibility artifact DOES NOT verify: {error}"),
            ),
        };
    }
    if source == Some("farkas") {
        let Some(fc) = &cert.farkas else {
            return (false, "claim names a Farkas block that is absent".into());
        };
        return match fc.verify(model) {
            Ok(()) => (
                true,
                format!(
                    "{} positive multipliers over model facts combine to `0 >= positive`: no \
                     point satisfies the model",
                    fc.multipliers.len()
                ),
            ),
            Err(e) => (
                false,
                format!("the Farkas combination DOES NOT verify: {e}"),
            ),
        };
    }
    if source == Some("tree") {
        let Some(t) = &cert.tree else {
            return (false, "claim names a tree block that is absent".into());
        };
        let leaves = count_leaves(&t.root);
        return match t.verify(model) {
            Ok(()) => (
                true,
                format!(
                    "the case-split tree covers the model's integer domain and all {leaves} \
                     leaves are exactly empty"
                ),
            ),
            Err(e) => (false, format!("the tree certificate DOES NOT verify: {e}")),
        };
    }
    if source == Some("single-row-dp") {
        let Some(proof) = &cert.single_row_dp else {
            return (
                false,
                "claim names a single-row-dp block that is absent".into(),
            );
        };
        return match crate::pb_route::verify_single_row_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the exact MILP-to-PB projection was rebuilt from the re-parsed model, and an \
                 independent scalar replay verified every reachability checkpoint and found no \
                 admissible sum"
                    .into(),
            ),
            Err(error) => (false, error),
        };
    }
    if source == Some("multi-row-bdd") {
        let Some(proof) = &cert.multi_row_bdd else {
            return (
                false,
                "claim names a multi-row-bdd block that is absent".into(),
            );
        };
        return match crate::pb_route::verify_multi_row_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the exact MILP-to-PB projection was rebuilt from the re-parsed model, and the \
                 independent verifier reconstructed every exact residual row state, checked every \
                 decision-DAG merge, and proved every leaf rejecting"
                    .into(),
            ),
            Err(error) => (false, error),
        };
    }
    if source == Some("open-domain-dp") {
        let Some(proof) = &cert.open_domain_dp else {
            return (
                false,
                "claim names an open-domain-dp block that is absent".into(),
            );
        };
        return if crate::open_domain_route::verify_single_row_infeasibility_certificate(
            model, proof,
        ) {
            (
                true,
                "the monotone open-domain projection was deterministically rebuilt from the \
                 re-parsed source model, and an independent scalar replay verified every \
                 residual reachability checkpoint"
                    .into(),
            )
        } else {
            (
                false,
                "the rebuilt open-domain residual DOES NOT accept the single-row proof".into(),
            )
        };
    }
    if source == Some("open-domain-bdd") {
        let Some(proof) = &cert.open_domain_bdd else {
            return (
                false,
                "claim names an open-domain-bdd block that is absent".into(),
            );
        };
        return if crate::open_domain_route::verify_multi_row_infeasibility_certificate(model, proof)
        {
            (
                true,
                "the monotone open-domain projection was deterministically rebuilt from the \
                 re-parsed source model, and the independent verifier reconstructed every \
                 residual state, checked every DAG merge, and proved every leaf rejecting"
                    .into(),
            )
        } else {
            (
                false,
                "the rebuilt open-domain residual DOES NOT accept the multi-row proof".into(),
            )
        };
    }
    if source == Some("hybrid-pb-lp") {
        let Some(proof) = &cert.hybrid_pb_lp else {
            return (
                false,
                "claim names a hybrid-pb-lp block that is absent".into(),
            );
        };
        return match verify_hybrid_pb_lp_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the binary master and every exact Benders cut were rebuilt from the re-parsed \
                 model, every Farkas/no-good license verified, and the final PB refutation \
                 independently replayed"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the hybrid PB/LP certificate DOES NOT verify: {error}"),
            ),
        };
    }
    if source == Some("open-domain-hybrid-pb-lp") {
        let Some(proof) = &cert.open_domain_hybrid_pb_lp else {
            return (
                false,
                "claim names an open-domain-hybrid-pb-lp block that is absent".into(),
            );
        };
        return if crate::open_domain_route::verify_hybrid_pb_lp_infeasibility_certificate(
            model, proof,
        ) {
            (
                true,
                "the monotone open-domain projection was rebuilt from the re-parsed source \
                 model, then every exact hybrid cut license and the final PB refutation \
                 independently replayed"
                    .into(),
            )
        } else {
            (
                false,
                "the rebuilt open-domain residual DOES NOT accept the hybrid PB/LP proof".into(),
            )
        };
    }
    if source == Some("open-domain-hybrid-integer-lift") {
        let Some(proof) = &cert.open_domain_hybrid_integer_lift else {
            return (
                false,
                "claim names an open-domain-hybrid-integer-lift block that is absent".into(),
            );
        };
        return if crate::open_domain_route::verify_hybrid_integer_lift_infeasibility_certificate(
            model, proof,
        ) {
            (
                true,
                "the monotone open-domain projection and bounded-integer radix transform were \
                 rebuilt from the re-parsed source model, then the nested hybrid proof \
                 independently replayed"
                    .into(),
            )
        } else {
            (
                false,
                "the rebuilt open-domain residual DOES NOT accept the integer-lifted hybrid proof"
                    .into(),
            )
        };
    }
    if source == Some("hybrid-integer-lift") {
        let Some(proof) = &cert.hybrid_integer_lift else {
            return (
                false,
                "claim names a hybrid-integer-lift block that is absent".into(),
            );
        };
        return match verify_hybrid_integer_lift_infeasibility_certificate(model, proof) {
            Ok(()) => (
                true,
                "the bounded general-integer radix transform was rebuilt and revalidated from \
                 the re-parsed source model, then its nested hybrid cut ledger and final PB \
                 refutation independently replayed"
                    .into(),
            ),
            Err(error) => (
                false,
                format!("the hybrid integer-lift certificate DOES NOT verify: {error}"),
            ),
        };
    }
    (
        false,
        "claim names an unsupported infeasibility block".into(),
    )
}

fn count_leaves(n: &TreeNode) -> usize {
    let mut stack = vec![n];
    let mut leaves = 0;
    while let Some(n) = stack.pop() {
        match n {
            TreeNode::Leaf { .. } => leaves += 1,
            TreeNode::Split { lo, hi, .. } => {
                stack.push(lo);
                stack.push(hi);
            }
        }
    }
    leaves
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_relu_rup_parser_enforces_caps_before_body_allocation() {
        let digest = "00".repeat(32);
        for oversized in [
            format!("vars={}", MAX_SAT_RELU_RUP_VARS + 1),
            format!("originals={}", MAX_SAT_RELU_RUP_ORIGINALS + 1),
            format!("steps={}", MAX_SAT_RELU_RUP_STEPS + 1),
            format!("derived_lits={}", MAX_SAT_RELU_RUP_LITERALS + 1),
            format!("hints={}", MAX_SAT_RELU_RUP_HINTS + 1),
        ] {
            let mut fields = vec![
                "vars=1".to_owned(),
                "originals=1".to_owned(),
                "steps=1".to_owned(),
                "derived_lits=0".to_owned(),
                "hints=1".to_owned(),
            ];
            let key = oversized.split('=').next().expect("field key");
            let position = fields
                .iter()
                .position(|field| field.starts_with(key))
                .expect("known field");
            fields[position] = oversized;
            let header = format!(
                "sat-relu-rup format=1 model=sha256:{digest} cnf=sha256:{digest} {} empty=2",
                fields.join(" ")
            );
            let lines = [header.as_str(), "step 2 lits=0 hints=1 1", "end"];
            assert!(
                parse_sat_relu_rup(&lines, 0).is_err(),
                "oversized header must decline before allocating its declared body"
            );
        }

        let header = format!(
            "sat-relu-rup format=1 model=sha256:{digest} cnf=sha256:{digest} \
             vars=1 originals=1 steps=1 derived_lits={} hints=0 empty=2",
            MAX_SAT_RELU_RUP_ITEMS_PER_STEP + 1
        );
        let step = format!(
            "step 2 lits={} hints=0",
            MAX_SAT_RELU_RUP_ITEMS_PER_STEP + 1
        );
        let lines = [header.as_str(), step.as_str(), "end"];
        assert!(
            parse_sat_relu_rup(&lines, 0).is_err(),
            "one oversized clause must fail before literal allocation"
        );
    }

    #[test]
    fn sat_relu_rup_emitter_refuses_noncanonical_internal_dags() {
        let variable = Variable::new(0);
        let malformed = SatReluInfeasibilityCertificate::from_wire_parts(
            1,
            [0; 32],
            [0; 32],
            1,
            2,
            vec![
                RupStep {
                    id: 3,
                    clause: vec![Literal::positive(variable)],
                    rup_hints: vec![1],
                },
                RupStep {
                    id: 4,
                    clause: Vec::new(),
                    // A forward/unknown hint is structurally noncanonical even
                    // before semantic RUP replay.
                    rup_hints: vec![5],
                },
            ],
            4,
        );
        assert!(sat_relu_rup_block(&malformed, MAX_SAT_RELU_RUP_BYTES).is_none());
    }

    fn tiny() -> (Model, String) {
        // minimize x + y, x + y >= 3, 0 <= x,y <= 10, both integer.
        let text = "NAME          TINY\n\
                    ROWS\n\
                    \x20N  COST\n\
                    \x20G  R1\n\
                    COLUMNS\n\
                    \x20   MARKER                 'MARKER'                 'INTORG'\n\
                    \x20   X         COST      1.0        R1        1.0\n\
                    \x20   Y         COST      1.0        R1        1.0\n\
                    \x20   MARKER                 'MARKER'                 'INTEND'\n\
                    RHS\n\
                    \x20   RHS       R1        3.0\n\
                    BOUNDS\n\
                    \x20UP BND       X         10.0\n\
                    \x20UP BND       Y         10.0\n\
                    ENDATA\n";
        let p = crate::read_mps(text).expect("parses");
        (p.model, text.to_string())
    }

    #[test]
    fn network_pattern_count_wire_round_trips_and_rejects_duplicate_variables() {
        let proof = crate::pattern_count_route::PatternCountOptimalityCertificate {
            blocks: vec![vec![1, 2], vec![3, 4], vec![5, 6]],
            pb_value: -17,
        };
        let value = BigRational::new(29.into(), 4.into());
        let certificate = crate::network_design_route::optimality_from_pattern_count(
            value.clone(),
            proof.clone(),
        );
        let wire = network_design_optimality_block(&certificate).expect("bounded wire block");
        let lines: Vec<&str> = wire.lines().collect();
        let (decoded, next) = parse_network_design_pattern_count(&lines, 0).expect("wire parses");
        assert_eq!(decoded, proof);
        assert_eq!(next, lines.len());
        assert!(wire.contains("value=29/4 frame=model kind=pattern-count"));

        let duplicate = [
            "network-design-optimality value=0 frame=model kind=pattern-count \
             pb_value=0 blocks=2 width=2",
            "block 1 2",
            "block 2 3",
            "end",
        ];
        assert!(parse_network_design_pattern_count(&duplicate, 0).is_err());

        let oversized_variable = format!("block {}", "1".repeat(2_000));
        let oversized = [
            "network-design-optimality value=0 frame=model kind=pattern-count \
             pb_value=0 blocks=2 width=1",
            oversized_variable.as_str(),
            "block 2",
            "end",
        ];
        assert!(parse_network_design_pattern_count(&oversized, 0).is_err());
    }

    #[test]
    fn emitted_pattern_count_optimum_parses_and_checks_end_to_end() {
        let model_text = "NAME          REPEATED_NETWORK\n\
                          ROWS\n\
                          \x20N  COST\n\
                          \x20E  DEF\n\
                          \x20E  BAL1\n\
                          \x20L  CAP1\n\
                          \x20E  BAL2\n\
                          \x20L  CAP2\n\
                          COLUMNS\n\
                          \x20   F1        BAL1      1          CAP1      1\n\
                          \x20   F2        BAL2      1          CAP2      1\n\
                          \x20   OBJ       COST      0.5        DEF       1\n\
                          \x20   MARK0000  'MARKER'              'INTORG'\n\
                          \x20   E1        DEF      -5          CAP1     -1\n\
                          \x20   E2        DEF      -5          CAP2     -1\n\
                          \x20   MARK0001  'MARKER'              'INTEND'\n\
                          RHS\n\
                          \x20   RHS       BAL1      1          BAL2      1\n\
                          BOUNDS\n\
                          \x20LO BND       F1        0\n\
                          \x20LO BND       F2        0\n\
                          \x20FR BND       OBJ\n\
                          \x20BV BND       E1\n\
                          \x20BV BND       E2\n\
                          ENDATA\n";
        let problem = crate::read_mps(model_text).expect("repeated network MPS parses");
        assert_eq!(problem.obj_scale, BigRational::from_integer(2.into()));
        let decision = crate::network_design_route::try_solve_certified(&problem.model, None)
            .expect("pattern-count route proves the repeated network optimum");
        let crate::network_design_route::CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision
        else {
            panic!("expected a certified optimum")
        };
        let pattern_proof = match crate::network_design_route::optimality_parts(&certificate).1 {
            crate::network_design_route::NetworkDesignOptimalityProofRef::PatternCount(proof) => {
                proof.clone()
            }
            crate::network_design_route::NetworkDesignOptimalityProofRef::StrictBetter(_) => {
                panic!("expected a pattern-count certificate")
            }
        };

        let scale = problem.obj_scale.clone();
        let ctx = EmitCtx {
            model: &problem.model,
            model_text,
            col_names: &problem.col_names,
            obj_scale: &scale,
            provenance: "pattern-count-e2e-test",
            replay_claims: &[],
            parity_infeasibility_certificate: None,
            sat_relu_infeasibility_certificate: None,
            network_design_infeasibility_certificate: None,
            network_design_optimality_certificate: Some(&certificate),
            block_angular_optimality_certificate: None,
            single_machine_scheduling_optimality_certificate: None,
            single_row_dp_infeasibility_certificate: None,
            multi_row_bdd_infeasibility_certificate: None,
            open_domain_single_row_dp_infeasibility_certificate: None,
            open_domain_multi_row_bdd_infeasibility_certificate: None,
            open_domain_hybrid_pb_lp_infeasibility_certificate: None,
            open_domain_hybrid_integer_lift_infeasibility_certificate: None,
            hybrid_pb_lp_infeasibility_certificate: None,
            hybrid_integer_lift_infeasibility_certificate: None,
            max_bytes: None,
        };
        let outcome = Outcome::Optimal {
            value: value.clone(),
            model_values: model_values.clone(),
            cert: None,
        };
        let wire = emit(&ctx, &outcome);
        assert!(wire.contains("kind=pattern-count"));
        assert!(wire.contains("verdict optimal value=5 frame=file"));
        assert!(wire.contains("network-design-optimality value=10 frame=model"));
        let parsed = parse(&wire).expect("public parser accepts the emitted certificate");
        assert!(parsed.network_design_optimality.is_some());
        let report = check(&wire, model_text);
        assert_eq!(report.status, CheckStatus::Verified, "{}", report.census());
        assert_eq!(
            report.claims_in(ClaimStanding::Verified),
            vec!["primal", "dual"]
        );

        let mut tampered_proof = pattern_proof;
        tampered_proof.pb_value = tampered_proof
            .pb_value
            .checked_add(1)
            .expect("small fixture value");
        let tampered = crate::network_design_route::optimality_from_pattern_count(
            value.clone(),
            tampered_proof,
        );
        let tampered_ctx = EmitCtx {
            network_design_optimality_certificate: Some(&tampered),
            ..ctx
        };
        let tampered_wire = emit(&tampered_ctx, &outcome);
        let tampered_report = check(&tampered_wire, model_text);
        assert_eq!(tampered_report.status, CheckStatus::Refuted);
        assert_eq!(
            tampered_report.claims_in(ClaimStanding::Refuted),
            vec!["dual"]
        );
    }

    /// THE SIZE-PREFERENCE LANE MEASURES THE BYTES THIS WRITER WRITES.
    ///
    /// `tree_cert::compact_leaf` ranks two exact-verified proposals for the
    /// same leaf by [`crate::tree_cert::wire_weight`] and ships the smaller,
    /// because `--emit-cert-max-bytes` drops an overflowing block and
    /// downgrades the claim. That decision is only as good as the estimate, so
    /// the estimate is held to THIS function's actual output — the one the
    /// consumer pays for — rather than to a formula nobody re-derives.
    #[test]
    fn the_leaf_weight_estimate_is_the_bytes_the_writer_emits() {
        let mults = vec![
            // A bare integer, a fraction, a negative numerator, a wide dyadic
            // of the kind the exactified float lane produces, and both fact
            // kinds at one- and multi-digit indices.
            Multiplier {
                fact: FactRef::RowBound {
                    row: Row(0),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            },
            Multiplier {
                fact: FactRef::RowBound {
                    row: Row(1234),
                    side: BoundSide::Upper,
                },
                coeff: BigRational::new(BigInt::from(75733), BigInt::from(1510)),
            },
            Multiplier {
                fact: FactRef::ColBound {
                    col: Col(7),
                    side: BoundSide::Lower,
                },
                coeff: BigRational::new(BigInt::from(-3), BigInt::from(4)),
            },
            Multiplier {
                fact: FactRef::ColBound {
                    col: Col(65_535),
                    side: BoundSide::Upper,
                },
                coeff: BigRational::new(
                    BigInt::from(2_514_297_896_833_393_i64),
                    BigInt::from(70_368_744_177_664_i64),
                ),
            },
        ];
        let cert = FarkasCertificate { multipliers: mults };
        let mut written = String::new();
        write_multipliers(&mut written, &cert.multipliers);
        assert_eq!(
            crate::tree_cert::wire_weight(&cert),
            written.len(),
            "the lane's size estimate must be the emitted byte count exactly, \
             or it ranks proposals in units the cap does not use; wrote {written:?}"
        );
    }

    #[test]
    fn rational_wire_form_round_trips_and_rejects_non_canonical() {
        let r = BigRational::new(BigInt::from(-3), BigInt::from(4));
        assert_eq!(fmt_rat(&r), "-3/4");
        assert_eq!(parse_rat("-3/4"), Some(r));
        assert_eq!(fmt_rat(&BigRational::from_integer(7.into())), "7");
        assert_eq!(parse_rat("7"), Some(BigRational::from_integer(7.into())));
        // Non-canonical forms are malformed, not silently normalised.
        assert_eq!(parse_rat("2/4"), None);
        assert_eq!(parse_rat("3/1"), None);
        assert_eq!(parse_rat("1/0"), None);
        assert_eq!(parse_rat("1/-2"), None);
    }

    #[test]
    fn bounded_rational_parser_preflights_decimal_size_and_checks_exact_bits() {
        let bit_cap = crate::block_angular_route::MAX_RATIONAL_BITS;
        let exact_decimal = BigRational::new(
            10_000_000_000_000_001_i64.into(),
            100_000_000_000_000_000_i64.into(),
        );
        assert_eq!(
            parse_rat_bounded("10000000000000001/100000000000000000", bit_cap),
            Ok(exact_decimal),
            "valid exact-decimal artifacts remain accepted"
        );

        let largest_power_within_cap = BigInt::one() << (bit_cap - 1);
        assert_eq!(
            parse_rat_bounded(&largest_power_within_cap.to_string(), bit_cap),
            Ok(BigRational::from_integer(largest_power_within_cap))
        );
        let first_power_above_cap = BigInt::one() << bit_cap;
        assert_eq!(
            parse_rat_bounded(&first_power_above_cap.to_string(), bit_cap),
            Err(BoundedRatParseError::BitLimit),
            "the exact bit check catches values at the decimal digit boundary"
        );

        let digit_cap = max_decimal_digits_for_bits(bit_cap).expect("small route cap");
        let allocation_attack = "9".repeat(digit_cap + 100_000);
        assert_eq!(
            parse_rat_bounded(&format!("{allocation_attack}/3"), bit_cap),
            Err(BoundedRatParseError::BitLimit),
            "an oversized numerator is rejected by length before BigInt parsing"
        );
        assert_eq!(
            parse_rat_bounded(&format!("1/{allocation_attack}"), bit_cap),
            Err(BoundedRatParseError::BitLimit),
            "an oversized denominator is rejected by length before BigInt parsing"
        );
    }

    #[test]
    fn canonical_digest_is_stable_and_shape_sensitive() {
        let (m, _) = tiny();
        assert_eq!(canonical_digest(&m), canonical_digest(&m.clone()));
        let canonical = canonical_model_v1(&m);
        let historical: [u8; 32] = Sha256::digest(canonical.as_bytes()).into();
        assert_eq!(
            canonical_digest_bytes(&m),
            historical,
            "streaming digest must preserve canonical-v1 bytes exactly"
        );
        assert_eq!(
            canonical_digest_bytes_bounded(&m, None, canonical.len()),
            Some(historical),
            "the exact byte cap is inclusive"
        );
        assert_eq!(
            canonical_digest_bytes_bounded(&m, None, canonical.len() - 1),
            None,
            "the streaming writer declines before exceeding its cap"
        );
        assert_eq!(
            canonical_digest_bytes_bounded(
                &m,
                Some(Instant::now() - std::time::Duration::from_millis(1)),
                usize::MAX,
            ),
            None,
            "an expired absolute deadline produces no partial digest"
        );
        let mut m2 = m.clone();
        m2.add_col(0.0, 1.0);
        assert_ne!(canonical_digest(&m), canonical_digest(&m2));

        let mut exact_offset = m.clone();
        let proxy_digest = canonical_digest(&exact_offset);
        exact_offset.record_inexact_obj_offset(BigRational::new(1.into(), 3.into()));
        assert_ne!(
            proxy_digest,
            canonical_digest(&exact_offset),
            "an exact-only offset mutation must change the frozen v1 digest"
        );
    }

    #[test]
    fn sat_relu_emission_reuses_its_model_bound_digest() {
        let (model, _) = tiny();
        let retained = [0x5au8; 32];
        let certificate = SatReluInfeasibilityCertificate::from_wire_parts(
            1,
            retained,
            [0u8; 32],
            0,
            0,
            Vec::new(),
            0,
        );
        let infeasible = Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        };
        assert_eq!(
            emitted_model_canon_digest(&model, &infeasible, Some(&certificate)),
            digest_hex(&retained),
            "the model-bound certificate already paid for this exact digest"
        );

        let optimal = Outcome::Optimal {
            value: BigRational::zero(),
            model_values: Vec::new(),
            cert: None,
        };
        assert_eq!(
            emitted_model_canon_digest(&model, &optimal, Some(&certificate)),
            canonical_digest(&model),
            "an unrelated verdict must never reuse stale SAT/ReLU evidence"
        );
    }

    #[test]
    fn block_angular_wire_round_trips_and_is_bounded() {
        let certificate = crate::block_angular_route::certificate_from_parts(
            BigRational::from_integer(17.into()),
            vec![
                (3, BigRational::new(1.into(), 2.into())),
                (9, BigRational::from_integer(2.into())),
            ],
            vec![
                crate::block_angular_route::source_pattern(vec![4, 1], vec![0, 3]),
                crate::block_angular_route::certified_initial_pattern(2),
            ],
        );
        let block = block_angular_optimality_block(&certificate);
        let lines: Vec<&str> = block.lines().collect();
        let (decoded, next) = parse_block_angular_optimality(&lines, 0).expect("wire block parses");
        assert_eq!(decoded, certificate);
        assert_eq!(next, lines.len());

        let oversized = "block-angular-optimality value=0 frame=model masters=65 blocks=0\nend";
        let lines: Vec<&str> = oversized.lines().collect();
        assert!(parse_block_angular_optimality(&lines, 0).is_err());

        let malformed = "block-angular-optimality value=0 frame=model masters=0 blocks=1\n\
                         source width=2 1 2 exits 0\nend";
        let lines: Vec<&str> = malformed.lines().collect();
        assert!(parse_block_angular_optimality(&lines, 0).is_err());

        let bit_cap = crate::block_angular_route::MAX_RATIONAL_BITS;
        let digit_cap = max_decimal_digits_for_bits(bit_cap).expect("small route cap");
        let allocation_attack = "9".repeat(digit_cap + 100_000);
        let oversized_value = format!(
            "block-angular-optimality value={allocation_attack} frame=model masters=0 blocks=0\n\
             end"
        );
        let lines: Vec<&str> = oversized_value.lines().collect();
        assert!(matches!(
            parse_block_angular_optimality(&lines, 0),
            Err(CertIoError::RationalBitLimit {
                line: 1,
                field,
                max_bits,
            }) if field == "block-angular optimum value" && max_bits == bit_cap
        ));

        let oversized_denominator = format!(
            "block-angular-optimality value=0 frame=model masters=1 blocks=0\n\
             master 0 1/{allocation_attack}\n\
             end"
        );
        let lines: Vec<&str> = oversized_denominator.lines().collect();
        assert!(matches!(
            parse_block_angular_optimality(&lines, 0),
            Err(CertIoError::RationalBitLimit {
                line: 2,
                field,
                max_bits,
            }) if field == "block-angular master multiplier" && max_bits == bit_cap
        ));
    }

    #[test]
    fn exact_reduction_replay_ids_back_only_the_claim_they_proved() {
        fn replay(claim: &str) -> ReplayClaim {
            ReplayClaim {
                claim: claim.to_owned(),
                device: "milp-to-pb-reduction".to_owned(),
                method: "exact-rational-boolean-projection+native-pb-cdcl".to_owned(),
                arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                nodes_visited: None,
                node_budget: 0,
                outcome: "exhausted".to_owned(),
                nondeterminism: Vec::new(),
                reproduce: "ay-milp solve <model> --require none".to_owned(),
                tcb: "pb route".to_owned(),
            }
        }

        let mut model = Model::new();
        model.set_objective_offset(0.0);
        let scale = BigRational::one();
        let names = Vec::new();

        let optimal_replay = vec![replay("pb-projection-optimal")];
        let optimal_ctx = EmitCtx {
            model: &model,
            model_text: "pb replay fixture",
            col_names: &names,
            obj_scale: &scale,
            provenance: "test",
            replay_claims: &optimal_replay,
            parity_infeasibility_certificate: None,
            sat_relu_infeasibility_certificate: None,
            network_design_infeasibility_certificate: None,
            network_design_optimality_certificate: None,
            block_angular_optimality_certificate: None,
            single_machine_scheduling_optimality_certificate: None,
            single_row_dp_infeasibility_certificate: None,
            multi_row_bdd_infeasibility_certificate: None,
            open_domain_single_row_dp_infeasibility_certificate: None,
            open_domain_multi_row_bdd_infeasibility_certificate: None,
            open_domain_hybrid_pb_lp_infeasibility_certificate: None,
            open_domain_hybrid_integer_lift_infeasibility_certificate: None,
            hybrid_pb_lp_infeasibility_certificate: None,
            hybrid_integer_lift_infeasibility_certificate: None,
            max_bytes: None,
        };
        let optimal = emit(
            &optimal_ctx,
            &Outcome::Optimal {
                value: BigRational::zero(),
                model_values: Vec::new(),
                cert: None,
            },
        );
        assert!(optimal.contains("evidence dual REPLAY pb-projection-optimal"));
        assert!(!optimal.contains("evidence infeasible REPLAY"));

        let infeasible_replay = vec![replay("pb-projection-infeasible")];
        let infeasible_ctx = EmitCtx {
            replay_claims: &infeasible_replay,
            ..optimal_ctx
        };
        let infeasible = emit(
            &infeasible_ctx,
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
        );
        assert!(infeasible.contains("evidence infeasible REPLAY pb-projection-infeasible"));
        assert!(!infeasible.contains("evidence dual REPLAY"));

        let hybrid_optimal_replay = vec![replay("hybrid-pb-lp-optimal")];
        let hybrid_optimal_ctx = EmitCtx {
            replay_claims: &hybrid_optimal_replay,
            ..optimal_ctx
        };
        let hybrid_optimal = emit(
            &hybrid_optimal_ctx,
            &Outcome::Optimal {
                value: BigRational::zero(),
                model_values: Vec::new(),
                cert: None,
            },
        );
        assert!(hybrid_optimal.contains("evidence dual REPLAY hybrid-pb-lp-optimal"));
        assert!(!hybrid_optimal.contains("evidence infeasible REPLAY"));

        let hybrid_infeasible_replay = vec![replay("hybrid-pb-lp-infeasible")];
        let hybrid_infeasible_ctx = EmitCtx {
            replay_claims: &hybrid_infeasible_replay,
            ..optimal_ctx
        };
        let hybrid_infeasible = emit(
            &hybrid_infeasible_ctx,
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
        );
        assert!(hybrid_infeasible.contains("evidence infeasible REPLAY hybrid-pb-lp-infeasible"));
        assert!(!hybrid_infeasible.contains("evidence dual REPLAY"));

        for claim in [
            "pb-portfolio-projection-optimal",
            "network-design-projection-optimal",
            "open-domain-cap-optimal",
        ] {
            let claims = vec![replay(claim)];
            let ctx = EmitCtx {
                replay_claims: &claims,
                ..optimal_ctx
            };
            let emitted = emit(
                &ctx,
                &Outcome::Optimal {
                    value: BigRational::zero(),
                    model_values: Vec::new(),
                    cert: None,
                },
            );
            assert!(emitted.contains(&format!("evidence dual REPLAY {claim}")));
            assert!(!emitted.contains("evidence infeasible REPLAY"));
        }

        for claim in [
            "pb-portfolio-projection-infeasible",
            "network-design-projection-infeasible",
            "open-domain-projection-infeasible",
        ] {
            let claims = vec![replay(claim)];
            let ctx = EmitCtx {
                replay_claims: &claims,
                ..optimal_ctx
            };
            let emitted = emit(
                &ctx,
                &Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                },
            );
            assert!(emitted.contains(&format!("evidence infeasible REPLAY {claim}")));
            assert!(!emitted.contains("evidence dual REPLAY"));
        }
    }
}
