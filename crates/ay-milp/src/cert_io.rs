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
//! that is present: `Some(FarkasCertificate)` is `SUCCINCT` by construction,
//! only a [`ReplayClaim`] can produce `REPLAY`, and a bare
//! `Outcome::Infeasible { cert: None, tree_cert: None }` has no path to
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

use std::fmt::Write as _;

use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use sha2::{Digest, Sha256};

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate};
use crate::model::{exact, Col, ColKind, Model, Row, Sense};
use crate::outcome::{Outcome, UnknownReason};
use crate::tree_cert::{MilpInfeasibilityCertificate, TreeNode};

/// The format version this build emits and the only one it reads.
pub const AYC_VERSION: u32 = 1;

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
#[must_use]
pub fn canonical_model_v1(model: &Model) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "ayc-canon-v1");
    let _ = writeln!(s, "sense {}", sense_token(model.sense()));
    let _ = writeln!(s, "objective {}", u8::from(model.has_objective()));
    let _ = writeln!(s, "offset {}", fmt_rat(&model.obj_offset_exact()));
    let _ = writeln!(s, "cols {}", model.num_cols());
    for j in 0..model.num_cols() {
        let c = Col(j as u32);
        let (lb, ub) = model.col_bounds(c);
        let kind = match model.col_kind(c) {
            ColKind::Binary => "b",
            ColKind::Integer => "i",
            ColKind::Continuous => "c",
        };
        let objf = model.obj_coeff(c);
        // `objective_value_at` skips a stored-zero `f64` objective coefficient,
        // and the side-store is only ever populated for columns whose `f64`
        // objective is nonzero — so this reproduces the exact objective the
        // engine itself evaluates, not a different one.
        let obj = if objf == 0.0 {
            BigRational::zero()
        } else {
            model.obj_coeff_exact_at(j as u32, objf)
        };
        let _ = writeln!(
            s,
            "col {j} {kind} {} {} {}",
            fmt_bound(exact(lb).as_ref(), false),
            fmt_bound(exact(ub).as_ref(), true),
            fmt_rat(&obj)
        );
    }
    let _ = writeln!(s, "rows {}", model.num_rows());
    for i in 0..model.num_rows() {
        let (coeffs, lb, ub) = model.row(Row(i as u32));
        let _ = write!(
            s,
            "row {i} {} {} {}",
            fmt_bound(model.row_lb_exact(i, lb).as_ref(), false),
            fmt_bound(model.row_ub_exact(i, ub).as_ref(), true),
            coeffs.len()
        );
        // `Model::row` guarantees sorted, duplicate-free, zero-free.
        for &(c, a) in coeffs {
            let _ = write!(s, " {c} {}", fmt_rat(&model.row_coeff_exact(i, c, a)));
        }
        s.push('\n');
    }
    s
}

/// The `model canon v1` digest.
#[must_use]
pub fn canonical_digest(model: &Model) -> String {
    sha256_hex(canonical_model_v1(model).as_bytes())
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
    let mut admit = |blocks: &mut String, body: String, what: &str| -> bool {
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
            if admit(&mut blocks, body, "witness") {
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
                    if admit(&mut blocks, body, "optcert") {
                        claims.push(EmittedClaim {
                            name: "dual",
                            // A certificate that bounds the identically-zero
                            // objective by zero VERIFIES, and proves nothing.
                            // It is emitted (losslessly) but never counted.
                            kind: if trivial {
                                EvidenceKind::None
                            } else {
                                EvidenceKind::Succinct
                            },
                            source: Some(
                                if trivial {
                                    "trivial-optcert"
                                } else {
                                    "optcert"
                                }
                                .into(),
                            ),
                        });
                    } else {
                        claims.push(EmittedClaim {
                            name: "dual",
                            kind: EvidenceKind::None,
                            source: Some("truncated".into()),
                        });
                    }
                }
                None => claims.push(dual_claim_from_replay(ctx, "objective-face-empty")),
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
            if admit(&mut blocks, body, "witness") {
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
                if admit(&mut blocks, body, "farkas") {
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
                if admit(&mut blocks, body, "tree") {
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
        let _ = admit(&mut blocks, body, "replay");
    }

    let mut out = String::new();
    let _ = writeln!(out, "%AYC {AYC_VERSION}");
    let _ = writeln!(
        out,
        "model file sha256:{} bytes={} form=text",
        sha256_hex(ctx.model_text.as_bytes()),
        ctx.model_text.len()
    );
    let _ = writeln!(out, "model canon v1 sha256:{}", canonical_digest(ctx.model));
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
fn dual_claim_from_replay(ctx: &EmitCtx<'_>, want: &str) -> EmittedClaim {
    if let Some(rc) = ctx.replay_claims.iter().find(|r| r.claim == want) {
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
    if let Some(rc) = ctx
        .replay_claims
        .iter()
        .find(|r| r.claim == "feasibility-face-empty" || r.claim == "coset-inconsistent")
    {
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

/// A certificate bounding the identically-zero objective by zero verifies and
/// says nothing. The lattice device ships one on a pure feasibility model.
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

/// The four source tokens that may back a `SUCCINCT` claim. Anything else on a
/// `SUCCINCT` record is a parse error.
const SUCCINCT_SOURCES: &[&str] = &["witness", "farkas", "optcert", "tree"];
/// Source tokens a `NONE` record may carry, explaining WHY it is none.
const NONE_SOURCES: &[&str] = &["trivial-optcert", "truncated"];

/// Parse a `.ayc` certificate.
///
/// # Errors
/// Returns [`CertIoError`] on a malformed record, an unknown version, or a
/// mislabelled evidence record.
#[allow(clippy::too_many_lines)]
pub fn parse(text: &str) -> Result<Certificate, CertIoError> {
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
    /// At least one claim is REPLAY or NONE. Exit 10.
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
    // Severity order: Mismatch > Refuted > Unverified > Verified. The status
    // only ever gets WORSE, so no later check can wash out an earlier failure.
    fn demote(s: CheckStatus, status: &mut CheckStatus) {
        let rank = |s: CheckStatus| match s {
            CheckStatus::Verified => 0u8,
            CheckStatus::Unverified => 1,
            CheckStatus::Refuted => 2,
            CheckStatus::Mismatch => 3,
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
            ("dual", EvidenceKind::Succinct) => {
                check_dual(&cert, model, claimed_model_value.as_ref())
            }
            ("infeasible", EvidenceKind::Succinct) => check_infeasible(&cert, model),
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
                        " (an optimality certificate is attached but bounds the identically-zero \
                         objective by zero: it verifies and proves nothing)"
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
) -> (bool, String) {
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

fn check_infeasible(cert: &Certificate, model: &Model) -> (bool, String) {
    if let Some(fc) = &cert.farkas {
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
    if let Some(t) = &cert.tree {
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
    (false, "claim names a block that is absent".into())
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
    fn canonical_digest_is_stable_and_shape_sensitive() {
        let (m, _) = tiny();
        assert_eq!(canonical_digest(&m), canonical_digest(&m.clone()));
        let mut m2 = m.clone();
        m2.add_col(0.0, 1.0);
        assert_ne!(canonical_digest(&m), canonical_digest(&m2));
    }
}
