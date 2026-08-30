// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ROOT-ONLY dual bound — what a declined whole-tree optimality proof can
//! still export, and the exact statement of what it does NOT prove.
//!
//! [`crate::opt_cert::MilpOptimalityCertificate`] is the complete dual half of
//! an `Optimal`: a split tree every leaf of which is priced at or beyond the
//! claimed optimum. When its certifying descent declines — and on the
//! 50-instance census behind
//! the development design notes it declines on 30 of
//! the 44 `OPTIMAL` verdicts, almost always at the work cap — the `.ayc`
//! shipped `evidence dual NONE`: the primal witness was checkable and NOTHING
//! WHATSOEVER backed "and nothing beats it".
//!
//! This module fills the space between "proved" and "nothing" with the one
//! object that is always available and always cheap: the model's own ROOT LP
//! relaxation, with the relaxation's dual solution kept as exact evidence.
//!
//! # What it proves, stated so it cannot be over-read
//!
//! A verified root dual bound `B` proves
//!
//! > no feasible point of the model has objective better than `B`
//!
//! over the model's ENTIRE feasible set — the multipliers are priced at the
//! model's own row and column bounds, with no branch, no cut and no presolve.
//! Paired with the `.ayc` `primal` claim, which exhibits a feasible point
//! attaining `z*`, the pair proves
//!
//! > the optimum lies in `[B, z*]` (Minimize) / `[z*, B]` (Maximize)
//!
//! and NOT that `z*` is the optimum. The residual `|z* − B|` is exactly the
//! part that remains on trust, and it is written into the artifact as `gap` so
//! that the size of what is unproved is a FIELD OF THE CERTIFICATE rather than
//! something a reader has to work out.
//!
//! # Why this cannot be mistaken for the complete proof
//!
//! Three separate mechanisms, because one would be a convention and three are
//! a design:
//!
//! 1. **A name that neither IS nor EXTENDS `dual`.** The bound rides as
//!    `objbound`. `evidence dual NONE` stays on the file exactly as before, so
//!    the claim "nothing beats z*" is still reported unbacked — and because
//!    `objbound` does not have `dual` as a prefix, the artifact's `evidence`
//!    record, the checker's `claim` line and the `CLAIMS` census cannot be
//!    grepped for the dual half and answered with this one. It shipped once as
//!    `dualbound` and could be; `cert_io`'s `CLAIM_NAMES` carries that
//!    measurement and the guard that now refuses any shadowing name.
//! 2. **The aggregate cannot move.** `dual` is still `NONE`, so the checker's
//!    status stays `PARTIAL` (exit 11). No flag turns a root-bounded optimum
//!    into exit 0.
//! 3. **The residual is a CHECKED field.** `gap` is re-derived by the checker
//!    from the block's `bound` and the VERDICT line's value and must agree
//!    exactly; a certificate that understates its own residual is REFUTED, not
//!    quietly believed.
//!
//! # Relation to the whole-tree lane
//!
//! Purely additive and strictly subordinate. The emitter offers `rootdual`
//! only where the dual claim would otherwise have been `NONE`, so no verdict
//! that already ships succinct dual evidence has its evidence changed, and a
//! root bound never displaces a tree.
//!
//! # Two lanes, and why only the cheap one is on by default
//!
//! Weak duality holds for ANY dual vector, so a bound can be built from a
//! float LP's duals just as soundly as from an exact one — the exactified
//! multipliers are re-priced against the model either way and a float that
//! lies produces no certificate rather than a wrong one. Measured on this
//! machine over 16 corpus instances (`root_dual_probe`), the EXACT rim needs
//! 0.005 s on `markshare1` but 14.3 s on `rout` and 15.6 s on `fiber`, and
//! runs out of clock entirely on `22433`, `23588`, `qnet1` and `qiu`. The
//! float lane is bounded by an iteration count instead. So the float lane is
//! unconditional and the rim is OPT-IN; when it is opted into, BOTH run and the
//! stronger verified bound wins.

use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::{CertificateError, Multiplier, OptimalityCertificate};
use crate::exact::{Budget, ExactLp, LpOptimum};
use crate::model::{Col, Model, Row, Sense};
use crate::opt_cert::{
    bound_multipliers_from_duals, exact_box, float_objective, grid_ladder,
    minimize_frame_objective, minimize_frame_objective_dense, DEFAULT_DUAL_GRID_BITS,
};
use crate::simplex::{FloatLp, SimplexStatus};

/// Resource bounds for [`derive_root_dual_bound`].
///
/// One LP solve per lane, so the bounds that matter are ITERATION caps —
/// deterministic, a function of the model alone. [`Self::deadline`] is the
/// wall-clock safety net and is the only way this derivation's OUTPUT can
/// depend on machine load; [`RootDualDecline::Undecided`] is where that shows
/// up, and it is reported under its own name for exactly that reason.
#[derive(Debug, Clone)]
pub struct RootDualBudget {
    /// Maximum exact-rim simplex iterations, over both phases. `0` switches
    /// the exact lane off entirely, leaving the float lane alone.
    pub rim_iters: u64,
    /// Absolute wall-clock SAFETY NET. Not the primary bound.
    pub deadline: Option<Instant>,
    /// Snap the float lane's row duals to a multiple of `2^-dual_grid_bits`
    /// before exactifying. PURE ADVICE, exactly as in
    /// [`crate::opt_cert::OptimalityTreeBudget`]: a coarser dual is still
    /// dual-feasible and still yields a VALID bound, merely a possibly weaker
    /// one, and the bound the multipliers actually prove is re-derived from
    /// them either way.
    ///
    /// # In THIS lane it buys coverage, not bytes
    ///
    /// In the tree lane the grid is a size dial, because a tree writes one
    /// multiplier list per leaf and the ladder stops at the first rung that
    /// closes. Here there is exactly ONE block and every rung is priced, with
    /// the STRONGEST verified candidate winning — so the lossless rung, which
    /// is always at least as tight, normally wins and the grid saves nothing.
    /// What the coarse rung still does is RESCUE models the lossless one
    /// cannot certify at all: `bound_multipliers_from_duals` declines outright
    /// when a nonzero reduced cost lands on a column with no finite bound on
    /// the side that would price it, and snapping a near-zero dual to exactly
    /// zero removes that residual instead of failing on it.
    pub dual_grid_bits: Option<u32>,
}

impl RootDualBudget {
    /// The SHIPPED default: the float lane alone, the shipped dual grid, and no
    /// deadline.
    ///
    /// `rim_iters` is ZERO here on purpose. With the rim off, every input to
    /// this derivation is the model, so the certificate a run emits is a pure
    /// function of the model — no clock, no load, no machine. Turning the rim on
    /// buys coverage and gives that property up, so it is a decision a caller
    /// makes rather than one this constructor makes for them.
    ///
    /// `model` is taken (and currently unused) because every other budget in
    /// this crate scales its caps by the model, and a constructor that silently
    /// stopped doing so would be the surprise.
    #[must_use]
    pub fn new(model: &Model) -> Self {
        let _ = model;
        Self {
            rim_iters: 0,
            deadline: None,
            dual_grid_bits: DEFAULT_DUAL_GRID_BITS,
        }
    }

    /// The exact rim's own default iteration cap for `model` — what
    /// [`Self::with_rim_iters`] wants when a caller opts in without a number of
    /// their own.
    #[must_use]
    pub fn default_rim_iters(model: &Model) -> u64 {
        Budget::default_iters(model.num_cols() + model.num_rows())
    }

    /// This budget with an absolute wall-clock safety net.
    #[must_use]
    pub fn with_deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// This budget with an explicit exact-rim iteration cap. `0` leaves only
    /// the float lane.
    #[must_use]
    pub fn with_rim_iters(mut self, iters: u64) -> Self {
        self.rim_iters = iters;
        self
    }

    /// This budget with an explicit dual grid. `None` restores the lossless
    /// `f64 -> BigRational` conversion.
    #[must_use]
    pub fn with_dual_grid_bits(mut self, bits: Option<u32>) -> Self {
        self.dual_grid_bits = bits;
        self
    }

    fn expired(&self) -> bool {
        self.deadline.is_some_and(|limit| Instant::now() >= limit)
    }
}

/// Which lane produced a root dual bound. Diagnostics only: both lanes end at
/// the same [`OptimalityCertificate::verify`] gate, so this says what a run
/// COST, never how much it is worth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootDualLane {
    /// The float relaxation's duals, exactified and re-priced.
    Float,
    /// The exact rim's own dual solution.
    ExactRim,
}

impl RootDualLane {
    /// The short tag used in the CLI's `certificate:` note.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            Self::Float => "float",
            Self::ExactRim => "exact-rim",
        }
    }
}

/// WHY a root dual bound derivation produced nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootDualDecline {
    /// Neither lane could be constructed over this model.
    LpUnavailable,
    /// The ROOT RELAXATION is infeasible, so the model is too. STRUCTURAL, and
    /// a red flag on any `Optimal` verdict being certified: nothing that
    /// verifies can be derived here and the verdict itself is in question.
    RootInfeasible,
    /// The root relaxation runs to −∞. STRUCTURAL: there is no finite dual
    /// bound to export.
    RootUnbounded,
    /// An LP solved but produced no evidence and the exact rim was not run to
    /// its end — because it was off (the shipped default), because its
    /// iteration cap ran out, or because the safety net did. BUDGET: raising
    /// `rim_iters` is a change that really can produce a bound, and on this
    /// project's own corpus it produces four.
    Undecided,
    /// The EXACT rim reached an optimum and its own duals still could not be
    /// priced into evidence. STRUCTURAL for this model: the usual cause is a
    /// nonzero reduced cost on a column with no finite bound on the side that
    /// would price it, which no budget can fix. Never raised on a float-only
    /// run — see the comment at its single construction site.
    NoVerifiedBound,
}

impl RootDualDecline {
    /// The short tag used in the CLI's `certificate:` note.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            Self::LpUnavailable => "lp-unavailable",
            Self::RootInfeasible => "root-infeasible",
            Self::RootUnbounded => "root-unbounded",
            Self::Undecided => "undecided",
            Self::NoVerifiedBound => "no-verified-bound",
        }
    }

    /// `true` when a larger budget could plausibly change the answer. The
    /// STRUCTURAL reasons return `false`: spending more time on them is pure
    /// waste, which is the whole point of separating them.
    #[must_use]
    pub fn is_budget(self) -> bool {
        matches!(self, Self::Undecided)
    }
}

/// What a root dual bound attempt cost and, when it produced nothing, why.
#[derive(Debug, Clone, Default)]
pub struct RootDualReport {
    /// The decline reason. `None` on success.
    pub decline: Option<RootDualDecline>,
    /// The lane that produced the certificate. `None` on decline.
    pub lane: Option<RootDualLane>,
    /// Exact-rim simplex iterations spent, over both phases.
    pub rim_iters: u64,
}

/// Derive an exact, independently checkable LOWER bound (Minimize) / UPPER
/// bound (Maximize) on `model`'s optimum from its root LP relaxation.
///
/// # This is a BOUND, never an optimum
///
/// `Some(cert)` means: `cert.verify(model)` succeeds, and it establishes
/// `objective·x >= cert.bound` (Minimize) / `<= cert.bound` (Maximize) for
/// every feasible `x`, with `bound` excluding the model's objective offset in
/// the same convention as [`OptimalityCertificate`]. It says nothing about
/// whether any particular value is ATTAINED; that is the primal witness's job,
/// and the two together bracket the optimum without closing it.
///
/// # Derive, never read
///
/// Neither lane's own claimed objective value is used. The bound is recomputed
/// from the multipliers by `OptimalityCertificate::bound_leaf_value`, priced at
/// a box the CALLER's model supplies, and the assembled certificate is then
/// gated on [`OptimalityCertificate::verify`] — the public verifier a consumer
/// would run. An LP that returned a wrong dual produces `None`, never a bad
/// bound.
#[must_use]
pub fn derive_root_dual_bound(
    model: &Model,
    budget: &RootDualBudget,
) -> (Option<OptimalityCertificate>, RootDualReport) {
    let mut report = RootDualReport::default();
    let mut structural: Option<RootDualDecline> = None;
    let mut rim_solved_but_unusable = false;
    let mut any_lp_solved = false;
    let mut candidates: Vec<(RootDualLane, Vec<Multiplier>)> = Vec::new();

    // THE CHEAP LANE ALWAYS. Its cost is an iteration count on `f64`
    // arithmetic, which is what makes it affordable to attempt
    // unconditionally.
    match float_root_multipliers(model, budget) {
        LaneOutcome::Multipliers(proposals) => {
            any_lp_solved = true;
            candidates.extend(proposals.into_iter().map(|m| (RootDualLane::Float, m)));
        }
        // Unreachable by construction — the float lane returns advice, never a
        // fact — but matched rather than ignored so a future edit that starts
        // returning one is a compile-time decision instead of a silent upgrade.
        LaneOutcome::Structural(reason) => structural = Some(reason),
        LaneOutcome::NoEvidence => any_lp_solved = true,
        LaneOutcome::Unavailable => {}
    }

    // THE EXACT RIM, WHENEVER IT IS ENABLED — not only when the float lane came
    // back empty.
    //
    // A fallback-only rim can rescue a model with no float bound but can never
    // IMPROVE a weak one, and the weak ones are where the tightness actually
    // goes: measured on this corpus the float lane exports `-65.6` for `blend2`
    // where the exact root bound is `6.92`, and a relative residual of 35 for
    // `qnet1` where the true root gap is 0.11. Both are cases where the float
    // lane "succeeded", so a fallback would never have run. Since the rim is
    // OFF by default, a caller who turns it on has already decided to pay for
    // it, and running it unconditionally is what makes `--root-dual-rim` mean
    // "also try the exact lane" rather than "try it only where I cannot tell
    // whether it would have helped".
    if budget.rim_iters > 0 && !budget.expired() {
        match rim_root_multipliers(model, budget, &mut report) {
            LaneOutcome::Multipliers(proposals) => {
                any_lp_solved = true;
                // THE ONLY PLACE `NoVerifiedBound` MAY COME FROM. An exact LP
                // reached an optimum and its own duals still could not be
                // priced into evidence, which is a fact about the model's bound
                // structure rather than a budget. Saying the same thing after
                // only the FLOAT lane ran would be wrong: the four corpus models
                // the rim rescues (`b-ball`, `dcmulti`, `gen`,
                // `neos-3610040-iskar`) are exactly the ones whose float duals
                // do not price.
                rim_solved_but_unusable = true;
                candidates.extend(proposals.into_iter().map(|m| (RootDualLane::ExactRim, m)));
            }
            LaneOutcome::Structural(reason) => {
                any_lp_solved = true;
                structural = Some(reason);
            }
            LaneOutcome::NoEvidence => any_lp_solved = true,
            LaneOutcome::Unavailable => {}
        }
    }

    if let Some((lane, certificate)) = best_certificate(model, candidates) {
        report.lane = Some(lane);
        return (Some(certificate), report);
    }

    // ATTRIBUTION, and the ordering is the whole point.
    //
    // * A STRUCTURAL verdict — which only the exact rim can produce — tells a
    //   caller never to spend anything here again, so it outranks everything.
    // * `no-verified-bound` is the exact rim's own dead end, above.
    // * `undecided` is the only tag that says "spend more", and it is where a
    //   float-only run lands: raising `--root-dual-rim` is a budget change that
    //   really can change the answer.
    // * `lp-unavailable` means no lane could even be CONSTRUCTED over this
    //   model, which no budget touches either.
    report.decline = Some(structural.unwrap_or({
        if rim_solved_but_unusable {
            RootDualDecline::NoVerifiedBound
        } else if any_lp_solved {
            RootDualDecline::Undecided
        } else {
            RootDualDecline::LpUnavailable
        }
    }));
    (None, report)
}

/// What one lane made of the root box.
enum LaneOutcome {
    /// Multiplier sets to be priced and verified, best-first is NOT assumed.
    Multipliers(Vec<Vec<Multiplier>>),
    /// A fact about the model that no budget changes. Only the EXACT rim may
    /// return this: a float LP's "infeasible" or "unbounded" is `f64` advice,
    /// and reporting advice as a structural fact would tell a caller never to
    /// spend anything on a model that an exact solve might well certify.
    Structural(RootDualDecline),
    /// The lane RAN and produced nothing usable. Distinct from
    /// [`Self::Unavailable`] because the two mean opposite things to a caller
    /// deciding whether to spend more.
    NoEvidence,
    /// The lane could not be CONSTRUCTED over this model at all.
    Unavailable,
}

/// The float relaxation's duals, exactified at every rung of the grid ladder
/// and in both sign conventions.
///
/// The sign convention is deliberately not relied upon — both orientations are
/// offered and only a verified one survives — exactly as
/// [`crate::opt_cert`]'s own float leaf does.
fn float_root_multipliers(model: &Model, budget: &RootDualBudget) -> LaneOutcome {
    let Some(lp) = FloatLp::from_model(model, &float_objective(model), Sense::Minimize) else {
        return LaneOutcome::Unavailable;
    };
    let columns = model.num_cols();
    let rows = model.num_rows();
    let mut lower = Vec::with_capacity(columns + rows);
    let mut upper = Vec::with_capacity(columns + rows);
    for column in 0..columns {
        let (low, high) = model.col_bounds(Col(column as u32));
        lower.push(low);
        upper.push(high);
    }
    for row in 0..rows {
        let (_, low, high) = model.row(Row(row as u32));
        lower.push(low);
        upper.push(high);
    }
    let candidate = lp.solve_bounded(&lower, &upper, None, budget.deadline);
    match candidate.status {
        // ADVICE, NOT A FACT. A float LP calling the root empty or unbounded is
        // an `f64` opinion; the exact rim behind this lane is what may state it
        // as a fact, and until it has run the honest answer is "this lane has
        // nothing", not "never look here again".
        SimplexStatus::PrimalInfeasible | SimplexStatus::Unbounded => LaneOutcome::NoEvidence,
        SimplexStatus::Optimal => {
            if candidate.duals.len() != rows {
                return LaneOutcome::NoEvidence;
            }
            let objective = minimize_frame_objective_dense(model);
            let (low, high) = exact_box(model);
            let mut out = Vec::new();
            for bits in grid_ladder(budget.dual_grid_bits) {
                for sign in [1.0f64, -1.0] {
                    if let Some(multipliers) = bound_multipliers_from_duals(
                        model,
                        &objective,
                        &candidate.duals,
                        sign,
                        &low,
                        &high,
                        bits,
                    ) {
                        out.push(multipliers);
                    }
                }
            }
            LaneOutcome::Multipliers(out)
        }
        SimplexStatus::Stopped | SimplexStatus::OutOfMemory | SimplexStatus::Cutoff => {
            LaneOutcome::NoEvidence
        }
    }
}

/// The exact rim's own dual solution: one multiplier set, already exact.
fn rim_root_multipliers(
    model: &Model,
    budget: &RootDualBudget,
    report: &mut RootDualReport,
) -> LaneOutcome {
    let Some(mut rim) = ExactLp::new_within(model, budget.deadline) else {
        return LaneOutcome::Unavailable;
    };
    let rim_budget = Budget {
        deadline: budget.deadline,
        max_iters: budget.rim_iters,
    };
    let verdict = rim.minimize(&minimize_frame_objective(model), &rim_budget);
    report.rim_iters = rim.iters_total();
    drop(rim);
    match verdict {
        LpOptimum::Optimal { multipliers, .. } => LaneOutcome::Multipliers(vec![multipliers]),
        LpOptimum::Infeasible(_) => LaneOutcome::Structural(RootDualDecline::RootInfeasible),
        LpOptimum::Unbounded => LaneOutcome::Structural(RootDualDecline::RootUnbounded),
        LpOptimum::Unknown(_) => LaneOutcome::NoEvidence,
    }
}

/// Price every candidate multiplier set against `model`, from every lane, and
/// keep the STRONGEST one that verifies — with the lane that produced it.
///
/// "Strongest" is the largest bound on a Minimize model and the smallest on a
/// Maximize one — the direction in which a bound says more. Comparing ACROSS
/// lanes rather than preferring one is what lets an enabled exact rim improve a
/// weak float bound instead of merely covering for a missing one. Candidates
/// that do not verify are dropped silently: this function's contract is that
/// whatever it returns has already passed [`OptimalityCertificate::verify`].
fn best_certificate(
    model: &Model,
    candidates: Vec<(RootDualLane, Vec<Multiplier>)>,
) -> Option<(RootDualLane, OptimalityCertificate)> {
    let objective = model_objective_exact(model);
    let (low, high) = exact_box(model);
    let offset = model.obj_offset_exact();
    let mut best: Option<(RootDualLane, OptimalityCertificate)> = None;
    for (lane, multipliers) in candidates {
        // DERIVE THE BOUND FROM THE MULTIPLIERS. Neither lane's own reported
        // objective value is consulted: the only number that can enter the
        // certificate is the one this list actually proves at this box.
        let Ok(value) = OptimalityCertificate::bound_leaf_value(&multipliers, model, &low, &high)
        else {
            continue;
        };
        let certificate = OptimalityCertificate {
            sense: model.sense(),
            objective: objective.clone(),
            bound: value.to_big() - &offset,
            multipliers,
        };
        // FAIL CLOSED on the assembled object, through the same public entry
        // point an independent consumer uses. Nothing about this derivation is
        // trusted by what comes after it.
        if certificate.verify(model).is_err() {
            continue;
        }
        let better = best
            .as_ref()
            .is_none_or(|(_, incumbent)| match model.sense() {
                Sense::Minimize => certificate.bound > incumbent.bound,
                Sense::Maximize => certificate.bound < incumbent.bound,
            });
        if better {
            best = Some((lane, certificate));
        }
    }
    best
}

/// The model's own objective as the exact, sorted, duplicate-free coefficient
/// list an [`OptimalityCertificate`] names.
///
/// Uses the same inclusion rule as [`Model::objective_value_at`] and
/// `OptimalityCertificate::bound_leaf_value` — `f64` advice nonzero OR an
/// exact side-store entry — so a coefficient whose `f64` proxy underflowed to
/// zero still carries its true value. A rule that keyed on the `f64` proxy
/// alone would silently bound a DIFFERENT objective than the one the model has.
#[must_use]
pub fn model_objective_exact(model: &Model) -> Vec<(u32, BigRational)> {
    let mut out = Vec::new();
    for (column, spec) in model.cols.iter().enumerate() {
        let column = column as u32;
        if spec.obj != 0.0 || model.exact_obj.contains_key(&column) {
            let coefficient = model.obj_coeff_exact_at(column, spec.obj);
            if !coefficient.is_zero() {
                out.push((column, coefficient));
            }
        }
    }
    out
}

/// The bound `certificate` proves, in the MODEL's frame — objective offset
/// included, so it is directly comparable with `Outcome::Optimal::value` and
/// with the `.ayc` verdict line.
#[must_use]
pub fn root_dual_bound_in_model_frame(
    certificate: &OptimalityCertificate,
    model: &Model,
) -> BigRational {
    &certificate.bound + model.obj_offset_exact()
}

/// Re-derive the residual that an [`OptimalityCertificate`] used as a ROOT
/// DUAL BOUND leaves unproved, in the model's frame: the distance from the
/// proved bound to the claimed optimum, objective offset included on both
/// sides.
///
/// Always non-negative on a well-formed pair, and `Err` when it is not — a
/// "bound" on the wrong side of the claimed optimum is not a weak certificate,
/// it is a contradiction between the block and the verdict line, and a caller
/// must be able to tell those apart.
///
/// # Errors
/// [`CertificateError::ConstantMismatch`] when `certificate` bounds the
/// opposite sense to `model`, or when `bound` is strictly BETTER than
/// `claimed`, i.e. when the two records cannot both be true of one model.
pub fn root_dual_gap(
    certificate: &OptimalityCertificate,
    model: &Model,
    claimed: &BigRational,
) -> Result<BigRational, CertificateError> {
    if certificate.sense != model.sense() {
        return Err(CertificateError::ConstantMismatch);
    }
    let bound = root_dual_bound_in_model_frame(certificate, model);
    let gap = match model.sense() {
        Sense::Minimize => claimed - &bound,
        Sense::Maximize => &bound - claimed,
    };
    if gap < BigRational::from_integer(BigInt::from(0)) {
        return Err(CertificateError::ConstantMismatch);
    }
    Ok(gap)
}
