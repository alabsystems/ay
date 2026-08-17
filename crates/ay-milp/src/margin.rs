// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Margin reframe: turn a feasibility "band-violation" verdict into a
//! margin OPTIMIZATION so dual-bound pruning wakes up.
//!
//! ## The structure
//!
//! A relational whole-net verifier emits an objective-≡0 FEASIBILITY MILP
//! whose UNSAT is the claim it wants: a single one-sided "violation" row
//! `c·x <= t` (or `c·x >= t`) asserts that a band violation EXISTS, and the
//! remaining rows `R` (a conjunction) describe the network. The property the
//! verifier is checking HOLDS exactly when the whole system is INFEASIBLE.
//!
//! Under a zero objective every dual bound is the trivial 0, so branch-and-
//! bound's dual-bound pruning and reduced-cost fixing are DORMANT — the search
//! is pure feasibility enumeration.
//!
//! ## The reframe (an exact, verdict-preserving transformation)
//!
//! Name the violation row with [`Model::mark_margin_row`]. Then, for a
//! `c·x <= t` row, DROP its bound (relax the row to free, keeping its index)
//! and set the objective to **minimize `c·x`** over `R`. Let `v* = min c·x`.
//! Because the original problem is `R ∧ (c·x <= t)`:
//!
//! - `R` feasible with `c·x <= t`  ⟺  `v* <= t`.
//!
//! So the ORIGINAL verdict reads directly off the reframed optimum:
//!
//! - `v* <= t`  ⟹  ORIGINAL FEASIBLE (the reframed optimum point is a witness:
//!   it satisfies `R` and, since `c·x = v* <= t`, the violation row too).
//! - `v* >  t`  ⟹  ORIGINAL INFEASIBLE (no point of `R` reaches the band), and
//!   the reframed [`OptimalityCertificate`] composes with the violation row's
//!   own bound into a [`FarkasCertificate`] for the ORIGINAL — see
//!   [`margin_farkas`].
//! - reframed INFEASIBLE (`R` alone infeasible) ⟹ ORIGINAL INFEASIBLE (the
//!   Farkas witness is valid verbatim: it never references the relaxed row).
//!
//! A `c·x >= t` row is symmetric: **maximize `c·x`**; the original is feasible
//! iff `v* >= t`.
//!
//! ## Soundness
//!
//! Every verdict this module returns is re-adjudicated by the session's shared
//! `finish` gate against the ORIGINAL model (its `check_point` re-tests the
//! witness against ALL rows, the violation row included; `cert.verify`
//! re-checks any Farkas). A mis-map cannot escape as a verdict — it degrades to
//! `Unknown`. Cases the reframe cannot map to an exact verdict (a reframed
//! `Unbounded`, or a timeout whose incumbent does not settle the band) are
//! FAIL-SAFE: the reframe either declines (the caller runs the plain
//! feasibility solve) or returns the honest `Unknown`, never a guess.
//!
//! ## How the margin row is found
//!
//! A caller may NAME it ([`Model::mark_margin_row`]), which is the only route
//! that is on by default. Under `with_auto_margin(true)` an ordinary
//! [`crate::BabSession::check`] that was given no name AUTO-DETECTS one instead
//! (see [`auto_margin_row`]) — the arm that makes this module reachable from a
//! model that arrives as a FILE, which is every ny W1 model and so the whole
//! workload it was written for.
//!
//! **That arm is default-off because it was measured and it lost.** It gains SAT
//! witnesses and loses UNSAT proofs, and UNSAT is the downstream optimization consumer's deliverable; the numbers
//! and the mechanism are at [`auto_margin_row`]. Auto-firing is also a wider
//! blast radius than a caller naming a row, and the soundness argument above is
//! what absorbs it: nothing here is trusted. A detection that picks a poor row
//! costs a slower solve or an honest `Unknown` — never a wrong verdict, because
//! `finish` re-adjudicates every mapped verdict against the ORIGINAL model. That
//! held on all 46 measured models: zero disagreements with the plain solve.
//!
//! Kill switch: `--no-margin-reframe` disables the reframe entirely (the
//! plain feasibility solve decides), marked or detected. Detection additionally
//! requires an objective identically zero, so a model with a real objective is
//! byte-identical however the arm is set.

use num_rational::BigRational;
use num_traits::One;

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier, OptimalityCertificate};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::opts::SolveOpts;
use crate::outcome::{Outcome, UnknownReason};
use crate::session::BabSession;

/// The result of a margin reframe: the ORIGINAL model's verdict plus the
/// diagnostics that make the reframed dual bound observable.
pub(crate) struct Reframed {
    /// The verdict for the ORIGINAL (objective-≡0) feasibility model.
    pub(crate) verdict: Outcome,
    /// Diagnostics (for `diag_margin_reframe` / traces).
    pub(crate) info: ReframeInfo,
}

/// Observable facts about a reframe (diagnostics only; never a verdict).
pub(crate) struct ReframeInfo {
    /// A one-word tag for the reframed solve's outcome.
    pub(crate) reframed_status: &'static str,
    /// The reframed problem's optimum / dual bound (model frame), when the
    /// reframed solve produced one. This is the number that "comes alive"
    /// versus the trivial 0 of the zero objective.
    pub(crate) reframed_bound: Option<BigRational>,
    /// Whether the reframe DECIDED the original verdict (vs surfaced `Unknown`).
    pub(crate) decided: bool,
}

/// A validated margin reframe, split into the optimization model and the
/// caller-frame metadata needed to map its outcome back.
pub(crate) struct PreparedMargin {
    pub(crate) reframed_model: Model,
    pub(crate) mapping: MarginMapping,
}

/// Caller-frame metadata for one validated margin reframe.
pub(crate) struct MarginMapping {
    row: Row,
    sense: Sense,
    threshold: BigRational,
}

/// Proof-only target passed to the native tree.
///
/// A rigorous interrupted-tree bound may use this only to trigger
/// caller-frame certificate finalization. The bound itself is never verdict
/// authority.
pub(crate) struct MarginProofTarget<'a> {
    proof_model: &'a Model,
    sense: Sense,
    threshold: BigRational,
}

impl MarginMapping {
    pub(crate) fn proof_target<'a>(&self, proof_model: &'a Model) -> MarginProofTarget<'a> {
        MarginProofTarget {
            proof_model,
            sense: self.sense,
            threshold: self.threshold.clone(),
        }
    }

    pub(crate) fn map(self, orig: &Model, reframed: Outcome) -> Reframed {
        map_reframed(orig, self.row, self.sense, &self.threshold, reframed)
    }
}

impl MarginProofTarget<'_> {
    /// Equality is not exclusion: a point on the closed row bound may witness
    /// the original feasibility model.
    pub(crate) fn strictly_excludes(&self, bound: &BigRational) -> bool {
        match self.sense {
            Sense::Minimize => bound > &self.threshold,
            Sense::Maximize => bound < &self.threshold,
        }
    }

    pub(crate) fn proof_model(&self) -> &Model {
        self.proof_model
    }
}

/// Attempt the margin reframe for `model` under `opts`.
///
/// Returns `None` when the reframe DECLINES (no margin named or detected, kill
/// switch set, a non-≡0 objective, or a margin row that is not a clean single
/// one-sided inequality) — the caller then runs the plain feasibility solve,
/// unchanged. Returns `Some(Reframed)` with a mapped verdict (or an honest
/// `Unknown`) otherwise.
///
/// This is the ORDINARY `check()` entry, so it takes the AUTO-DETECTED margin
/// when the caller named none (see [`auto_margin_row`]). The explicit
/// shared-margin API goes through [`prepare`] instead and still requires a mark.
pub(crate) fn reframe(model: &Model, opts: &SolveOpts) -> Option<Reframed> {
    let PreparedMargin {
        reframed_model,
        mapping,
    } = prepare_auto(model)?;
    let mut sub = BabSession::new(reframed_model, opts).ok()?;
    let reframed_outcome = sub.check().ok()?;
    Some(mapping.map(model, reframed_outcome))
}

/// Validate and construct a margin reframe without starting a solver, from a
/// margin the CALLER named.
///
/// `None` is a fail-safe decline. The ordinary check then runs plain
/// feasibility; the explicit shared-margin API instead reports a typed error
/// before starting its nested search — which is why this entry deliberately does
/// NOT auto-detect: "the caller must name the row" is that API's contract, and an
/// auto-detected row would answer a question the caller never asked.
pub(crate) fn prepare(model: &Model) -> Option<PreparedMargin> {
    if reframe_disabled() {
        return None;
    }
    prepare_row(model, model.margin_row()?)
}

/// The whole-module kill switch, read at ONE literal site so the ledger's
/// derived read-site count stays a fact about the source rather than a guess.
fn reframe_disabled() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::NoMarginReframe) == Some(true)
}

/// [`prepare`], falling back to [`auto_margin_row`] when no margin is marked.
pub(crate) fn prepare_auto(model: &Model) -> Option<PreparedMargin> {
    if reframe_disabled() {
        return None;
    }
    let row = match model.margin_row() {
        Some(row) => row,
        None => auto_margin_row(model)?,
    };
    prepare_row(model, row)
}

/// AUTO-DETECT the band-violation row of an objective-≡0 feasibility model.
///
/// # Why this exists
///
/// This module was written for exactly one model class and could not be reached
/// from a plain [`BabSession::check`]: [`Model::mark_margin_row`]'s only
/// non-test callers are the explicit shared-prefix API (which requires the
/// CALLER to name the row) and the `ay-milp diag margin-row` CLI. So the entire
/// reframe was dormant on every model that arrives as a file — which is every ny
/// W1 model, the whole workload it describes.
///
/// # The shape, and why each condition is load-bearing
///
/// A relational verifier emits `R ∧ (c·x ⋛ t)` where the violation row is a
/// SINGLETON over a FREE slack column: the downstream optimization consumer's W1 models carry `R394: X324 >= 1`
/// and `R395: X325 <= 0`, with `X324`/`X325` free and defined by an equality row
/// of `R`. Each condition rejects a shape the reframe would waste work on:
///
/// * **objective ≡ 0** — a model with a real objective is an optimization and
///   its objective is the caller's, not ours to replace. This is the condition
///   that keeps every off-class model byte-identical.
/// * **singleton row** — a multi-column row is not a *slack* declaration, and
///   guessing which of several structural rows is "the violation" is exactly the
///   guess `mark_margin_row` exists to avoid.
/// * **one-sided** — an equality or a range is not a band; [`prepare_row`]
///   re-checks this, but excluding it here keeps the candidate set honest.
/// * **the column is FREE** — a bounded column is already bounded without the
///   row, so relaxing the row would leave a bound the reframe did not create and
///   the "margin" would be a box corner rather than the network's own reach. Free
///   also means the row is the ONLY thing constraining that side, which is what
///   makes it a violation ASSERTION rather than an ordinary constraint.
/// * **the column appears in some OTHER row** — otherwise the relaxed problem is
///   trivially unbounded, the reframe maps to `Unknown` and the caller pays a
///   whole nested solve to learn nothing.
///
/// # Why the LAST candidate wins
///
/// The shape admits SEVERAL candidates (both W1 rows above qualify), and folding
/// any one of them is exactly as sound — the reframe relaxes one row and keeps
/// the rest of `R`, including the other candidates, as constraints. So the rule
/// only has to be DETERMINISTIC, and it is the last (highest-index) row: emitters
/// append the property being checked after the network they check, so the last
/// candidate is the outermost assertion. Measured on `W1_unsat_v30_c38_000000`,
/// both candidates wake the bound off its trivial 0 and neither dominates
/// (row 394 `max X324` root LP 1.0 against threshold 1; row 395 `min X325` root
/// LP -6.1e-5 against threshold 0).
///
/// # ⛔ DEFAULT OFF: MEASURED, AND IT LOSES THE VERDICT ny WANTS
///
/// `with_auto_margin(true)` opts in. The name exists because the negative result
/// is worth keeping re-checkable, not because the arm is dormant scaffolding —
/// it fires, it works, and the trade is the wrong way round for this consumer.
///
/// Serial, 46 captured ny W1 models, 30s, one binary, two runs:
///
/// ```text
///   arm                     decided   sat roots   unsat roots   nodes-to-proof*
///   plain feasibility        25/46       8/10         2/13            379
///   auto margin reframe      22/46      10/10         1/13         41,867
///   * on the 12 instances BOTH arms decide (load-invariant: a completed proof)
/// ```
///
/// It gains exactly what a margin objective is good at and loses exactly what it
/// is not. The reframed objective is a PRIMAL driver — it points the search
/// straight at the band — so both previously-open SAT roots
/// (`sat_v83_c328_000000`, `sat_v99_c485_000000`) now land a witness. But proving
/// the band UNREACHABLE means closing an optimality gap on the reframed model,
/// and that is strictly harder than the feasibility refutation it replaced: FIVE
/// UNSAT instances lost their proof, including `unsat_v16_c39_000000` (INFEASIBLE
/// in 4.3s -> UNKNOWN at 30s) and `unsat_v75_c99_000008` (1.1s / 15 nodes ->
/// UNKNOWN at 30s / 30,889 nodes). the downstream optimization consumer's W1 deliverable is UNSAT, so a +2 SAT /
/// −5 UNSAT trade is a loss whatever the totals say.
///
/// ⚠ AND THE REFRAME DISABLES THE LEVERS THAT DO WORK ON THIS CLASS. The reframed
/// model has a REAL objective by construction, so `bab::feasibility_conflict_class`
/// is false inside the nested solve and the conflict lane — nogood unit
/// propagation, nogood-guided branching, propagation-conflict learning, VSIDS —
/// goes dark exactly where it was measured to be worth 10.96x. The two devices
/// are mutually exclusive on the same model, and the conflict lane is the one
/// that wins.
///
/// Nothing here is unsound: every mapped verdict agreed with the plain solve on
/// all 46 models, and the losses are `Unknown`, never a wrong answer.
fn auto_margin_row(model: &Model) -> Option<Row> {
    // Default OFF (see above). `=0`/`off` is spelled out rather than left to
    // `is_ok()` so that setting the name to zero cannot mean "on" — the ledger's
    // own `ZERO_IGNORED` trap in reverse.
    let opted_in = crate::tune::caller_flag(crate::tune::Knob::AutoMargin) == Some(true);
    if !opted_in {
        return None;
    }
    if !model.objective_is_identically_zero() {
        return None;
    }
    let n = model.num_rows();
    // Column -> how many rows mention it. One pass; the candidate test needs
    // "appears in some OTHER row", which is `count >= 2` for a singleton row.
    let mut row_uses = vec![0u32; model.num_cols()];
    for r in 0..n {
        let (coeffs, _, _) = model.row(Row(r as u32));
        for &(c, _) in coeffs {
            row_uses[c as usize] = row_uses[c as usize].saturating_add(1);
        }
    }
    (0..n).rev().map(|r| Row(r as u32)).find(|&row| {
        let (coeffs, lb, ub) = model.row(row);
        let [(c, _)] = coeffs[..] else { return false };
        if lb.is_finite() == ub.is_finite() {
            return false; // not one-sided (equality, range, or free)
        }
        let (clb, cub) = model.col_bounds(Col(c));
        clb == f64::NEG_INFINITY && cub == f64::INFINITY && row_uses[c as usize] >= 2
    })
}

/// Validate `row` as a margin for `model` and build the reframed optimization.
fn prepare_row(model: &Model, row: Row) -> Option<PreparedMargin> {
    // Defense in depth: only reframe a genuine objective-≡0 feasibility model.
    // A caller that named a margin but also set a real objective is misusing
    // the hint; decline and let the plain solve honor the objective.
    if !model.objective_is_identically_zero() {
        return None;
    }
    let ridx = row.index();
    if ridx >= model.num_rows() {
        return None;
    }
    let (coeffs, lb, ub) = model.row(row);
    if coeffs.is_empty() {
        return None;
    }
    // A clean margin is ONE-SIDED: exactly one finite bound. A two-sided range,
    // an equality, or a free row is not a single margin — decline (fail-safe).
    let (sense, threshold) = match (lb.is_finite(), ub.is_finite()) {
        (false, true) => (Sense::Minimize, model.row_ub_exact(ridx, ub)?),
        (true, false) => (Sense::Maximize, model.row_lb_exact(ridx, lb)?),
        _ => return None,
    };
    let reframed_model = build_reframed(model, row, sense);
    Some(PreparedMargin {
        reframed_model,
        mapping: MarginMapping {
            row,
            sense,
            threshold,
        },
    })
}

/// Build the reframed optimization model: relax the margin row to free (keeping
/// its index so certificate facts stay aligned with the original) and set the
/// objective to `sense · (c·x)` where `c` is the margin row's coefficients.
fn build_reframed(model: &Model, row: Row, sense: Sense) -> Model {
    let (coeffs, _lb, _ub) = model.row(row);
    let obj: Vec<(Col, f64)> = coeffs.iter().map(|&(c, a)| (Col(c), a)).collect();
    let ridx = row.index();
    // Capture the margin row's TRUE (exact) coefficients BEFORE mutating, so an
    // inexact-`f64` coefficient carries into the objective exactly rather than
    // as its rounded proxy — otherwise the reframe would optimize the WRONG
    // objective and the threshold comparison would be unsound.
    let exact_obj: Vec<(u32, BigRational)> = if model.has_inexact_coeffs() {
        coeffs
            .iter()
            .filter_map(|&(c, a)| {
                let ex = model.row_coeff_exact(ridx, c, a);
                (Some(&ex) != exact(a).as_ref()).then_some((c, ex))
            })
            .collect()
    } else {
        Vec::new()
    };

    let mut m = model.clone();
    m.margin = None; // the reframed solve must not re-enter the reframe
    m.set_objective(&obj, sense);
    for (c, ex) in exact_obj {
        m.record_inexact_obj_coeff(c, ex);
    }
    // Relax the row to free: it keeps its index and coefficients but constrains
    // nothing, so it drops out of feasibility and can never be referenced by a
    // certificate (an infinite bound has no fact).
    m.set_row(row, f64::NEG_INFINITY, f64::INFINITY, &obj);
    m
}

/// Map the reframed solve's outcome to the ORIGINAL feasibility verdict.
fn map_reframed(
    orig: &Model,
    row: Row,
    sense: Sense,
    threshold: &BigRational,
    reframed: Outcome,
) -> Reframed {
    let info = |status: &'static str, bound: Option<BigRational>, decided: bool| ReframeInfo {
        reframed_status: status,
        reframed_bound: bound,
        decided,
    };
    match reframed {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            // `value` is the reframed optimum in the model frame (min c·x for a
            // `<=` row, max c·x for a `>=` row); the reframed offset is 0.
            let reaches = match sense {
                Sense::Minimize => value <= *threshold, // min c·x <= t
                Sense::Maximize => value >= *threshold, // max c·x >= t
            };
            if reaches {
                // The reframed optimum satisfies `R` and the band: a witness for
                // the ORIGINAL. (`finish` re-checks it against every row.)
                Reframed {
                    verdict: Outcome::Feasible {
                        model_values,
                        incumbent_only: false,
                        dual_bound: None,
                    },
                    info: info("OPTIMAL", Some(value), true),
                }
            } else {
                // `v*` past the band ⟹ ORIGINAL INFEASIBLE. Compose the reframed
                // dual proof with the band bound into a Farkas for the original.
                let farkas = cert
                    .as_ref()
                    .and_then(|c| margin_farkas(orig, row, sense, c));
                Reframed {
                    verdict: Outcome::Infeasible {
                        cert: farkas,
                        tree_cert: None,
                    },
                    info: info("OPTIMAL", Some(value), true),
                }
            }
        }
        Outcome::Infeasible { cert, tree_cert } => {
            // Ordinarily this means `R` alone is infeasible, so the original
            // (a subset) is too and its witnesses transfer verbatim. The
            // explicit interrupted-margin path may instead have returned a
            // tree already derived against the original row. In either case,
            // keep only artifacts that independently re-verify in that
            // original frame.
            let cert = cert.filter(|c| c.verify(orig).is_ok());
            let tree_cert = tree_cert.filter(|c| c.verify(orig).is_ok());
            Reframed {
                verdict: Outcome::Infeasible { cert, tree_cert },
                info: info("INFEASIBLE", None, true),
            }
        }
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => {
            // A timeout with an incumbent of `R`. If the incumbent also lands in
            // the band it settles the original FEASIBLE; otherwise we cannot
            // decide from an incumbent alone (the un-exported tree dual bound is
            // not independently checkable), so return the honest `Unknown` and
            // surface the reframed bound for the demo.
            if orig.check_point(&model_values).is_ok() {
                Reframed {
                    verdict: Outcome::Feasible {
                        model_values,
                        incumbent_only: false,
                        dual_bound: None,
                    },
                    info: info("FEASIBLE_INCUMBENT", dual_bound, true),
                }
            } else {
                Reframed {
                    verdict: Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    },
                    info: info("FEASIBLE_UNDECIDED", dual_bound, false),
                }
            }
        }
        Outcome::Unknown { reason } => Reframed {
            verdict: Outcome::Unknown { reason },
            info: info("UNKNOWN", None, false),
        },
        // `min c·x = -inf` (resp. `max = +inf`) means the band IS reachable, so
        // the original is FEASIBLE — but the reframed `Unbounded` carries no
        // witness ray to exhibit one. Decline; the caller's plain feasibility
        // solve produces a witnessed verdict.
        Outcome::Unbounded => Reframed {
            verdict: Outcome::Unknown {
                reason: UnknownReason::SolverIncomplete {
                    detail: "margin reframe unbounded; deferring to plain feasibility".to_owned(),
                },
            },
            info: info("UNBOUNDED", None, false),
        },
        Outcome::Bound { .. } => Reframed {
            verdict: Outcome::Unknown {
                reason: UnknownReason::Timeout,
            },
            info: info("BOUND", None, false),
        },
    }
}

/// Compose the reframed [`OptimalityCertificate`] with the violation row's own
/// bound into a [`FarkasCertificate`] for the ORIGINAL model, in the `v*` past
/// the band case.
///
/// For a `c·x <= t` row (Minimize, `v* > t`) the certificate proves
/// `Σ μ·oriented = c·x − v*` over `R`; adding the row's UPPER fact `t − c·x`
/// (multiplier 1) gives `t − v* < 0` with every column cancelling — a Farkas
/// contradiction. For a `c·x >= t` row (Maximize, `v* < t`) it proves
/// `Σ μ·oriented = v* − c·x`; adding the row's LOWER fact `c·x − t` gives
/// `v* − t < 0`. Both verify against the original with no re-derivation, because
/// the reframed certificate references only `R`'s facts (identical in the
/// original) and the added fact is the original violation row's finite bound.
fn margin_farkas(
    orig: &Model,
    row: Row,
    sense: Sense,
    cert: &OptimalityCertificate,
) -> Option<FarkasCertificate> {
    // The reframed certificate must already recombine correctly against the
    // original's `R` facts (they are the same facts). If it does not, decline
    // the export rather than emit an unchecked witness.
    if cert.verify(orig).is_err() {
        return None;
    }
    let side = match sense {
        Sense::Minimize => BoundSide::Upper, // t − c·x
        Sense::Maximize => BoundSide::Lower, // c·x − t
    };
    let mut multipliers = cert.multipliers.clone();
    multipliers.push(Multiplier {
        fact: FactRef::RowBound { row, side },
        coeff: BigRational::one(),
    });
    let farkas = FarkasCertificate { multipliers };
    farkas.verify(orig).is_ok().then_some(farkas)
}

/// Diagnostic: build the margin reframe for `model` and report the reframed
/// dual bound next to the trivial-0 zero-objective bound, plus the mapped
/// verdict. Mirrors [`crate::diag_float_lp`]; used by the `mps_solve` example
/// under the margin-row demo flag.
#[must_use]
pub fn diag_margin_reframe(model: &Model, secs: f64) -> String {
    use num_traits::ToPrimitive;
    let Some(row) = model.margin_row() else {
        return "diag_margin_reframe: no margin row marked (call mark_margin_row)".to_owned();
    };
    // Root LP bound of the zero objective (the "before"): always the trivial 0.
    // Root LP bound of the reframe (the "after"): the meaningful margin bound.
    let ridx = row.index();
    let (_c, lb, ub) = model.row(row);
    let sense = match (lb.is_finite(), ub.is_finite()) {
        (false, true) => Sense::Minimize,
        (true, false) => Sense::Maximize,
        _ => return "diag_margin_reframe: margin row is not one-sided".to_owned(),
    };
    let threshold = match sense {
        Sense::Minimize => model.row_ub_exact(ridx, ub),
        Sense::Maximize => model.row_lb_exact(ridx, lb),
    };
    let reframed_model = build_reframed(model, row, sense);

    // The reframed root LP relaxation optimum (float lane, min-form): the
    // rigorous dual bound the search's own pruning reads. This is the "dual
    // bound comes alive" number — nonzero and informative where the zero
    // objective's is the trivial 0. Extracted from the shared `diag_float_lp`
    // so it measures exactly the engine's root LP.
    let lp_budget = secs.min(15.0);
    let root_lp = crate::diag_float_lp(&reframed_model, lp_budget)
        .split("obj(min-form)=")
        .nth(1)
        .and_then(|s| s.split_whitespace().next())
        .unwrap_or("?")
        .to_owned();

    // The full reframe + verdict map (what the session would return).
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs_f64(secs.min(30.0)));
    let mapped = reframe(model, &opts);
    let (status, bound, decided, verdict) = match mapped {
        Some(r) => {
            let b = r.info.reframed_bound.as_ref().map_or_else(
                || "-".to_owned(),
                |v| {
                    v.to_f64()
                        .map_or_else(|| v.to_string(), |f| format!("{f:.6}"))
                },
            );
            (
                r.info.reframed_status,
                b,
                r.info.decided,
                verdict_tag(&r.verdict),
            )
        }
        None => ("DECLINED", "-".to_owned(), false, "plain-feasibility"),
    };
    let t = threshold.as_ref().map_or_else(
        || "?".to_owned(),
        |v| v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}")),
    );
    format!(
        "diag_margin_reframe: row={ridx} sense={sense:?} threshold={t} \
         zero_obj_root_bound=0 reframed_root_LP_bound={root_lp} \
         reframed_solve={status} reframed_bound={bound} decided={decided} => original={verdict}"
    )
}

/// A one-word tag for an outcome (diagnostics).
fn verdict_tag(o: &Outcome) -> &'static str {
    match o {
        Outcome::Optimal { .. } => "OPTIMAL",
        Outcome::Feasible { .. } => "FEASIBLE",
        Outcome::Infeasible { .. } => "INFEASIBLE",
        Outcome::Unbounded => "UNBOUNDED",
        Outcome::Bound { .. } => "BOUND",
        Outcome::Unknown { .. } => "UNKNOWN",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_test_support::env::lock_env;

    /// Every detection test runs with the arm ON, because the arm is default-OFF
    /// (measured losing; see [`auto_margin_row`]). `default_is_off` below is the
    /// one test that asserts the default itself.
    fn armed() -> crate::tune::Active {
        crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::AutoMargin,
            crate::tune::Setting::Flag(true),
        ))
    }

    /// The ny W1 shape in miniature: an objective-≡0 model whose network rows
    /// define two FREE slack columns, each asserted one-sided by its own
    /// singleton row (`W1_unsat_v30_c38` carries `R394: X324 >= 1` and
    /// `R395: X325 <= 0` over free `X324`/`X325`).
    fn w1_shape() -> (Model, Row, Row) {
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_binary_col();
        let s0 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let s1 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        // The "network": s0 = a + b, s1 = a - b.
        m.add_row(0.0, 0.0, &[(a, 1.0), (b, 1.0), (s0, -1.0)]);
        m.add_row(0.0, 0.0, &[(a, 1.0), (b, -1.0), (s1, -1.0)]);
        // The two violation assertions.
        let lo = m.add_row(1.0, f64::INFINITY, &[(s0, 1.0)]);
        let hi = m.add_row(f64::NEG_INFINITY, 0.0, &[(s1, 1.0)]);
        (m, lo, hi)
    }

    /// THE DEFAULT. Detection is opt-in, so an unmarked model runs the plain
    /// feasibility solve and every model in the crate's corpora is untouched.
    #[test]
    fn default_is_off() {
        let _env_lock = lock_env();
        let (m, _lo, _hi) = w1_shape();
        assert_eq!(auto_margin_row(&m), None, "the arm must be default-off");
        assert!(
            prepare_auto(&m).is_none(),
            "with the arm unset an unmarked model runs plain feasibility"
        );
        // An explicit `false` must mean off, not "the knob is set, therefore on".
        let _zero = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::AutoMargin,
            crate::tune::Setting::Flag(false),
        ));
        assert_eq!(auto_margin_row(&m), None);
    }

    #[test]
    fn auto_detect_takes_the_last_candidate() {
        let _env_lock = lock_env();
        let _on = armed();
        let (m, lo, hi) = w1_shape();
        assert!(lo.index() < hi.index(), "fixture orders the two candidates");
        assert_eq!(
            auto_margin_row(&m),
            Some(hi),
            "several candidates are equally sound; the rule must be the last one"
        );
    }

    #[test]
    fn auto_detect_declines_a_real_objective() {
        let _env_lock = lock_env();
        let _on = armed();
        let (mut m, _lo, _hi) = w1_shape();
        let col = m.col_at(0).expect("in range");
        m.set_objective(&[(col, 1.0)], Sense::Minimize);
        assert_eq!(
            auto_margin_row(&m),
            None,
            "a model with a real objective must be untouched by detection"
        );
    }

    /// A BOUNDED column is already bounded without the row, so relaxing the row
    /// would leave a bound the reframe did not create: the "margin" would be a box
    /// corner rather than the network's own reach.
    #[test]
    fn auto_detect_declines_a_bounded_column() {
        let _env_lock = lock_env();
        let _on = armed();
        let mut m = Model::new();
        let a = m.add_binary_col();
        let s = m.add_col(0.0, 8.0);
        m.add_row(0.0, 0.0, &[(a, 1.0), (s, -1.0)]);
        m.add_row(1.0, f64::INFINITY, &[(s, 1.0)]);
        assert_eq!(auto_margin_row(&m), None);
    }

    /// A free column appearing in NO other row makes the relaxed problem
    /// trivially unbounded: the reframe would map to `Unknown` and the caller
    /// would have paid a whole nested solve to learn nothing.
    #[test]
    fn auto_detect_declines_a_column_no_other_row_mentions() {
        let _env_lock = lock_env();
        let _on = armed();
        let mut m = Model::new();
        let a = m.add_binary_col();
        let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        m.add_row(0.0, 1.0, &[(a, 1.0)]);
        m.add_row(1.0, f64::INFINITY, &[(s, 1.0)]);
        assert_eq!(auto_margin_row(&m), None);
    }

    /// An equality, a two-sided range, a free row and a multi-column row are all
    /// not a single one-sided band, and none may be guessed at.
    #[test]
    fn auto_detect_declines_non_band_shapes() {
        let _env_lock = lock_env();
        let _on = armed();
        for (lb, ub) in [(1.0, 1.0), (0.0, 2.0), (f64::NEG_INFINITY, f64::INFINITY)] {
            let mut m = Model::new();
            let a = m.add_binary_col();
            let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
            m.add_row(0.0, 0.0, &[(a, 1.0), (s, -1.0)]);
            m.add_row(lb, ub, &[(s, 1.0)]);
            assert_eq!(auto_margin_row(&m), None, "({lb}, {ub}) is not a band");
        }
        let mut m = Model::new();
        let a = m.add_binary_col();
        let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(a, 1.0), (s, -1.0)]);
        m.add_row(1.0, f64::INFINITY, &[(a, 1.0), (s, 1.0)]);
        assert_eq!(auto_margin_row(&m), None, "a two-column row is not a slack");
    }

    /// An explicitly MARKED margin always wins: detection is a fallback for the
    /// callers that cannot name one, never an override of one that did.
    #[test]
    fn a_marked_margin_beats_the_detected_one() {
        let _env_lock = lock_env();
        let _on = armed();
        let (mut m, lo, hi) = w1_shape();
        m.mark_margin_row(lo).expect("one-sided margin");
        assert_eq!(auto_margin_row(&m), Some(hi));
        let prepared = prepare_auto(&m).expect("prepared");
        assert_eq!(
            prepared.mapping.row, lo,
            "the caller's mark must be honored"
        );
    }

    /// The wider kill switch turns off the reframe however the row was found.
    #[test]
    fn the_reframe_kill_switch_outranks_the_arm() {
        let _on = armed();
        let _off = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::NoMarginReframe,
            crate::tune::Setting::Flag(true),
        ));
        let (m, _lo, _hi) = w1_shape();
        assert!(prepare_auto(&m).is_none());
    }

    /// The explicit shared-margin API's contract is "the caller names the row",
    /// and detection must not answer a question that API's caller never asked.
    #[test]
    fn the_explicit_prepare_entry_never_auto_detects() {
        let _env_lock = lock_env();
        let _on = armed();
        let (m, _lo, hi) = w1_shape();
        assert_eq!(auto_margin_row(&m), Some(hi));
        assert!(prepare(&m).is_none());
    }
}
