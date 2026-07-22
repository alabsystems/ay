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
//! Kill switch: `AY_MILP_NO_MARGIN_REFRAME=1` disables the reframe (the plain
//! feasibility solve decides). The feature is dormant unless a caller names a
//! margin row, so every model that never does is byte-identical.

use num_rational::BigRational;
use num_traits::{One, Zero};

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

/// Whether the model's objective is identically zero (every coefficient AND the
/// offset exactly 0). A nonzero true rational never rounds to `0.0` for the
/// magnitudes the reader admits, so the `f64` coefficient test is exact; the
/// offset is checked through the exact side-store.
fn objective_is_zero(m: &Model) -> bool {
    (0..m.num_cols()).all(|j| m.obj_coeff(Col(j as u32)) == 0.0) && m.obj_offset_exact().is_zero()
}

/// Attempt the margin reframe for `model` under `opts`.
///
/// Returns `None` when the reframe DECLINES (no margin named, kill switch set,
/// a non-≡0 objective, or a margin row that is not a clean single one-sided
/// inequality) — the caller then runs the plain feasibility solve, unchanged.
/// Returns `Some(Reframed)` with a mapped verdict (or an honest `Unknown`)
/// otherwise.
pub(crate) fn reframe(model: &Model, opts: &SolveOpts) -> Option<Reframed> {
    if std::env::var_os("AY_MILP_NO_MARGIN_REFRAME").is_some() {
        return None;
    }
    let row = model.margin_row()?;
    // Defense in depth: only reframe a genuine objective-≡0 feasibility model.
    // A caller that named a margin but also set a real objective is misusing
    // the hint; decline and let the plain solve honor the objective.
    if !objective_is_zero(model) {
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
    let mut sub = BabSession::new(reframed_model, opts).ok()?;
    let reframed_outcome = sub.check().ok()?;
    Some(map_reframed(
        model,
        row,
        sense,
        &threshold,
        reframed_outcome,
    ))
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
            // `R` alone is infeasible ⟹ the original (a subset) is too. The
            // witnesses never reference the relaxed row, so they verify verbatim
            // against the original; keep only what re-verifies (belt-and-braces).
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
/// under `AY_MILP_MARGIN_ROW`.
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
