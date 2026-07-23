// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stateful LP and MILP solve sessions.
//!
//! [`LpSession`] supports one continuous model with many objectives and keeps
//! its exact-rational basis across re-solves. [`BabSession`] provides scoped
//! `fix_col`/`add_row` operations for MILP, using native branch-and-bound for
//! integral models and the exact LP path for continuous models. When a MILP's
//! root relaxation is already contradictory, the session may attach an exact
//! Farkas certificate to the infeasibility verdict.

use std::time::{Duration, Instant};

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::OptimalityCertificate;
use crate::certify::certify;
use crate::error::{MilpError, ModelError};
use crate::exact::{Budget, ExactLp, LpFeasibility, LpOptimum};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::opts::SolveOpts;
use crate::outcome::{Outcome, UnknownReason};
use crate::simplex::{FloatLp, SimplexStatus};

/// Whether the float lane runs. Off via `AY_MILP_NO_FLOAT=1`, which forces every
/// solve down the exact rim — the A/B switch the float lane's speedup is
/// measured with, and the escape hatch if it ever misbehaves. Read once: this
/// sits on the per-solve path.
fn float_lane_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_MILP_NO_FLOAT").is_none())
}

/// Build the exact-lane iteration/deadline budget for `model` under `opts`.
fn budget_for(model: &Model, opts: &SolveOpts) -> Budget {
    Budget {
        deadline: opts.effective_deadline(Instant::now()),
        max_iters: Budget::default_iters(model.num_cols() + model.num_rows()),
    }
}

/// [`budget_for`] with bounded post-verdict grace for certificate derivation.
/// Farkas enrichment runs after search, when the original deadline may already
/// be exhausted. A solve that already has a verdict may therefore spend up to
/// `min(5s, 25% of the configured time limit)` beyond that deadline deriving
/// an independently checkable witness. This never extends the search; a budget
/// miss leaves the verdict uncertified.
fn cert_budget_for(model: &Model, opts: &SolveOpts) -> Budget {
    let now = Instant::now();
    let grace = opts
        .time_limit
        .map(|t| t.mul_f64(0.25).min(Duration::from_secs(5)))
        .unwrap_or(Duration::from_secs(5));
    let floor = now + grace;
    let deadline = match opts.effective_deadline(now) {
        Some(d) if d > floor => Some(d),
        _ => Some(floor),
    };
    Budget {
        deadline,
        max_iters: Budget::default_iters(model.num_cols() + model.num_rows()),
    }
}

/// The native lane's post-verdict enrichment budget: bounded grace rather
/// than the whole remaining wall. A contradictory root relaxation can yield a
/// Farkas certificate quickly; when infeasibility required branching, no root
/// certificate exists and a long exact pass would be wasted. The pass is
/// therefore capped at `max(5s, 15% of the time limit)`, overridable with
/// `AY_MILP_CERT_GRACE=<secs>` (`0` selects the uncapped behavior). The verdict
/// is never at stake: a budget miss only leaves `cert` as `None`.
fn cert_budget_native(model: &Model, opts: &SolveOpts) -> Budget {
    let uncapped = cert_budget_for(model, opts);
    let cap = match std::env::var("AY_MILP_CERT_GRACE")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
    {
        Some(s) if s == 0.0 => return uncapped,
        Some(s) if s > 0.0 => Duration::from_secs_f64(s),
        _ => opts
            .time_limit
            .map(|t| t.mul_f64(0.15).max(Duration::from_secs(5)))
            .unwrap_or(Duration::from_secs(5)),
    };
    let ceiling = Instant::now() + cap;
    Budget {
        deadline: Some(uncapped.deadline.map_or(ceiling, |d| d.min(ceiling))),
        max_iters: uncapped.max_iters,
    }
}

/// Exact objective coefficients of `coeffs` (f64) — validated finite.
fn exact_obj(coeffs: &[(u32, f64)]) -> Vec<(u32, Rational)> {
    let mut out: Vec<(u32, Rational)> = coeffs
        .iter()
        .filter(|&&(_, a)| a != 0.0)
        .map(|&(c, a)| {
            (
                c,
                Rational::from_big(exact(a).expect("validated objective coefficient")),
            )
        })
        .collect();
    out.sort_unstable_by_key(|&(c, _)| c);
    out
}

/// Apply `require_certificates` policy: strip-or-degrade uncertified
/// verdicts.
fn apply_cert_policy(outcome: Outcome, opts: &SolveOpts) -> Outcome {
    if !opts.require_certificates {
        return outcome;
    }
    match &outcome {
        // A whole-tree certificate satisfies the policy: it is exact,
        // independently checkable evidence, same as the root Farkas.
        Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        }
        | Outcome::Optimal { cert: None, .. } => Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
        },
        _ => outcome,
    }
}

/// A model objective in exact rationals: `(coeffs, offset)`. Present only when
/// the model carries inexact objective coefficients (rounded `f64` proxies);
/// then the re-derivation gate must read the TRUE objective, not the `f64` one.
type ExactObjective = (Vec<(u32, BigRational)>, BigRational);

/// The objective a solve actually ran against. Not always the model's own:
/// `LpSession::optimize` bounds a single column, and `tighten_col_bounds`
/// leans on that.
struct SolvedObjective<'a> {
    coeffs: &'a [(u32, f64)],
    sense: Sense,
    offset: f64,
    /// The TRUE rational objective, set ONLY when `coeffs` IS the model's own
    /// objective AND the model carries inexact obj coefficients. When present
    /// `value_at` re-derives the reported value from it, closing the
    /// rounded-objective wrong-value hole (a rounded reported value and the
    /// rounded re-derivation would otherwise agree with each other).
    exact: Option<ExactObjective>,
}

impl SolvedObjective<'_> {
    /// The exact objective value at an exact point.
    fn value_at(&self, values: &[BigRational]) -> BigRational {
        if let Some((coeffs, offset)) = &self.exact {
            let mut acc = offset.clone();
            for (c, a) in coeffs {
                acc += a * &values[*c as usize];
            }
            return acc;
        }
        let mut acc = exact(self.offset).unwrap_or_else(BigRational::zero);
        for &(c, a) in self.coeffs {
            if let Some(a) = exact(a) {
                acc += a * &values[c as usize];
            }
        }
        acc
    }
}

/// Re-derive a verdict's claims from the model alone, consulting no solver
/// state. `Err` names the first claim that does not hold up.
///
/// The dual certificate alone is insufficient: [`OptimalityCertificate`]
/// bounds the objective but says nothing about the point in `model_values`.
/// The primal side is therefore re-tested against every bound, row, and
/// integrality requirement before an outcome reaches the caller.
fn validate_witnesses(
    outcome: &Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
) -> Result<(), String> {
    let check_arity = |vals: &[BigRational]| -> Result<(), String> {
        if vals.len() == model.num_cols() {
            Ok(())
        } else {
            Err(format!(
                "point has {} values for a {}-column model",
                vals.len(),
                model.num_cols()
            ))
        }
    };
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            check_arity(model_values)?;
            if let Err(v) = model.check_point(model_values) {
                return Err(format!("the point claimed optimal is infeasible: {v:?}"));
            }
            let attained = obj.value_at(model_values);
            if attained != *value {
                return Err(format!(
                    "the point attains {attained}, not the reported optimum {value}"
                ));
            }
            if let Some(cert) = cert {
                cert.verify(model)
                    .map_err(|e| format!("optimality certificate does not verify: {e}"))?;
                let offset = obj.exact.as_ref().map_or_else(
                    || exact(obj.offset).unwrap_or_else(BigRational::zero),
                    |(_, o)| o.clone(),
                );
                let bound = cert.bound.clone() + offset;
                // A dual bound may trail the primal across an integrality gap,
                // but it may never cross it — that is a contradiction, not a
                // gap. A continuous model has no gap to trail across, so there
                // meeting the primal is what makes the pair a proof of
                // optimality rather than merely a valid bound.
                let crossed = match obj.sense {
                    Sense::Minimize => bound > *value,
                    Sense::Maximize => bound < *value,
                };
                if crossed {
                    return Err(format!(
                        "certified dual bound {bound} crosses the primal optimum {value}"
                    ));
                }
                if !model.has_integrality() && bound != *value {
                    return Err(format!(
                        "certified dual bound {bound} does not meet the primal optimum {value} \
                         on a continuous model"
                    ));
                }
            }
            Ok(())
        }
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => {
            check_arity(model_values)?;
            model
                .check_point(model_values)
                .map_err(|v| format!("the point claimed feasible is infeasible: {v:?}"))?;
            if let Some(bound) = dual_bound {
                // The tree's bound may trail the incumbent across the remaining
                // gap, but it may never cross it — a "bound" beyond the point in
                // hand is a contradiction, not a gap.
                let attained = obj.value_at(model_values);
                let crossed = match obj.sense {
                    Sense::Minimize => bound > &attained,
                    Sense::Maximize => bound < &attained,
                };
                if crossed {
                    return Err(format!(
                        "interrupted-tree dual bound {bound} crosses the incumbent value {attained}"
                    ));
                }
            }
            Ok(())
        }
        Outcome::Infeasible { cert, tree_cert } => {
            if let Some(cert) = cert {
                cert.verify(model)
                    .map_err(|e| format!("Farkas certificate does not verify: {e}"))?;
            }
            if let Some(tree_cert) = tree_cert {
                tree_cert
                    .verify(model)
                    .map_err(|e| format!("tree certificate does not verify: {e}"))?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// The single exit every verdict leaves a session through: re-validate the
/// witnesses, then apply the certificate policy. A verdict whose own witness
/// does not hold up is withheld, never returned.
fn finish(outcome: Outcome, model: &Model, obj: &SolvedObjective<'_>, opts: &SolveOpts) -> Outcome {
    let outcome = fail_closed_for_inexact(outcome, model);
    match validate_witnesses(&outcome, model, obj) {
        Ok(()) => apply_cert_policy(outcome, opts),
        Err(detail) => Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { detail },
        },
    }
}

/// FAIL-CLOSED BACKSTOP for models carrying inexact (rounded-`f64`) coefficients.
///
/// The whole search is re-adjudicated by [`validate_witnesses`] against the TRUE
/// model (its three gates — `check_point`, `value_at`, `cert.verify` — all read
/// the exact-rational side-store). Three verdict shapes escape that re-check
/// and so must be degraded HERE rather than trusted from a search that read
/// rounded coefficients for its pruning:
///
///   * a MILP `Optimal` — the certificate bounds only the LP dual, and for an
///     integral model `validate_witnesses` permits the dual bound to trail the
///     primal across the integrality gap, so a subtree wrongly fathomed on a
///     rounded coefficient could hide a better integer point. We keep the
///     (`check_point`-verified, true-value) incumbent as `Feasible` and DROP the
///     unprovable optimality claim. A continuous `Optimal` is fully re-proven
///     (dual bound must MEET the primal) and passes through.
///
///   * an `Infeasible` with NO certificate — `validate_witnesses` accepts a bare
///     infeasibility on trust. A certified one is re-verified against the true
///     model (and fails closed to `Unknown` there if the cert was built on
///     rounded coefficients), but a bare one has nothing to re-check, so we
///     decline it.
///
///   * a MILP `Unbounded` — the native integer search may reach it after
///     transformations and pruning over the rounded advice model, and this
///     outcome carries no ray certificate to replay against the true rationals.
///     (The exact continuous lane remains authoritative and passes through.)
///
/// For an all-`f64`-exact model this is a no-op (the guard is off), so every
/// existing instance is byte-identical.
fn fail_closed_for_inexact(outcome: Outcome, model: &Model) -> Outcome {
    if !model.has_inexact_coeffs() {
        return outcome;
    }
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } if model.has_integrality() => {
            // Keep the incumbent (re-checked by `validate_witnesses`), drop the
            // optimality claim we cannot certify over the true model.
            let _ = value;
            Outcome::Feasible {
                model_values,
                incumbent_only: true,
                dual_bound: None,
            }
        }
        Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        } => Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
        },
        Outcome::Unbounded if model.has_integrality() => Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
        },
        // A `Feasible` incumbent is re-checked by `check_point` (sound), but any
        // dual bound riding along was derived by the search from rounded `f64`
        // coefficients (NS / safe-dual bounds are valid only for the LP the
        // `f64` matrix denotes, which is the WRONG LP here) — so it is not a
        // rigorous bound on the true optimum. Drop it rather than present a
        // bound we cannot stand behind.
        Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: Some(_),
        } => Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: None,
        },
        other => other,
    }
}

/// An LP session: one continuous model, many objectives, warm re-solves, and
/// certificates on every verdict.
pub struct LpSession {
    model: Model,
    opts: SolveOpts,
    lp: ExactLp,
    /// Set when [`Self::narrow_col_bounds`] changes the model box: the
    /// persistent exact rim is rebuilt from the (narrowed) model before its
    /// next use, so its certificates reference the bounds the model states
    /// and never a stale-wide box. The per-solve float lane already rebuilds
    /// from the model, so it needs no such flag.
    lp_dirty: bool,
}

impl LpSession {
    /// Build a session over a continuous model.
    ///
    /// # Errors
    /// Rejects models with integral columns (`ModelError::Unsupported`) or
    /// invalid numbers.
    pub fn new(model: &Model, opts: &SolveOpts) -> Result<Self, MilpError> {
        model.validate().map_err(MilpError::Model)?;
        if model.has_integrality() {
            return Err(MilpError::Model(ModelError::Unsupported {
                reason: "LpSession requires a continuous model; use BabSession for MILP".to_owned(),
            }));
        }
        Ok(Self {
            model: model.clone(),
            opts: opts.clone(),
            lp: ExactLp::new(model),
            lp_dirty: false,
        })
    }

    /// Optimize the single-column objective `x_col` in `sense`.
    /// The basis persists across calls (warm re-solve).
    pub fn optimize(&mut self, col: Col, sense: Sense) -> Result<Outcome, MilpError> {
        if col.index() >= self.model.num_cols() {
            return Err(MilpError::Session {
                message: format!("column {} out of range", col.index()),
            });
        }
        // Single-column objective (coefficient 1.0) — never the model's own, so
        // no exact-objective override even if the model carries inexact obj
        // coefficients.
        Ok(self.optimize_linear(&[(col.0, 1.0)], sense, 0.0, None))
    }

    /// Optimize the model's own objective (coefficients, offset, sense).
    pub fn optimize_model_objective(&mut self) -> Result<Outcome, MilpError> {
        let coeffs: Vec<(u32, f64)> = (0..self.model.num_cols())
            .map(|i| (i as u32, self.model.obj_coeff(Col(i as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let exact = self.model_objective_exact(&coeffs);
        Ok(self.optimize_linear(
            &coeffs,
            self.model.sense(),
            self.model.objective_offset(),
            exact,
        ))
    }

    /// The TRUE rational form of the model's own objective `coeffs`, when the
    /// model carries inexact obj coefficients; `None` on the exact fast path.
    fn model_objective_exact(&self, coeffs: &[(u32, f64)]) -> Option<ExactObjective> {
        if !self.model.has_inexact_coeffs() {
            return None;
        }
        Some((
            coeffs
                .iter()
                .map(|&(c, a)| (c, self.model.obj_coeff_exact_at(c, a)))
                .collect(),
            self.model.obj_offset_exact(),
        ))
    }

    /// Tighten a column's bounds: `(minimize x_col, maximize x_col)`.
    pub fn tighten_col_bounds(&mut self, col: Col) -> Result<(Outcome, Outcome), MilpError> {
        let lo = self.optimize(col, Sense::Minimize)?;
        let hi = self.optimize(col, Sense::Maximize)?;
        Ok((lo, hi))
    }

    /// Search in `f64`, then have the exact lane adjudicate the proposed basis.
    ///
    /// `None` means "no verdict from here" and costs only the wasted search —
    /// the caller falls through to the exact rim. Note what is NOT trusted: a
    /// float `PrimalInfeasible` or `Unbounded` is a numerical opinion, not a
    /// proof, so those fall through too rather than becoming verdicts. Only an
    /// optimal basis that survives exact replay is allowed to speak.
    fn try_float_lane(&self, coeffs: &[(u32, f64)], sense: Sense, offset: f64) -> Option<Outcome> {
        if !float_lane_enabled() {
            return None;
        }
        let mut lp = FloatLp::from_model(&self.model, coeffs, sense)?;
        lp.plain_cold = true; // session lane: keep the classic measured path (see `FloatLp::plain_cold`)
        let deadline = self.opts.effective_deadline(Instant::now());
        let cand = lp.solve(deadline);
        // A memory DECLINE is reportable in its own right: short-circuit the
        // exact rim (a denser factorization on the same shape would only OOM
        // harder) and name the reason. This must precede the generic
        // `!= Optimal → None` fall-through below.
        if cand.status == SimplexStatus::OutOfMemory {
            return Some(Outcome::Unknown {
                reason: UnknownReason::MemoryLimit,
            });
        }
        if cand.status != SimplexStatus::Optimal {
            return None;
        }
        let proven = certify(&self.model, &lp, &cand)?;
        let offset = exact(offset).unwrap_or_else(BigRational::zero);
        Some(Outcome::Optimal {
            value: proven.value + offset,
            model_values: proven.values,
            cert: Some(proven.cert),
        })
    }

    fn optimize_linear(
        &mut self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        model_obj_exact: Option<ExactObjective>,
    ) -> Outcome {
        let solved = SolvedObjective {
            coeffs,
            sense,
            offset,
            exact: model_obj_exact.clone(),
        };
        // The float certificate lane is built from ROUNDED `f64` coefficients;
        // on an inexact model its certificate would bound the wrong linear form.
        // Decline it and let the exact rim (which reads the true rationals)
        // answer. The exact-coeff fast path is unchanged.
        if !self.model.has_inexact_coeffs() {
            if let Some(fast) = self.try_float_lane(coeffs, sense, offset) {
                return finish(fast, &self.model, &solved, &self.opts);
            }
        }

        // The exact rim is the fallback authority; a narrowed box invalidates
        // its persistent state, so rebuild it from the model first. No
        // narrowing ⇒ warm re-solve, as before.
        if self.lp_dirty {
            self.lp = ExactLp::new(&self.model);
            self.lp_dirty = false;
        }
        let budget = budget_for(&self.model, &self.opts);
        // On an inexact model the exact rim minimizes the TRUE objective from
        // the side-store, and its certificate names that same true objective.
        let obj: Vec<(u32, Rational)> = match &model_obj_exact {
            Some((c, _)) => {
                let mut v: Vec<(u32, Rational)> = c
                    .iter()
                    .map(|(i, r)| (*i, Rational::from_big(r.clone())))
                    .collect();
                v.sort_unstable_by_key(|&(i, _)| i);
                v
            }
            None => exact_obj(coeffs),
        };
        // Minimize form: negate for Maximize, un-negate the optimum below.
        let solve_obj: Vec<(u32, Rational)> = match sense {
            Sense::Minimize => obj.clone(),
            Sense::Maximize => obj.iter().map(|(c, a)| (*c, -a.clone())).collect(),
        };
        let outcome = match self.lp.minimize(&solve_obj, &budget) {
            LpOptimum::Optimal { value, multipliers } => {
                let bound = match sense {
                    Sense::Minimize => value,
                    Sense::Maximize => -value,
                };
                let offset = match &model_obj_exact {
                    Some((_, o)) => o.clone(),
                    None => exact(offset).unwrap_or_else(BigRational::zero),
                };
                let cert = OptimalityCertificate {
                    sense,
                    objective: obj.iter().map(|(c, a)| (*c, a.to_big())).collect(),
                    bound: bound.clone(),
                    multipliers,
                };
                debug_assert!(
                    cert.verify(&self.model).is_ok(),
                    "exact-lane certificate must verify"
                );
                Outcome::Optimal {
                    value: bound + offset,
                    model_values: self.lp.structural_values(),
                    cert: Some(cert),
                }
            }
            LpOptimum::Unbounded => Outcome::Unbounded,
            LpOptimum::Infeasible(cert) => {
                debug_assert!(
                    cert.verify(&self.model).is_ok(),
                    "exact-lane Farkas certificate must verify"
                );
                Outcome::Infeasible {
                    cert: Some(cert),
                    tree_cert: None,
                }
            }
            LpOptimum::Unknown(reason) => Outcome::Unknown { reason },
        };
        finish(outcome, &self.model, &solved, &self.opts)
    }

    /// A rigorous bound on `col` in `sense`.
    ///
    /// First tries the **Neumaier–Shcherbina** lane: the float simplex finds a
    /// dual vector, then [`crate::ns`] turns it into a safe bound with directed
    /// `f64` rounding, avoiding an exact-rational solve when possible. The NS
    /// bound is a true bound for the exact LP *no matter how wrong the float
    /// dual is* (soundness never rests on the dual). If NS cannot produce a finite
    /// bound (an unbounded direction, an infinite bound side meeting a
    /// wrong-signed reduced cost, or the float lane not settling), it falls
    /// back to the exact rim, whose `optimize` optimum is exact hence rigorous.
    /// Infeasible / Unbounded / Unknown pass through unchanged; never a
    /// non-rigorous answer.
    ///
    /// # Errors
    /// Propagates session errors (e.g. an out-of-range column).
    pub fn rigorous_bound(&mut self, col: Col, sense: Sense) -> Result<Outcome, MilpError> {
        if col.index() >= self.model.num_cols() {
            return Err(MilpError::Session {
                message: format!("column {} out of range", col.index()),
            });
        }
        if let Some(dual_bound) = self.ns_bound(col, sense) {
            return Ok(Outcome::Bound {
                dual_bound,
                rigorous: true,
            });
        }
        Ok(match self.optimize(col, sense)? {
            Outcome::Optimal { value, .. } => Outcome::Bound {
                dual_bound: value,
                rigorous: true,
            },
            other => other,
        })
    }

    /// The Neumaier–Shcherbina safe bound on `col` in `sense`, or `None` to
    /// defer to the exact rim. Runs the float lane once for a dual vector, then
    /// evaluates the weak-duality bound (crate::ns) with directed rounding.
    ///
    /// To bound `max x_col` we bound `min (−x_col)` and negate. Robust to the
    /// float dual's sign convention: `y` and `−y` are BOTH valid duals for the
    /// NS argument (soundness is dual-independent), so the tighter (max) of the
    /// two bounds is taken — the correct-convention one wins automatically.
    fn ns_bound(&self, col: Col, sense: Sense) -> Option<BigRational> {
        // NS evaluates the `f64` matrix with directed rounding.  That encloses
        // the dyadic values represented by those f64s, but it cannot enclose a
        // different true rational held in the model's side-store.  Calling the
        // result rigorous in that case can over-tighten OBBT and delete a true
        // feasible point, so side-store models go straight to the exact rim.
        if self.model.has_inexact_coeffs() || !float_lane_enabled() {
            return None;
        }
        // Minimize form: `min (coeff · x_col)`; coeff = −1 encodes maximize.
        let (coeff, flip) = match sense {
            Sense::Minimize => (1.0_f64, false),
            Sense::Maximize => (-1.0_f64, true),
        };
        let mut lp = FloatLp::from_model(&self.model, &[(col.0, coeff)], Sense::Minimize)?;
        lp.plain_cold = true; // session lane: keep the classic measured path (see `FloatLp::plain_cold`)
        let cand = lp.solve(self.opts.effective_deadline(Instant::now()));
        if cand.status != SimplexStatus::Optimal {
            return None;
        }
        let mut obj = vec![0.0_f64; self.model.num_cols()];
        obj[col.index()] = coeff;
        let neg_y: Vec<f64> = cand.duals.iter().map(|d| -d).collect();
        let best = [
            crate::ns::rigorous_lower_bound(&self.model, &obj, &cand.duals),
            crate::ns::rigorous_lower_bound(&self.model, &obj, &neg_y),
        ]
        .into_iter()
        .flatten()
        .fold(f64::NEG_INFINITY, f64::max);
        if !best.is_finite() {
            return None;
        }
        // `best` bounds `min (coeff·x)` from below; un-negate for maximize.
        exact(if flip { -best } else { best })
    }

    /// Tighten a column's bounds with RIGOROUS bounds: `(min, max)`.
    ///
    /// # Errors
    /// Propagates session errors.
    pub fn tighten_col_bounds_rigorous(
        &mut self,
        col: Col,
    ) -> Result<(Outcome, Outcome), MilpError> {
        let lo = self.rigorous_bound(col, Sense::Minimize)?;
        let hi = self.rigorous_bound(col, Sense::Maximize)?;
        Ok((lo, hi))
    }

    /// Intersect `[lower, upper]` into `col`'s box (the OBBT commit
    /// primitive). Returns whether the box actually shrank.
    ///
    /// SOUND ONLY for PROVEN bounds: the caller must pass values the true
    /// feasible region already satisfies (a rigorous min/max), because the
    /// method trusts them and narrows the model. It only ever intersects —
    /// a widening request, a NaN, an out-of-range column, a tightening-side
    /// infinity, or an intersection that would cross leaves the box
    /// untouched and returns `false`. The per-solve float lane rebuilds from
    /// the model automatically; the persistent exact rim is marked for
    /// rebuild.
    pub fn narrow_col_bounds(&mut self, col: Col, lower: f64, upper: f64) -> bool {
        if col.index() >= self.model.num_cols() || lower.is_nan() || upper.is_nan() {
            return false;
        }
        let (cur_lb, cur_ub) = self.model.col_bounds(col);
        // `max`/`min` with an infinite input is a no-op on that side.
        let new_lb = cur_lb.max(lower);
        let new_ub = cur_ub.min(upper);
        // A tightening-side infinity would empty the box: refuse it.
        if new_lb == f64::INFINITY || new_ub == f64::NEG_INFINITY {
            return false;
        }
        // Only ever tighten, never cross.
        if new_lb > new_ub || (new_lb <= cur_lb && new_ub >= cur_ub) {
            return false;
        }
        self.model.set_col_bounds(col, new_lb, new_ub);
        self.lp_dirty = true;
        true
    }

    /// Optimization-based bound tightening over `cols`: a within-session
    /// fixpoint that rigorously bounds each column and commits the tighter
    /// box, so coupled columns tighten each other across rounds. Every
    /// committed bound is a proven rigorous bound outward-rounded to f64 —
    /// the tightened model has the same feasible set as the original.
    /// Deterministic; fail-closed (`Unknown` / `Unbounded` / non-rigorous
    /// results tighten nothing).
    ///
    /// # Errors
    /// Propagates session errors (e.g. an out-of-range column).
    pub fn obbt(&mut self, cols: &[Col], opts: &ObbtOpts) -> Result<ObbtReport, MilpError> {
        for &c in cols {
            if c.index() >= self.model.num_cols() {
                return Err(MilpError::Session {
                    message: format!("column {} out of range", c.index()),
                });
            }
        }
        let mut ever_tightened = vec![false; cols.len()];
        let mut rounds = 0usize;
        let mut infeasible = false;
        'rounds: for _ in 0..opts.max_rounds {
            rounds += 1;
            let mut improved = false;
            for (i, &col) in cols.iter().enumerate() {
                let (lb0, ub0) = self.model.col_bounds(col);
                if lb0 == ub0 {
                    continue; // already fixed
                }
                let mut new_lb = lb0;
                match self.rigorous_bound(col, Sense::Minimize)? {
                    Outcome::Bound {
                        dual_bound,
                        rigorous: true,
                    } => {
                        if let Some(f) = floor_f64(&dual_bound) {
                            new_lb = new_lb.max(f);
                        }
                    }
                    Outcome::Infeasible { .. } => {
                        infeasible = true;
                        break 'rounds;
                    }
                    _ => {}
                }
                let mut new_ub = ub0;
                match self.rigorous_bound(col, Sense::Maximize)? {
                    Outcome::Bound {
                        dual_bound,
                        rigorous: true,
                    } => {
                        if let Some(f) = ceil_f64(&dual_bound) {
                            new_ub = new_ub.min(f);
                        }
                    }
                    Outcome::Infeasible { .. } => {
                        infeasible = true;
                        break 'rounds;
                    }
                    _ => {}
                }
                if self.narrow_col_bounds(col, new_lb, new_ub) {
                    ever_tightened[i] = true;
                    if (new_lb - lb0) > opts.tol || (ub0 - new_ub) > opts.tol {
                        improved = true;
                    }
                }
            }
            if !improved {
                break;
            }
        }
        Ok(ObbtReport {
            bounds: cols.iter().map(|&c| self.model.col_bounds(c)).collect(),
            rounds,
            tightened: ever_tightened.iter().filter(|&&t| t).count(),
            infeasible,
        })
    }

    /// Harvest a certified valid inequality on `coeffs·x`.
    ///
    /// Solves the linear objective and, when it has a finite optimum, returns
    /// the [`crate::cert::CertifiedRow`] the exact dual proof establishes:
    /// `coeffs·x >= optimum` for Minimize (or `<= optimum`, re-oriented, for
    /// Maximize). Re-verified before it is handed out; anything unbounded,
    /// infeasible, uncertified, or non-finite yields `None` (fail-closed).
    pub fn harvest_cut(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
    ) -> Option<crate::cert::CertifiedRow> {
        if coeffs
            .iter()
            .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }
        let u32_coeffs: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        match self.optimize_linear(&u32_coeffs, sense, 0.0, None) {
            Outcome::Optimal {
                cert: Some(cert), ..
            } => {
                let row = cert.into_certified_row();
                row.verify(&self.model).ok().map(|()| row)
            }
            _ => None,
        }
    }

    /// The session's current bounds for `col` (post-OBBT read-back).
    #[must_use]
    pub fn col_bounds(&self, col: Col) -> (f64, f64) {
        self.model.col_bounds(col)
    }
}

/// The largest f64 `≤ r` (round toward −∞) — the exact→f64 commit of a
/// rigorous LOWER bound: weakening it outward excludes no feasible point.
/// `None` on overflow to non-finite (commit nothing; fail closed).
fn floor_f64(r: &BigRational) -> Option<f64> {
    use num_traits::ToPrimitive;
    let f = r.to_f64()?;
    if !f.is_finite() {
        return None;
    }
    match BigRational::from_float(f) {
        Some(exact_f) if &exact_f > r => Some(f.next_down()),
        _ => Some(f),
    }
}

/// The smallest f64 `≥ r` (round toward +∞); the upper-bound mirror.
fn ceil_f64(r: &BigRational) -> Option<f64> {
    use num_traits::ToPrimitive;
    let f = r.to_f64()?;
    if !f.is_finite() {
        return None;
    }
    match BigRational::from_float(f) {
        Some(exact_f) if &exact_f < r => Some(f.next_up()),
        _ => Some(f),
    }
}

/// Tuning for [`LpSession::obbt`].
#[derive(Debug, Clone, Copy)]
pub struct ObbtOpts {
    /// Maximum fixpoint rounds. Each round is one rigorous min+max per
    /// column; the loop also stops early once a round tightens nothing.
    pub max_rounds: usize,
    /// A round counts as progress only if some column's box shrank by more
    /// than this (guards against infinite chatter on tiny float steps).
    pub tol: f64,
}

impl Default for ObbtOpts {
    fn default() -> Self {
        Self {
            max_rounds: 4,
            tol: 1e-9,
        }
    }
}

/// What one [`LpSession::obbt`] run produced.
#[derive(Debug, Clone)]
pub struct ObbtReport {
    /// Final `(lb, ub)` per input column, in the order `cols` was given.
    pub bounds: Vec<(f64, f64)>,
    /// Rounds actually run (≤ `max_rounds`).
    pub rounds: usize,
    /// How many columns had their box shrink at least once.
    pub tightened: usize,
    /// Set when a rigorous solve proved the whole model infeasible; the
    /// per-column `bounds` are then not meaningful.
    pub infeasible: bool,
}

/// One scope frame of a [`BabSession`]: what to restore on `pop`.
struct ScopeFrame {
    rows_len: usize,
    saved_bounds: Vec<(usize, f64, f64)>,
}

/// The MILP lane behind a [`BabSession`].
enum MilpLane {
    /// Native branch-and-bound over the float LP core.
    Native,
    /// ay-dpll typed-Solver fallback, forced with `AY_MILP_SMT=1`.
    #[cfg(feature = "smt")]
    Smt(Box<crate::smt::SmtMilp>),
    /// Exact rim (continuous models).
    Exact,
}

/// Whether a MILP goes down the old ay-dpll lowering instead of the native
/// branch-and-bound. The A/B switch the native lane is measured against.
fn smt_lane_forced() -> bool {
    static FORCED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FORCED.get_or_init(|| std::env::var_os("AY_MILP_SMT").is_some())
}

/// A MILP session with scoped `fix_col`/`add_row`, feasibility and
/// optimization checks, cut harvesting (native engine only).
pub struct BabSession {
    model: Model,
    opts: SolveOpts,
    lane: MilpLane,
    scopes: Vec<ScopeFrame>,
    /// Advice-only incumbent seeds and branch hints for the native engine.
    incumbent_seed: Option<Vec<f64>>,
    branch_hints: Vec<Col>,
}

impl BabSession {
    /// Build a session over `model`, TAKING OWNERSHIP of it (Lever A).
    ///
    /// The session becomes the single owner of this f64 model; read it back with
    /// [`Self::model`] instead of keeping a separate copy alive. On a large
    /// NN-verification MILP (cifar100's 44M-nnz class) a full-matrix f64 copy is
    /// ~0.71GB, and the old `&Model` signature forced the caller to hold its own
    /// copy alongside the session's clone at the root-LP memory peak. Taking
    /// `model` by value removes that redundant copy — byte-identical to every
    /// verdict: the model's bytes are untouched, only its ownership moves.
    pub fn new(model: Model, opts: &SolveOpts) -> Result<Self, MilpError> {
        model.validate().map_err(MilpError::Model)?;
        let lane = if model.has_integrality() {
            #[cfg(feature = "smt")]
            {
                if smt_lane_forced() {
                    MilpLane::Smt(Box::new(crate::smt::SmtMilp::new(&model, opts)?))
                } else {
                    MilpLane::Native
                }
            }
            #[cfg(not(feature = "smt"))]
            {
                MilpLane::Native
            }
        } else {
            MilpLane::Exact
        };
        Ok(Self {
            model,
            opts: opts.clone(),
            lane,
            scopes: Vec::new(),
            incumbent_seed: None,
            branch_hints: Vec::new(),
        })
    }

    /// The model this session owns (Lever A accessor). Callers that used to keep
    /// their own copy of the pre-`new` model — e.g. to compute the objective value
    /// of an outcome — read it here instead, so only ONE f64 matrix is resident.
    #[must_use]
    pub fn model(&self) -> &Model {
        &self.model
    }

    /// Open a scope. `fix_col`/`add_row` inside it are undone by [`Self::pop`].
    pub fn push(&mut self) -> Result<(), MilpError> {
        #[cfg(feature = "smt")]
        if let MilpLane::Smt(smt) = &mut self.lane {
            smt.push()?;
        }
        self.scopes.push(ScopeFrame {
            rows_len: self.model.num_rows(),
            saved_bounds: Vec::new(),
        });
        Ok(())
    }

    /// Close the innermost scope.
    pub fn pop(&mut self) -> Result<(), MilpError> {
        let frame = self.scopes.pop().ok_or_else(|| MilpError::Session {
            message: "pop at scope depth 0".to_owned(),
        })?;
        #[cfg(feature = "smt")]
        if let MilpLane::Smt(smt) = &mut self.lane {
            smt.pop()?;
        }
        self.model.rows.truncate(frame.rows_len);
        for (col, lb, ub) in frame.saved_bounds.into_iter().rev() {
            self.model.cols[col].lb = lb;
            self.model.cols[col].ub = ub;
        }
        Ok(())
    }

    /// Fix a column to `value` in the current scope (the phase-split
    /// primitive: a dual-feasible warm child in the native engine).
    ///
    /// # Panics
    /// Panics if `value` is NaN.
    pub fn fix_col(&mut self, col: Col, value: f64) -> Result<(), MilpError> {
        assert!(!value.is_nan(), "fix_col: NaN value");
        if col.index() >= self.model.num_cols() {
            return Err(MilpError::Session {
                message: format!("column {} out of range", col.index()),
            });
        }
        if let Some(frame) = self.scopes.last_mut() {
            let (lb, ub) = self.model.col_bounds(col);
            frame.saved_bounds.push((col.index(), lb, ub));
        }
        self.model.fix_col(col, value);
        #[cfg(feature = "smt")]
        if let MilpLane::Smt(smt) = &mut self.lane {
            smt.fix_col(col, value)?;
        }
        Ok(())
    }

    /// Add a row `lb <= coeffs·x <= ub` in the current scope (lazy cuts).
    pub fn add_row(&mut self, lb: f64, ub: f64, coeffs: &[(Col, f64)]) -> Result<Row, MilpError> {
        let row = self.model.add_row(lb, ub, coeffs);
        #[cfg(feature = "smt")]
        if let MilpLane::Smt(smt) = &mut self.lane {
            let (rc, rlb, rub) = self.model.row(row);
            let rc = rc.to_vec();
            smt.assert_row_facts(&rc, rlb, rub)?;
        }
        Ok(row)
    }

    /// Seed a candidate incumbent from an external heuristic. Advice only:
    /// it never changes verdicts, only (in the native engine) search order.
    pub fn seed_incumbent(&mut self, values: &[f64]) {
        self.incumbent_seed = Some(values.to_vec());
    }

    /// Suggest a branching order for binary columns. Advice only: valid,
    /// currently branchable hints break ties between equally-scored native
    /// branch candidates; stronger measured/structural choices still win.
    /// Stale, fixed, non-binary, and duplicate handles are ignored.
    pub fn hint_branch_order(&mut self, cols: &[Col]) {
        self.branch_hints = cols.to_vec();
    }

    /// Solve the current scope: feasibility when the model carries no
    /// objective, optimization otherwise.
    ///
    /// "Carries no objective" is [`Model::has_objective`], not "every
    /// coefficient is zero". An explicit all-zero objective is an
    /// optimization problem whose optimum is the offset, and reading the
    /// distinction off the coefficients instead made this lane answer
    /// `Feasible` where [`LpSession`] answered `Optimal { value: 0 }` on the
    /// very same model.
    pub fn check(&mut self) -> Result<Outcome, MilpError> {
        // ONE deadline, fixed here, for every lane this call touches.
        //
        // `SolveOpts::time_limit` is a DURATION, and `effective_deadline(now)` turns it into an
        // instant relative to whenever it happens to be asked. Each lane asked separately -- so
        // when branch-and-bound spent the whole limit and handed a model it could not settle to
        // the smt lane, that lane started a FRESH clock. A caller who asked for 20 seconds got
        // 20 from one lane and 20 more from the next. On air03 (10,757 binaries, which the smt
        // lane tries to enumerate) a 10-second limit ran past two minutes.
        //
        // Pinning the deadline to an absolute instant makes the limit mean what it says: the
        // lanes now SHARE it, and a lane handed an already-spent budget declines rather than
        // starting over.
        let started = Instant::now();
        self.opts.deadline = self.opts.effective_deadline(started);
        self.opts.time_limit = None;
        let expired = |o: &SolveOpts| o.deadline.is_some_and(|d| Instant::now() >= d);

        let objective: Vec<(u32, f64)> = (0..self.model.num_cols())
            .map(|i| (i as u32, self.model.obj_coeff(Col(i as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let has_objective = self.model.has_objective();
        // TRUE rational objective for the re-derivation gate / exact rim, present
        // only when the model carries inexact obj coefficients.
        let exact_objective: Option<ExactObjective> = if self.model.has_inexact_coeffs() {
            Some((
                objective
                    .iter()
                    .map(|&(c, a)| (c, self.model.obj_coeff_exact_at(c, a)))
                    .collect(),
                self.model.obj_offset_exact(),
            ))
        } else {
            None
        };
        // MARGIN REFRAME (opt-in via `Model::mark_margin_row`). When the model
        // names a band-violation row in an objective-≡0 feasibility problem,
        // solve the equivalent margin OPTIMIZATION so dual-bound pruning wakes
        // up, then map the reframed optimum back to the ORIGINAL feasibility
        // verdict. `reframe` DECLINES (returns `None`, and the plain lanes below
        // run unchanged) whenever no margin is named, the shape does not fit, or
        // the kill switch is set — so every model without a margin mark is
        // byte-identical. The mapped verdict still leaves through the shared
        // `finish` gate, which re-validates its witness against THIS model.
        if let Some(reframed) = crate::margin::reframe(&self.model, &self.opts) {
            let solved = SolvedObjective {
                coeffs: &objective,
                sense: self.model.sense(),
                offset: self.model.objective_offset(),
                exact: exact_objective,
            };
            return Ok(finish(reframed.verdict, &self.model, &solved, &self.opts));
        }
        let outcome = match &mut self.lane {
            MilpLane::Native => {
                // Native branch-and-bound is the FAST path, not the only one. It
                // is sound but not yet complete (no cuts, no presolve, and it
                // declines rather than guesses on an unbounded relaxation), so a
                // node it cannot settle is handed to the lane that always finishes
                // rather than surfaced as `Unknown`. Fast where it works, correct
                // everywhere — the same bargain the float LP lane strikes with the
                // exact rim.
                // A session-supplied incumbent seed (advice only — exactly re-checked
                // inside; a bad seed is dropped, never believed) reaches the tree here.
                let mut raw = match self.incumbent_seed.as_deref() {
                    Some(seed) => crate::bab::solve_milp_seeded(
                        &self.model,
                        &self.opts,
                        seed,
                        &self.branch_hints,
                    ),
                    None if self.branch_hints.is_empty() => {
                        crate::bab::solve_milp(&self.model, &self.opts)
                    }
                    None => {
                        crate::bab::solve_milp_hinted(&self.model, &self.opts, &self.branch_hints)
                    }
                };
                #[cfg(feature = "smt")]
                if raw.is_unknown() && !expired(&self.opts) && self.smt_fallback_within_reach() {
                    let mut smt = crate::smt::SmtMilp::new(&self.model, &self.opts)?;
                    raw = if has_objective {
                        smt.optimize(&self.model, &self.opts, &objective, self.model.sense())?
                    } else {
                        smt.check_feasible(&self.opts)?
                    };
                }
                let raw = if has_objective {
                    raw
                } else {
                    // No objective was set, so the caller asked "is there a
                    // point?", not "which is best?". Branch-and-bound answers the
                    // latter by construction (over the zero objective, the first
                    // integer-feasible leaf is optimal), so report what was
                    // actually asked for rather than a stronger-sounding verdict
                    // the caller did not request.
                    match raw {
                        Outcome::Optimal { model_values, .. } => Outcome::Feasible {
                            model_values,
                            incumbent_only: false,
                            dual_bound: None,
                        },
                        other => other,
                    }
                };
                // Same LP-relaxation Farkas enrichment the smt lane gets: when the
                // relaxation alone is already contradictory, that witness is valid
                // for the MILP a fortiori. The root Farkas remains the PREFERRED
                // evidence; the engine's whole-tree certificate (when captured)
                // rides along either way and is what certifies the case-split-only
                // infeasibilities the relaxation cannot see.
                match raw {
                    Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    } => {
                        // Bounded post-verdict certificate pass.
                        // Only when NO evidence exists yet: with a tree
                        // certificate in hand the verdict is already
                        // independently checkable, and this exact root
                        // re-solve — on a model whose relaxation is typically
                        // FEASIBLE (that is why the tree had to split) — is a
                        // BigRational phase A that can consume the remaining
                        // budget without finding root evidence. Hence the
                        // bounded grace: see `cert_budget_native`.
                        let budget = cert_budget_native(&self.model, &self.opts);
                        let mut lp = ExactLp::new(&self.model);
                        match lp.make_feasible(&budget) {
                            LpFeasibility::Infeasible(cert) => Outcome::Infeasible {
                                cert: Some(cert),
                                tree_cert: None,
                            },
                            _ => Outcome::Infeasible {
                                cert: None,
                                tree_cert: None,
                            },
                        }
                    }
                    other => other,
                }
            }
            #[cfg(feature = "smt")]
            MilpLane::Smt(smt) => {
                let raw = if has_objective {
                    let raw =
                        smt.optimize(&self.model, &self.opts, &objective, self.model.sense())?;
                    // The smt lane reports the pure linear optimum; fold in
                    // the offset here.
                    match raw {
                        Outcome::Optimal {
                            value,
                            model_values,
                            cert,
                        } => {
                            let offset = self.model.obj_offset_exact();
                            Outcome::Optimal {
                                value: value + offset,
                                model_values,
                                cert,
                            }
                        }
                        other => other,
                    }
                } else {
                    smt.check_feasible(&self.opts)?
                };
                // Enrich bare infeasibility with an LP-relaxation Farkas
                // certificate when the relaxation is already contradictory
                // (valid for the MILP a fortiori). Skipped when a tree
                // certificate already evidences the verdict — same reasoning
                // as the native lane above.
                match raw {
                    Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    } => {
                        // Bounded post-verdict certificate pass.
                        let budget = cert_budget_for(&self.model, &self.opts);
                        let mut lp = ExactLp::new(&self.model);
                        match lp.make_feasible(&budget) {
                            LpFeasibility::Infeasible(cert) => {
                                debug_assert!(cert.verify(&self.model).is_ok());
                                Outcome::Infeasible {
                                    cert: Some(cert),
                                    tree_cert: None,
                                }
                            }
                            _ => Outcome::Infeasible {
                                cert: None,
                                tree_cert: None,
                            },
                        }
                    }
                    other => other,
                }
            }
            MilpLane::Exact => {
                let budget = budget_for(&self.model, &self.opts);
                let mut lp = ExactLp::new(&self.model);
                if has_objective {
                    // On an inexact model the exact rim minimizes the TRUE
                    // objective from the side-store and names it in the cert.
                    let obj: Vec<(u32, Rational)> = match &exact_objective {
                        Some((c, _)) => {
                            let mut v: Vec<(u32, Rational)> = c
                                .iter()
                                .map(|(i, r)| (*i, Rational::from_big(r.clone())))
                                .collect();
                            v.sort_unstable_by_key(|&(i, _)| i);
                            v
                        }
                        None => exact_obj(&objective),
                    };
                    let sense = self.model.sense();
                    let solve_obj: Vec<(u32, Rational)> = match sense {
                        Sense::Minimize => obj.clone(),
                        Sense::Maximize => obj.iter().map(|(c, a)| (*c, -a.clone())).collect(),
                    };
                    match lp.minimize(&solve_obj, &budget) {
                        LpOptimum::Optimal { value, multipliers } => {
                            let bound = match sense {
                                Sense::Minimize => value,
                                Sense::Maximize => -value,
                            };
                            let offset = match &exact_objective {
                                Some((_, o)) => o.clone(),
                                None => self.model.obj_offset_exact(),
                            };
                            let cert = OptimalityCertificate {
                                sense,
                                objective: obj.iter().map(|(c, a)| (*c, a.to_big())).collect(),
                                bound: bound.clone(),
                                multipliers,
                            };
                            debug_assert!(cert.verify(&self.model).is_ok());
                            Outcome::Optimal {
                                value: bound + offset,
                                model_values: lp.structural_values(),
                                cert: Some(cert),
                            }
                        }
                        LpOptimum::Unbounded => Outcome::Unbounded,
                        LpOptimum::Infeasible(cert) => Outcome::Infeasible {
                            cert: Some(cert),
                            tree_cert: None,
                        },
                        LpOptimum::Unknown(reason) => Outcome::Unknown { reason },
                    }
                } else {
                    match lp.make_feasible(&budget) {
                        LpFeasibility::Feasible => Outcome::Feasible {
                            model_values: lp.structural_values(),
                            incumbent_only: false,
                            dual_bound: None,
                        },
                        LpFeasibility::Infeasible(cert) => Outcome::Infeasible {
                            cert: Some(cert),
                            tree_cert: None,
                        },
                        LpFeasibility::Unknown(reason) => Outcome::Unknown { reason },
                    }
                }
            }
        };
        let solved = SolvedObjective {
            coeffs: &objective,
            sense: self.model.sense(),
            offset: self.model.objective_offset(),
            exact: exact_objective,
        };
        Ok(finish(outcome, &self.model, &solved, &self.opts))
    }

    /// Decide whether the exact SMT fallback can plausibly respect the caller's
    /// deadline. The lane enumerates integer branches over an exact-rational
    /// LRA tableau, and its wall enforcement is iteration-granular. Under a
    /// finite deadline it is entered only when the model is small enough and
    /// enough budget remains for one slice; otherwise the session preserves
    /// the native lane's `Unknown`. Without a deadline the fallback remains
    /// available unconditionally.
    #[cfg(feature = "smt")]
    fn smt_fallback_within_reach(&self) -> bool {
        /// Integer-column ceiling for entering the enumeration lane under a
        /// deadline. Larger models remain on the native path.
        const SMT_FALLBACK_MAX_INTS: usize = 1_024;
        /// Remaining-budget FLOOR for entering the enumeration lane, in
        /// seconds (`AY_MILP_SMT_MIN_BUDGET` overrides). The column ceiling
        /// alone does not honor the cap: a timing-out branch-and-bound
        /// can return with its finalization reserve still on the clock, so
        /// "not yet expired" at the call site can mean a sliver. Entering
        /// the BigRational enumeration with a sliver cannot reliably answer
        /// inside the cap because its first inner phase runs to iteration
        /// granularity. Declining here returns the honest `Unknown` at the cap;
        /// it cannot change a decided verdict.
        const SMT_FALLBACK_MIN_BUDGET_SECS: f64 = 5.0;
        if self.opts.deadline.is_none() && self.opts.time_limit.is_none() {
            return true;
        }
        let floor = std::env::var("AY_MILP_SMT_MIN_BUDGET")
            .ok()
            .and_then(|v| v.parse::<f64>().ok())
            .filter(|s| s.is_finite() && *s >= 0.0)
            .unwrap_or(SMT_FALLBACK_MIN_BUDGET_SECS);
        let now = Instant::now();
        if self
            .opts
            .effective_deadline(now)
            .is_some_and(|d| d.saturating_duration_since(now) < Duration::from_secs_f64(floor))
        {
            return false;
        }
        let ints = (0..self.model.num_cols())
            .filter(|&j| self.model.col_kind(Col(j as u32)).is_integral())
            .count();
        ints <= SMT_FALLBACK_MAX_INTS
    }

    /// Harvest certified cut rows discovered by the last `check`.
    ///
    /// Exact-only paths do not emit cuts; the native branch-and-cut engine may
    /// populate this collection.
    pub fn harvest_cuts(&mut self) -> Vec<crate::cert::CertifiedRow> {
        Vec::new()
    }

    /// The stored incumbent seed (advice; native engine).
    #[must_use]
    pub fn incumbent_seed(&self) -> Option<&[f64]> {
        self.incumbent_seed.as_deref()
    }

    /// The stored branch hints (advice; native engine).
    #[must_use]
    pub fn branch_hints(&self) -> &[Col] {
        &self.branch_hints
    }
}

#[cfg(test)]
mod node_warm_tests {
    use super::*;

    fn binary_model() -> Model {
        let mut model = Model::new();
        let _ = model.add_binary_col();
        model
    }

    #[test]
    fn node_warm_limit_is_isolated_between_sessions() {
        let short_limit = Duration::from_millis(10);
        let long_limit = Duration::from_secs(10);
        let short_opts = SolveOpts::new().with_node_warm_time_limit(Some(short_limit));
        let long_opts = SolveOpts::new().with_node_warm_time_limit(Some(long_limit));

        let short = BabSession::new(binary_model(), &short_opts).expect("short-cap session");
        let uncapped =
            BabSession::new(binary_model(), &SolveOpts::new()).expect("default uncapped session");
        let long = BabSession::new(binary_model(), &long_opts).expect("long-cap session");

        assert_eq!(short.opts.node_warm_time_limit, Some(short_limit));
        assert_eq!(uncapped.opts.node_warm_time_limit, None);
        assert_eq!(long.opts.node_warm_time_limit, Some(long_limit));
        assert_eq!(
            short.opts.node_warm_time_limit,
            Some(short_limit),
            "constructing later sessions must not change an earlier session's cap"
        );
    }
}

#[cfg(all(test, feature = "smt"))]
mod tests {
    use super::*;

    /// A rounded proxy is not the model NS is proving a bound for.  In this
    /// discriminating row the f64 lane sees `x >= 1`, while the true stored row
    /// is `2x >= 1` and has minimum 1/2.  Returning the proxy's 1 as a rigorous
    /// lower bound would let OBBT delete the true optimum.
    #[test]
    fn rigorous_bound_declines_ns_on_exact_side_store_models() {
        let mut m = Model::new();
        let x = m.add_col(0.0, 2.0);
        let row = m.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        m.record_inexact_row_coeff(row, x.0, BigRational::from_integer(2.into()));
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("continuous session");
        match s.rigorous_bound(x, Sense::Minimize).expect("bound solve") {
            Outcome::Bound {
                dual_bound,
                rigorous: true,
            } => assert_eq!(dual_bound, BigRational::new(1.into(), 2.into())),
            other => panic!("expected exact rigorous bound 1/2, got {other:?}"),
        }
    }

    #[test]
    fn inexact_milp_unbounded_without_ray_fails_closed() {
        let mut m = Model::new();
        let x = m.add_int_col(0.0, f64::INFINITY);
        let row = m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        m.record_inexact_row_coeff(row, x.0, BigRational::from_integer(2.into()));
        assert!(matches!(
            fail_closed_for_inexact(Outcome::Unbounded, &m),
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        ));
    }

    fn binary_model(cols: usize) -> Model {
        let mut m = Model::new();
        for _ in 0..cols {
            let _ = m.add_binary_col();
        }
        m
    }

    /// An un-deadlined session keeps the unconditional fallback (the
    /// function's contract: an answer at any price).
    #[test]
    fn smt_fallback_unconditional_without_deadline() {
        let s = BabSession::new(binary_model(1), &SolveOpts::new()).unwrap();
        assert!(s.smt_fallback_within_reach());
    }

    /// Small model, ample remaining budget: the fallback stays reachable.
    #[test]
    fn smt_fallback_entered_with_ample_budget() {
        let opts = SolveOpts::new().with_deadline(Instant::now() + Duration::from_hours(1));
        let s = BabSession::new(binary_model(1), &opts).unwrap();
        assert!(s.smt_fallback_within_reach());
    }

    /// The remaining-budget floor: a deadline with only a sliver left (the
    /// finalization-reserve shape a timing-out branch-and-bound hands back)
    /// declines the enumeration lane even though the model passes the
    /// integer-column ceiling — the honest `Unknown` ships at the cap.
    #[test]
    fn smt_fallback_declined_below_remaining_budget_floor() {
        let opts = SolveOpts::new().with_deadline(Instant::now() + Duration::from_millis(200));
        let s = BabSession::new(binary_model(124), &opts).unwrap();
        assert!(!s.smt_fallback_within_reach());
    }

    /// A deadline already in the past saturates to zero remaining and is
    /// likewise below the floor.
    #[test]
    fn smt_fallback_declined_past_deadline() {
        let expired_at = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the monotonic clock must be at least one second old");
        let opts = SolveOpts::new().with_deadline(expired_at);
        let s = BabSession::new(binary_model(1), &opts).unwrap();
        assert!(!s.smt_fallback_within_reach());
    }

    /// The floor gates on budget, not size: the many-binary ceiling still
    /// declines on its own even with ample budget remaining.
    #[test]
    fn smt_fallback_declined_above_int_ceiling_with_ample_budget() {
        let opts = SolveOpts::new().with_deadline(Instant::now() + Duration::from_hours(1));
        let s = BabSession::new(binary_model(1_025), &opts).unwrap();
        assert!(!s.smt_fallback_within_reach());
    }
}
