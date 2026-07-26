// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stateful LP and MILP solve sessions.
//!
//! [`LpSession`] supports one continuous model with many objectives and lazily
//! materializes an exact-rational basis that persists across exact re-solves.
//! [`BabSession`] provides scoped `fix_col`/`add_row` operations for MILP, using
//! native branch-and-bound for integral models and the exact LP path for
//! continuous models. When a MILP's root relaxation is already contradictory,
//! the session may attach an exact Farkas certificate to the infeasibility
//! verdict.

use std::mem::size_of;
use std::time::{Duration, Instant};

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::{BoundSide, CertifiedRow, FarkasCertificate, OptimalityCertificate};
use crate::certify::{certified_weak_dual_row, certify, MAX_EXACT_BASIS_ROWS};
use crate::error::{MilpError, ModelError};
use crate::exact::{Budget, ExactLp, LpFeasibility, LpOptimum};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::opts::{FixedAssignmentTreeWarmStart, SolveOpts};
use crate::outcome::{Outcome, UnknownReason};
use crate::simplex::{Candidate, FloatLp, SimplexStatus, WarmSolveMode};
use crate::tree_cert::{exact_farkas_from_float_ray, MilpInfeasibilityCertificate, TreeNode};

fn fixed_assignment_tree_start_assignment(
    warm_start: Option<FixedAssignmentTreeWarmStart>,
) -> usize {
    match warm_start {
        None => 0,
        Some(FixedAssignmentTreeWarmStart::ProgressivePrefix {
            start_assignment, ..
        })
        | Some(FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
            start_assignment,
            ..
        }) => usize::from(start_assignment),
    }
}

/// Intersect a local root/prefix advice cap with the proof's outer deadline.
///
/// `Duration::ZERO` requests one cooperative stop poll at the current instant.
/// Ordinary finite durations are capped by (and never extend) `outer_deadline`.
/// If `Instant` cannot represent `now + time_limit` (notably
/// `Duration::MAX`), the local cap is treated as unbounded: the outer deadline
/// remains authoritative, or `None` remains uncapped.
fn capped_assignment_tree_advice_deadline(
    outer_deadline: Option<Instant>,
    time_limit: Duration,
) -> Option<Instant> {
    let local_deadline = Instant::now().checked_add(time_limit);
    match (outer_deadline, local_deadline) {
        (Some(outer), Some(local)) => Some(outer.min(local)),
        (outer, None) => outer,
        (None, local) => local,
    }
}

fn fixed_assignment_tree_leaf_warm_mode(
    step: usize,
    warm_start: Option<FixedAssignmentTreeWarmStart>,
    incoming_status: SimplexStatus,
) -> WarmSolveMode {
    if step == 0 && warm_start.is_some() && incoming_status != SimplexStatus::Optimal {
        WarmSolveMode::PrimalProofContinuation
    } else {
        WarmSolveMode::Normal
    }
}

#[cfg(test)]
mod fixed_assignment_tree_warm_mode_tests {
    use super::*;

    fn configured() -> Option<FixedAssignmentTreeWarmStart> {
        Some(FixedAssignmentTreeWarmStart::ProgressivePrefix {
            prefix_time_limit: Duration::ZERO,
            start_assignment: 0,
        })
    }

    fn fixed_leaf_model() -> (Model, Vec<f64>) {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.fix_col(x, 1.0);
        (model, vec![1.0])
    }

    #[test]
    fn proof_continuation_is_only_first_configured_nonoptimal_leaf() {
        for incoming in [SimplexStatus::Stopped, SimplexStatus::PrimalInfeasible] {
            assert_eq!(
                fixed_assignment_tree_leaf_warm_mode(0, configured(), incoming),
                WarmSolveMode::PrimalProofContinuation
            );
            assert_eq!(
                fixed_assignment_tree_leaf_warm_mode(1, configured(), incoming),
                WarmSolveMode::Normal,
                "later Gray leaves retain historical warm-dual routing"
            );
            assert_eq!(
                fixed_assignment_tree_leaf_warm_mode(0, None, incoming),
                WarmSolveMode::Normal,
                "the default tree remains byte-for-byte on Normal mode"
            );
        }
        assert_eq!(
            fixed_assignment_tree_leaf_warm_mode(0, configured(), SimplexStatus::Optimal),
            WarmSolveMode::Normal,
            "an already optimal prefix needs no stopped-primal continuation"
        );
    }

    #[test]
    fn cached_dual_accepts_only_a_strictly_sufficient_verified_row() {
        let (model, q) = fixed_leaf_model();
        let warm_mode =
            fixed_assignment_tree_leaf_warm_mode(0, configured(), SimplexStatus::Stopped);
        let row = certified_cached_assignment_tree_leaf_row(
            warm_mode,
            &model,
            &q,
            &[],
            None,
            &BigRational::zero(),
            "cached positive test",
        )
        .expect("the fully fixed x=1 leaf proves objective x strictly above zero");

        assert_eq!(row.lb, BigRational::from_integer(1.into()));
        row.verify(&model)
            .expect("the cached-dual row must independently verify");
    }

    #[test]
    fn cached_dual_declines_an_insufficient_row() {
        let (model, q) = fixed_leaf_model();
        let warm_mode =
            fixed_assignment_tree_leaf_warm_mode(0, configured(), SimplexStatus::Stopped);
        assert!(
            certified_cached_assignment_tree_leaf_row(
                warm_mode,
                &model,
                &q,
                &[],
                None,
                &BigRational::from_integer(1.into()),
                "cached insufficient test",
            )
            .is_none(),
            "the threshold gate is strict: a bound equal to it is insufficient"
        );
    }

    #[test]
    fn cached_dual_declines_corrupt_float_advice() {
        let (mut model, q) = fixed_leaf_model();
        let x = Col(0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0)]);
        let warm_mode =
            fixed_assignment_tree_leaf_warm_mode(0, configured(), SimplexStatus::Stopped);
        assert!(
            certified_cached_assignment_tree_leaf_row(
                warm_mode,
                &model,
                &q,
                &[f64::NAN],
                None,
                &BigRational::zero(),
                "cached corrupt test",
            )
            .is_none(),
            "non-finite float advice must never produce an exact row"
        );
    }

    #[test]
    fn cached_dual_honors_an_expired_outer_deadline() {
        let (model, q) = fixed_leaf_model();
        let warm_mode =
            fixed_assignment_tree_leaf_warm_mode(0, configured(), SimplexStatus::Stopped);
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the monotonic clock supports a one-second lookback");
        assert!(
            certified_cached_assignment_tree_leaf_row(
                warm_mode,
                &model,
                &q,
                &[],
                Some(expired),
                &BigRational::zero(),
                "cached expired test",
            )
            .is_none(),
            "expired work must fail closed"
        );
    }

    #[test]
    fn cached_dual_is_inert_on_proof_neutral_routes() {
        let (mut model, q) = fixed_leaf_model();
        let x = Col(0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0)]);

        // Deliberately malformed arity: the exact weak-row machinery asserts
        // if invoked. Returning `None` proves these routes do not inspect it.
        for warm_mode in [WarmSolveMode::Normal, WarmSolveMode::PrimalAdvice] {
            assert!(certified_cached_assignment_tree_leaf_row(
                warm_mode,
                &model,
                &q,
                &[],
                None,
                &BigRational::zero(),
                "cached routing test",
            )
            .is_none());
        }
    }

    #[test]
    fn advice_deadline_zero_is_an_immediate_cooperative_cap() {
        let before = Instant::now();
        let capped = capped_assignment_tree_advice_deadline(None, Duration::ZERO)
            .expect("zero duration has a representable local deadline");
        let after = Instant::now();
        assert!(capped >= before && capped <= after);
    }

    #[test]
    fn advice_deadline_finite_cap_cooperates_with_outer_deadline() {
        let before = Instant::now();
        let outer = before + Duration::from_secs(30);
        let local = capped_assignment_tree_advice_deadline(Some(outer), Duration::from_secs(10))
            .expect("finite cap");
        assert!(local < outer);
        assert!(local >= before + Duration::from_secs(9));

        let nearer_outer = before + Duration::from_secs(1);
        assert_eq!(
            capped_assignment_tree_advice_deadline(Some(nearer_outer), Duration::from_secs(10)),
            Some(nearer_outer),
            "a local advice cap never extends the proof deadline"
        );
    }

    #[test]
    fn advice_deadline_max_is_unbounded_except_for_outer_deadline() {
        let outer = Instant::now() + Duration::from_secs(30);
        assert_eq!(
            capped_assignment_tree_advice_deadline(Some(outer), Duration::MAX),
            Some(outer)
        );
        assert_eq!(
            capped_assignment_tree_advice_deadline(None, Duration::MAX),
            None
        );
    }
}

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

/// Try both row-dual sign conventions as exact weak-duality rows, strongest
/// directed-rounding score first.
///
/// The float vector is advice only. Each proposal is independently rebuilt
/// and verified over `model`'s true rational facts, and `stronger_than` is an
/// exact exclusive gate in the returned row's lower-form coordinates.
fn certified_weak_row_from_duals(
    model: &Model,
    q: &[f64],
    row_duals: &[f64],
    deadline: Option<Instant>,
    stronger_than: Option<&BigRational>,
    trace_context: &str,
) -> Option<CertifiedRow> {
    let expired = || deadline.is_some_and(|limit| Instant::now() >= limit);
    if expired() {
        return None;
    }
    let negated_duals: Vec<f64> = row_duals.iter().map(|&y| -y).collect();
    let direct_score = crate::ns::rigorous_lower_bound(model, q, row_duals);
    if expired() {
        return None;
    }
    let negated_score = crate::ns::rigorous_lower_bound(model, q, &negated_duals);
    if expired() {
        return None;
    }
    let (first, second) = match (direct_score, negated_score) {
        (Some(a), Some(b)) if b > a => (&negated_duals[..], row_duals),
        (None, Some(_)) => (&negated_duals[..], row_duals),
        _ => (row_duals, &negated_duals[..]),
    };
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    for (proposal, duals) in [first, second].into_iter().enumerate() {
        if let Some(row) = certified_weak_dual_row(model, q, duals, deadline) {
            let sufficient = stronger_than.is_none_or(|threshold| &row.lb > threshold);
            if trace {
                let lb = &row.lb;
                match stronger_than {
                    Some(threshold) => eprintln!(
                        "AY_MILP_TRACE {trace_context} proposal {proposal}: \
                         lb={lb} threshold={threshold} sufficient={sufficient}"
                    ),
                    None => eprintln!(
                        "AY_MILP_TRACE {trace_context} proposal {proposal}: lb={lb} accepted"
                    ),
                }
            }
            if sufficient {
                return Some(row);
            }
        }
    }
    None
}

/// Try the prefix candidate's already-extracted true-objective duals as the
/// first configured assignment-tree leaf's exact weak row.
///
/// This is deliberately narrower than [`certified_weak_row_from_duals`]:
/// [`WarmSolveMode::PrimalProofContinuation`] is the typed token for the first
/// configured non-optimal leaf only. The float vector remains advice. A row
/// leaves this helper only after the existing exact reconstruction,
/// independent verification, strict threshold, and deadline gates all pass.
/// Every other route returns before even inspecting `row_duals`.
fn certified_cached_assignment_tree_leaf_row(
    warm_mode: WarmSolveMode,
    model: &Model,
    q: &[f64],
    row_duals: &[f64],
    deadline: Option<Instant>,
    threshold: &BigRational,
    trace_context: &str,
) -> Option<CertifiedRow> {
    if warm_mode != WarmSolveMode::PrimalProofContinuation {
        return None;
    }
    certified_weak_row_from_duals(
        model,
        q,
        row_duals,
        deadline,
        Some(threshold),
        trace_context,
    )
}

/// A certified lower-row harvest that either closes at the root relaxation or
/// needs one complete 0/1 case split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedSplitHarvest {
    /// The root relaxation itself proves the requested lower row.
    Root(CertifiedRow),
    /// The root row was insufficient, but both binary children prove it.
    ///
    /// `zero` is conditional on the split column being 0; `one` is
    /// conditional on it being 1. The rows retain ordinary model fact
    /// multipliers and are intended for
    /// [`CertifiedRow::into_farkas_against_row_upper`] plus a checked
    /// [`crate::TreeNode`] split.
    Split {
        /// Certified under the split column fixed to 0.
        zero: CertifiedRow,
        /// Certified under the split column fixed to 1.
        one: CertifiedRow,
    },
}

/// Maximum number of leaves in a certified binary assignment-tree harvest.
///
/// The corresponding depth cap is four. Keeping the cap in the proof API
/// bounds the exponential amplification at sixteen leaves; each solve and
/// exact leaf certificate still scales with the caller's model.
pub const MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES: usize = 16;

/// Maximum number of relaxed binary candidates considered by target-FSB.
///
/// The complete depth-two selector probes both children of every candidate,
/// then all four joint assignments with the first selected candidate. Eight
/// candidates therefore cost at most 44 bounded advice calls. The three-stage
/// five-leaf comb costs 36 quick probes at the same candidate cap.
pub const MAX_TARGET_FSB_CANDIDATES: usize = 8;

/// Resource caps for target-objective full strong branching.
///
/// These caps govern the complete depth-two selector, the adaptive three-leaf
/// selector, and the adaptive four- and five-leaf comb selectors. The probes
/// are advice only. Complete and three-leaf calls start from the same saved
/// target-root basis; every comb call starts from its saved cold root-hard
/// basis. Each call spends at most `max_probe_pivots_per_call` dual pivots, and
/// all calls in one complete scan share `probe_time_limit`. `max_probe_calls`
/// is an absolute count cap; a request whose complete deterministic scan would
/// exceed it declines before probing. `max_probe_scratch_bytes` caps the
/// selector's incremental retained/scoring workspace. The simplex LU fill
/// guard remains an additional hard memory backstop. Each comb's one cold
/// root-hard anchor is not a quick probe: the per-call pivot, call, and
/// probe-wall caps do not govern its iterations or time. The outer
/// [`SolveOpts`] deadline and the simplex's internal LU guard do; its retained
/// anchor candidate is nevertheless included in the scratch preflight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetFsbOpts {
    max_probe_pivots_per_call: u64,
    max_probe_calls: usize,
    probe_time_limit: Duration,
    max_probe_scratch_bytes: usize,
}

impl Default for TargetFsbOpts {
    fn default() -> Self {
        Self {
            max_probe_pivots_per_call: 25,
            max_probe_calls: 44,
            probe_time_limit: Duration::from_secs(5),
            max_probe_scratch_bytes: 64 << 20,
        }
    }
}

impl TargetFsbOpts {
    /// Default bounded target-FSB policy.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the dual-pivot cap for each advice child.
    #[must_use]
    pub fn with_max_probe_pivots_per_call(mut self, pivots: u64) -> Self {
        self.max_probe_pivots_per_call = pivots;
        self
    }

    /// Set the total advice-call cap.
    #[must_use]
    pub fn with_max_probe_calls(mut self, calls: usize) -> Self {
        self.max_probe_calls = calls;
        self
    }

    /// Set the wall-clock cap shared by the complete advice scan.
    #[must_use]
    pub fn with_probe_time_limit(mut self, limit: Duration) -> Self {
        self.probe_time_limit = limit;
        self
    }

    /// Set the cap on incremental target-FSB scoring workspace.
    #[must_use]
    pub fn with_max_probe_scratch_bytes(mut self, bytes: usize) -> Self {
        self.max_probe_scratch_bytes = bytes;
        self
    }
}

/// Diagnostics from one target-FSB selection and exact harvest.
#[derive(Debug, Clone, PartialEq)]
pub struct TargetFsbReport {
    candidate_count: usize,
    probe_calls: usize,
    selected_splits: Vec<Col>,
    first_worst_lower_bound: Option<f64>,
    joint_worst_lower_bound: Option<f64>,
}

impl TargetFsbReport {
    /// Number of caller candidates admitted to the bounded scan.
    #[must_use]
    pub fn candidate_count(&self) -> usize {
        self.candidate_count
    }

    /// Number of quick advice LPs actually run.
    #[must_use]
    pub fn probe_calls(&self) -> usize {
        self.probe_calls
    }

    /// Selected split columns in tree order. Empty on the root fast path.
    #[must_use]
    pub fn selected_splits(&self) -> &[Col] {
        &self.selected_splits
    }

    /// Worst of the selected first candidate's two child lower bounds.
    #[must_use]
    pub fn first_worst_lower_bound(&self) -> Option<f64> {
        self.first_worst_lower_bound
    }

    /// Worst of the selected pair's four joint-assignment lower bounds.
    #[must_use]
    pub fn joint_worst_lower_bound(&self) -> Option<f64> {
        self.joint_worst_lower_bound
    }
}

/// Diagnostics from one adaptive three-leaf target-FSB harvest.
///
/// The caller fixes the root split and which root value is the hard branch.
/// Target-FSB then ranks one second split only inside that hard branch. On the
/// root fast path, [`Self::second_split`] and
/// [`Self::hard_grandchild_lower_bounds`] are `None`.
#[derive(Debug, Clone, PartialEq)]
pub struct AdaptiveThreeLeafTargetFsbReport {
    candidate_count: usize,
    probe_calls: usize,
    root_candidate_index: usize,
    root_split: Col,
    hard_value: bool,
    second_candidate_index: Option<usize>,
    second_split: Option<Col>,
    hard_grandchild_lower_bounds: Option<[f64; 2]>,
}

impl AdaptiveThreeLeafTargetFsbReport {
    /// Number of caller candidates admitted to the bounded scan.
    #[must_use]
    pub fn candidate_count(&self) -> usize {
        self.candidate_count
    }

    /// Number of quick advice LPs actually run.
    #[must_use]
    pub fn probe_calls(&self) -> usize {
        self.probe_calls
    }

    /// Index of [`Self::root_split`] in the caller's candidate slice.
    #[must_use]
    pub fn root_candidate_index(&self) -> usize {
        self.root_candidate_index
    }

    /// Caller-selected root split.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Value of the root split refined by the second split.
    ///
    /// `false` denotes 0 and `true` denotes 1.
    #[must_use]
    pub fn hard_value(&self) -> bool {
        self.hard_value
    }

    /// Index of the selected second split in the caller's candidate slice.
    ///
    /// This is `None` when a sufficient root row returns before any probes.
    #[must_use]
    pub fn second_candidate_index(&self) -> Option<usize> {
        self.second_candidate_index
    }

    /// Target-FSB-selected split below the hard root child.
    ///
    /// This is `None` when a sufficient root row returns before any probes.
    #[must_use]
    pub fn second_split(&self) -> Option<Col> {
        self.second_split
    }

    /// Rigorous probe lower bounds for the selected second split fixed to
    /// `[0, 1]` below the hard root child.
    ///
    /// This is `None` on the root fast path. A completed advice scan can still
    /// report `-infinity` for a box whose limited duals did not produce a finite
    /// safe bound; such a score is advice only.
    #[must_use]
    pub fn hard_grandchild_lower_bounds(&self) -> Option<[f64; 2]> {
        self.hard_grandchild_lower_bounds
    }
}

/// Diagnostics from one adaptive four-leaf comb target-FSB harvest.
#[derive(Debug, Clone, PartialEq)]
pub struct AdaptiveFourLeafCombTargetFsbReport {
    candidate_count: usize,
    probe_calls: usize,
    second_stage_probe_calls: usize,
    third_stage_probe_calls: usize,
    root_candidate_index: usize,
    root_split: Col,
    root_hard_value: bool,
    second_candidate_index: usize,
    second_split: Col,
    second_hard_value: bool,
    second_child_lower_bounds: [f64; 2],
    third_candidate_index: usize,
    third_split: Col,
    third_child_lower_bounds: [f64; 2],
}

impl AdaptiveFourLeafCombTargetFsbReport {
    /// Number of caller candidates admitted to the bounded scan.
    #[must_use]
    pub fn candidate_count(&self) -> usize {
        self.candidate_count
    }

    /// Total quick advice LPs actually run.
    #[must_use]
    pub fn probe_calls(&self) -> usize {
        self.probe_calls
    }

    /// Advice calls used to select the split below the hard root child.
    #[must_use]
    pub fn second_stage_probe_calls(&self) -> usize {
        self.second_stage_probe_calls
    }

    /// Advice calls used to select the terminal split below both hard values.
    #[must_use]
    pub fn third_stage_probe_calls(&self) -> usize {
        self.third_stage_probe_calls
    }

    /// Index of [`Self::root_split`] in the caller's candidate slice.
    #[must_use]
    pub fn root_candidate_index(&self) -> usize {
        self.root_candidate_index
    }

    /// Caller-selected root split.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Caller-selected root value refined by the rest of the comb.
    #[must_use]
    pub fn root_hard_value(&self) -> bool {
        self.root_hard_value
    }

    /// Index of [`Self::second_split`] in the caller's candidate slice.
    #[must_use]
    pub fn second_candidate_index(&self) -> usize {
        self.second_candidate_index
    }

    /// Target-FSB-selected split below the hard root child.
    #[must_use]
    pub fn second_split(&self) -> Col {
        self.second_split
    }

    /// Value of [`Self::second_split`] refined by the terminal split.
    ///
    /// The strictly lower of [`Self::second_child_lower_bounds`] is hard;
    /// `false` wins an exact tie.
    #[must_use]
    pub fn second_hard_value(&self) -> bool {
        self.second_hard_value
    }

    /// Rigorous stage-one probe bounds for the selected second split fixed to
    /// `[0, 1]`.
    #[must_use]
    pub fn second_child_lower_bounds(&self) -> [f64; 2] {
        self.second_child_lower_bounds
    }

    /// Index of [`Self::third_split`] in the caller's candidate slice.
    #[must_use]
    pub fn third_candidate_index(&self) -> usize {
        self.third_candidate_index
    }

    /// Target-FSB-selected terminal split.
    #[must_use]
    pub fn third_split(&self) -> Col {
        self.third_split
    }

    /// Rigorous stage-two probe bounds for the selected terminal split fixed
    /// to `[0, 1]`.
    #[must_use]
    pub fn third_child_lower_bounds(&self) -> [f64; 2] {
        self.third_child_lower_bounds
    }
}

/// Diagnostics from one adaptive five-leaf comb target-FSB harvest.
#[derive(Debug, Clone, PartialEq)]
pub struct AdaptiveFiveLeafCombTargetFsbReport {
    candidate_count: usize,
    probe_calls: usize,
    second_stage_probe_calls: usize,
    third_stage_probe_calls: usize,
    fourth_stage_probe_calls: usize,
    root_candidate_index: usize,
    root_split: Col,
    root_hard_value: bool,
    second_candidate_index: usize,
    second_split: Col,
    second_hard_value: bool,
    second_child_lower_bounds: [f64; 2],
    third_candidate_index: usize,
    third_split: Col,
    third_hard_value: bool,
    third_child_lower_bounds: [f64; 2],
    fourth_candidate_index: usize,
    fourth_split: Col,
    fourth_child_lower_bounds: [f64; 2],
}

impl AdaptiveFiveLeafCombTargetFsbReport {
    /// Number of caller candidates admitted to the bounded scan.
    #[must_use]
    pub fn candidate_count(&self) -> usize {
        self.candidate_count
    }

    /// Total quick advice LPs actually run.
    #[must_use]
    pub fn probe_calls(&self) -> usize {
        self.probe_calls
    }

    /// Advice calls used to select the split below the hard root child.
    #[must_use]
    pub fn second_stage_probe_calls(&self) -> usize {
        self.second_stage_probe_calls
    }

    /// Advice calls used to select the split below the first two hard values.
    #[must_use]
    pub fn third_stage_probe_calls(&self) -> usize {
        self.third_stage_probe_calls
    }

    /// Advice calls used to select the terminal split below three hard values.
    #[must_use]
    pub fn fourth_stage_probe_calls(&self) -> usize {
        self.fourth_stage_probe_calls
    }

    /// Index of [`Self::root_split`] in the caller's candidate slice.
    #[must_use]
    pub fn root_candidate_index(&self) -> usize {
        self.root_candidate_index
    }

    /// Caller-selected root split.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Caller-selected root value refined by the rest of the comb.
    #[must_use]
    pub fn root_hard_value(&self) -> bool {
        self.root_hard_value
    }

    /// Index of [`Self::second_split`] in the caller's candidate slice.
    #[must_use]
    pub fn second_candidate_index(&self) -> usize {
        self.second_candidate_index
    }

    /// Target-FSB-selected split below the hard root child.
    #[must_use]
    pub fn second_split(&self) -> Col {
        self.second_split
    }

    /// Value of [`Self::second_split`] refined by [`Self::third_split`].
    ///
    /// The strictly lower of [`Self::second_child_lower_bounds`] is hard;
    /// `false` wins an exact tie.
    #[must_use]
    pub fn second_hard_value(&self) -> bool {
        self.second_hard_value
    }

    /// Rigorous stage-one probe bounds for the selected second split fixed to
    /// `[0, 1]`.
    #[must_use]
    pub fn second_child_lower_bounds(&self) -> [f64; 2] {
        self.second_child_lower_bounds
    }

    /// Index of [`Self::third_split`] in the caller's candidate slice.
    #[must_use]
    pub fn third_candidate_index(&self) -> usize {
        self.third_candidate_index
    }

    /// Target-FSB-selected split below the first two hard values.
    #[must_use]
    pub fn third_split(&self) -> Col {
        self.third_split
    }

    /// Value of [`Self::third_split`] refined by [`Self::fourth_split`].
    ///
    /// The strictly lower of [`Self::third_child_lower_bounds`] is hard;
    /// `false` wins an exact tie.
    #[must_use]
    pub fn third_hard_value(&self) -> bool {
        self.third_hard_value
    }

    /// Rigorous stage-two probe bounds for the selected third split fixed to
    /// `[0, 1]`.
    #[must_use]
    pub fn third_child_lower_bounds(&self) -> [f64; 2] {
        self.third_child_lower_bounds
    }

    /// Index of [`Self::fourth_split`] in the caller's candidate slice.
    #[must_use]
    pub fn fourth_candidate_index(&self) -> usize {
        self.fourth_candidate_index
    }

    /// Target-FSB-selected terminal split.
    #[must_use]
    pub fn fourth_split(&self) -> Col {
        self.fourth_split
    }

    /// Rigorous stage-three probe bounds for the selected fourth split fixed
    /// to `[0, 1]`.
    #[must_use]
    pub fn fourth_child_lower_bounds(&self) -> [f64; 2] {
        self.fourth_child_lower_bounds
    }
}

/// Rigorous target-FSB score for one probed computational box.
///
/// Use the branch-and-bound bound implementation rather than the model-level
/// NS helper: `safe_bound` first clamps a wrong-signed dual on a one-sided
/// logical row to zero. Weak duality permits that replacement for any
/// approximate dual, and it prevents an otherwise useful probe from becoming
/// `-inf` merely because the limited pivot walk stopped before restoring the
/// logical's preferred sign. The reduced-cost buffer is caller-owned so a
/// complete `6n - 4` depth-two scan, `4n - 6` four-leaf comb scan, or
/// `6n - 12` five-leaf comb scan allocates it only once.
fn target_fsb_probe_score(
    lp: &FloatLp,
    duals: &[f64],
    lower: &[f64],
    upper: &[f64],
    rc_scratch: &mut [(f64, f64)],
) -> Option<f64> {
    crate::bab::safe_bound(lp, duals, lower, upper, rc_scratch)
}

#[allow(clippy::too_many_arguments)]
fn adaptive_target_fsb_probe_box(
    lp: &FloatLp,
    warm: &Candidate,
    lower: &[f64],
    upper: &[f64],
    fsb_opts: &TargetFsbOpts,
    probe_deadline: Instant,
    rc_scratch: &mut [(f64, f64)],
    probe_calls: &mut usize,
) -> Option<f64> {
    if *probe_calls >= fsb_opts.max_probe_calls || Instant::now() >= probe_deadline {
        return None;
    }
    *probe_calls += 1;
    let duals = lp.probe_duals_fail_closed(
        lower,
        upper,
        Some((&warm.basis, &warm.at)),
        fsb_opts.max_probe_pivots_per_call,
        Some(probe_deadline),
    )?;
    if Instant::now() >= probe_deadline {
        return None;
    }
    let score = target_fsb_probe_score(lp, &duals, lower, upper, rc_scratch);
    if Instant::now() >= probe_deadline {
        return None;
    }
    Some(score.unwrap_or(f64::NEG_INFINITY))
}

#[allow(clippy::too_many_arguments)]
fn adaptive_target_fsb_select_stage(
    lp: &FloatLp,
    warm: &Candidate,
    candidates: &[Col],
    excluded_indices: &[usize],
    lower: &mut [f64],
    upper: &mut [f64],
    fsb_opts: &TargetFsbOpts,
    probe_deadline: Instant,
    rc_scratch: &mut [(f64, f64)],
    probe_calls: &mut usize,
    trace_context: &str,
) -> Option<(usize, [f64; 2], f64)> {
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    let mut selected_index = None;
    let mut selected_bounds = [f64::NEG_INFINITY; 2];
    let mut selected_worst = f64::NEG_INFINITY;
    for (index, &candidate) in candidates.iter().enumerate() {
        if excluded_indices.contains(&index) {
            continue;
        }
        lower[candidate.index()] = 0.0;
        upper[candidate.index()] = 0.0;
        let zero = adaptive_target_fsb_probe_box(
            lp,
            warm,
            lower,
            upper,
            fsb_opts,
            probe_deadline,
            rc_scratch,
            probe_calls,
        )?;
        lower[candidate.index()] = 1.0;
        upper[candidate.index()] = 1.0;
        let one = adaptive_target_fsb_probe_box(
            lp,
            warm,
            lower,
            upper,
            fsb_opts,
            probe_deadline,
            rc_scratch,
            probe_calls,
        )?;
        lower[candidate.index()] = 0.0;
        upper[candidate.index()] = 1.0;
        let worst = zero.min(one);
        if trace {
            eprintln!(
                "AY_MILP_TRACE {trace_context}: candidate_col={} zero={zero:.17e} \
                 one={one:.17e} worst={worst:.17e}",
                candidate.index(),
            );
        }
        if selected_index.is_none() || worst > selected_worst {
            selected_index = Some(index);
            selected_bounds = [zero, one];
            selected_worst = worst;
        }
    }
    Some((selected_index?, selected_bounds, selected_worst))
}

/// A certified lower-row harvest that either closes at the root relaxation or
/// needs a complete assignment tree over up to four relaxed binary-candidate
/// columns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedBinaryTreeHarvest {
    /// The root relaxation itself proves the requested lower row.
    Root(CertifiedRow),
    /// Every complete 0/1 assignment to the selected columns proves the row.
    Tree(CertifiedBinaryAssignmentTree),
}

/// Exact evidence for every complete assignment to an ordered relaxed
/// binary-candidate column list.
///
/// Fields are deliberately private: the association between an assignment and
/// its conditional row or infeasibility witness is proof-critical. Use
/// [`Self::into_farkas_against_row_upper`] to close the rows against a decision
/// row and obtain an independently verified whole-tree certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedBinaryAssignmentTree {
    split_cols: Vec<Col>,
    /// Canonical binary order, with `split_cols[0]` as the most-significant
    /// assignment bit. This differs from the Gray-code order used to solve the
    /// leaves.
    leaves: Vec<CertifiedBinaryAssignmentLeaf>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CertifiedBinaryAssignmentLeaf {
    ConditionalRow(CertifiedRow),
    Infeasible(FarkasCertificate),
}

impl CertifiedBinaryAssignmentTree {
    /// Ordered columns split by this tree.
    #[must_use]
    pub fn split_cols(&self) -> &[Col] {
        &self.split_cols
    }

    /// Number of complete assignments (and therefore certificate leaves).
    #[must_use]
    pub fn num_leaves(&self) -> usize {
        self.leaves.len()
    }

    /// Close every feasible leaf's conditional lower row against `upper_row`,
    /// retain direct infeasible-leaf witnesses, and build a verified
    /// whole-tree infeasibility certificate.
    ///
    /// `model` is the caller's decision model: it must preserve the rows and
    /// column indices used to derive this harvest, restore the selected
    /// columns' integrality, and contain `upper_row`. Each low branch is
    /// `x <= 0` and each high branch is `x >= 1`. Row identities, branch
    /// assumptions, split coverage, and the completed certificate are all
    /// rechecked exactly; any mismatch returns `None`.
    #[must_use]
    pub fn into_farkas_against_row_upper(
        self,
        model: &Model,
        upper_row: Row,
    ) -> Option<MilpInfeasibilityCertificate> {
        let depth = self.split_cols.len();
        if depth == 0
            || depth > MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES.ilog2() as usize
            || self.leaves.len() != 1usize.checked_shl(u32::try_from(depth).ok()?)?
        {
            return None;
        }

        fn build(
            level: usize,
            canonical_index: usize,
            split_cols: &[Col],
            leaves: &mut [Option<CertifiedBinaryAssignmentLeaf>],
            branch_bounds: &mut Vec<(Col, BoundSide, BigRational)>,
            model: &Model,
            upper_row: Row,
        ) -> Option<TreeNode> {
            if level == split_cols.len() {
                let farkas = match leaves.get_mut(canonical_index)?.take()? {
                    CertifiedBinaryAssignmentLeaf::ConditionalRow(row) => {
                        row.into_farkas_against_row_upper(model, upper_row, branch_bounds)?
                    }
                    CertifiedBinaryAssignmentLeaf::Infeasible(farkas) => farkas,
                };
                return Some(TreeNode::Leaf { farkas });
            }

            let col = split_cols[level];
            let remaining = split_cols.len() - level - 1;
            let high_bit = 1usize.checked_shl(u32::try_from(remaining).ok()?)?;

            branch_bounds.push((col, BoundSide::Upper, BigRational::zero()));
            let lo = build(
                level + 1,
                canonical_index,
                split_cols,
                leaves,
                branch_bounds,
                model,
                upper_row,
            )?;
            branch_bounds.pop();

            branch_bounds.push((col, BoundSide::Lower, BigRational::from_integer(1.into())));
            let hi = build(
                level + 1,
                canonical_index | high_bit,
                split_cols,
                leaves,
                branch_bounds,
                model,
                upper_row,
            )?;
            branch_bounds.pop();

            Some(TreeNode::Split {
                col,
                cut: BigRational::zero(),
                lo: Box::new(lo),
                hi: Box::new(hi),
            })
        }

        let mut leaves: Vec<Option<CertifiedBinaryAssignmentLeaf>> =
            self.leaves.into_iter().map(Some).collect();
        let root = build(
            0,
            0,
            &self.split_cols,
            &mut leaves,
            &mut Vec::with_capacity(depth),
            model,
            upper_row,
        )?;
        let certificate = MilpInfeasibilityCertificate { root };
        certificate.verify(model).ok()?;
        Some(certificate)
    }
}

/// A certified lower-row harvest that either closes at the root relaxation or
/// uses an adaptive three-leaf binary tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedAdaptiveThreeLeafHarvest {
    /// The root relaxation itself proves the requested lower row.
    Root(CertifiedRow),
    /// The easy root child and both grandchildren of the hard child prove it.
    Tree(Box<CertifiedAdaptiveThreeLeafTree>),
}

/// Exact evidence for an asymmetric binary tree with exactly three leaves.
///
/// The root split and its hard value are supplied by the caller. The opposite
/// root value is the easy leaf; only the hard child is refined by
/// `second_split`. Fields are deliberately private because the association
/// between branch assumptions and leaf evidence is proof-critical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedAdaptiveThreeLeafTree {
    root_split: Col,
    hard_value: bool,
    second_split: Col,
    easy: CertifiedBinaryAssignmentLeaf,
    hard_zero: CertifiedBinaryAssignmentLeaf,
    hard_one: CertifiedBinaryAssignmentLeaf,
}

impl CertifiedAdaptiveThreeLeafTree {
    /// Caller-selected split at the root.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Value of the root split refined by [`Self::second_split`].
    ///
    /// `false` denotes 0 and `true` denotes 1.
    #[must_use]
    pub fn hard_value(&self) -> bool {
        self.hard_value
    }

    /// Target-FSB-selected split below the hard root child.
    #[must_use]
    pub fn second_split(&self) -> Col {
        self.second_split
    }

    /// Number of certificate leaves.
    #[must_use]
    pub const fn num_leaves(&self) -> usize {
        3
    }

    /// Close every feasible leaf's conditional lower row against `upper_row`,
    /// retain direct infeasible-leaf witnesses, and build a verified
    /// whole-tree infeasibility certificate.
    ///
    /// `model` must preserve the relaxation facts used to derive this harvest,
    /// restore both split columns' integrality, and contain `upper_row`.
    /// Branch identities, the asymmetric tree shape, leaf assumptions, and the
    /// completed certificate are rechecked exactly; any mismatch returns
    /// `None`.
    #[must_use]
    pub fn into_farkas_against_row_upper(
        self,
        model: &Model,
        upper_row: Row,
    ) -> Option<MilpInfeasibilityCertificate> {
        fn branch_bound(col: Col, value: bool) -> (Col, BoundSide, BigRational) {
            if value {
                (col, BoundSide::Lower, BigRational::from_integer(1.into()))
            } else {
                (col, BoundSide::Upper, BigRational::zero())
            }
        }

        fn leaf_node(
            leaf: CertifiedBinaryAssignmentLeaf,
            branch_bounds: &[(Col, BoundSide, BigRational)],
            model: &Model,
            upper_row: Row,
        ) -> Option<TreeNode> {
            let farkas = match leaf {
                CertifiedBinaryAssignmentLeaf::ConditionalRow(row) => {
                    row.into_farkas_against_row_upper(model, upper_row, branch_bounds)?
                }
                CertifiedBinaryAssignmentLeaf::Infeasible(farkas) => farkas,
            };
            Some(TreeNode::Leaf { farkas })
        }

        let Self {
            root_split,
            hard_value,
            second_split,
            easy,
            hard_zero,
            hard_one,
        } = self;
        if root_split == second_split {
            return None;
        }
        if root_split.index() >= model.num_cols() || second_split.index() >= model.num_cols() {
            return None;
        }

        let easy_node = leaf_node(
            easy,
            &[branch_bound(root_split, !hard_value)],
            model,
            upper_row,
        )?;
        let hard_zero_node = leaf_node(
            hard_zero,
            &[
                branch_bound(root_split, hard_value),
                branch_bound(second_split, false),
            ],
            model,
            upper_row,
        )?;
        let hard_one_node = leaf_node(
            hard_one,
            &[
                branch_bound(root_split, hard_value),
                branch_bound(second_split, true),
            ],
            model,
            upper_row,
        )?;
        let hard_node = TreeNode::Split {
            col: second_split,
            cut: BigRational::zero(),
            lo: Box::new(hard_zero_node),
            hi: Box::new(hard_one_node),
        };
        let (lo, hi) = if hard_value {
            (easy_node, hard_node)
        } else {
            (hard_node, easy_node)
        };
        let certificate = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: root_split,
                cut: BigRational::zero(),
                lo: Box::new(lo),
                hi: Box::new(hi),
            },
        };
        certificate.verify(model).ok()?;
        Some(certificate)
    }
}

/// Exact evidence for an asymmetric four-leaf binary comb.
///
/// The caller supplies the root split and its hard value. Target-FSB chooses a
/// second split below that value, refines the lower-scoring second value, and
/// chooses a terminal third split below both hard assignments. Fields are
/// deliberately private because their leaf-to-path association is
/// proof-critical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedAdaptiveFourLeafComb {
    root_split: Col,
    root_hard_value: bool,
    second_split: Col,
    second_hard_value: bool,
    third_split: Col,
    root_easy: CertifiedBinaryAssignmentLeaf,
    second_easy: CertifiedBinaryAssignmentLeaf,
    third_zero: CertifiedBinaryAssignmentLeaf,
    third_one: CertifiedBinaryAssignmentLeaf,
}

impl CertifiedAdaptiveFourLeafComb {
    /// Caller-selected split at the root.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Value of the root split refined by [`Self::second_split`].
    #[must_use]
    pub fn root_hard_value(&self) -> bool {
        self.root_hard_value
    }

    /// Target-FSB-selected split below the hard root child.
    #[must_use]
    pub fn second_split(&self) -> Col {
        self.second_split
    }

    /// Value of the second split refined by [`Self::third_split`].
    #[must_use]
    pub fn second_hard_value(&self) -> bool {
        self.second_hard_value
    }

    /// Target-FSB-selected terminal split.
    #[must_use]
    pub fn third_split(&self) -> Col {
        self.third_split
    }

    /// Number of certificate leaves.
    #[must_use]
    pub const fn num_leaves(&self) -> usize {
        4
    }

    /// Close every feasible leaf's conditional lower row against `upper_row`,
    /// retain direct infeasible-leaf witnesses, and return a verified
    /// whole-comb infeasibility certificate.
    ///
    /// `model` must preserve the relaxation facts used to derive this carrier,
    /// restore all three split columns' integrality, and contain `upper_row`.
    /// Branch identities, orientations, leaf assumptions, and the completed
    /// arbitrary tree are rechecked exactly; any mismatch returns `None`.
    #[must_use]
    pub fn into_farkas_against_row_upper(
        self,
        model: &Model,
        upper_row: Row,
    ) -> Option<MilpInfeasibilityCertificate> {
        if upper_row.index() >= model.num_rows() {
            return None;
        }

        fn branch_bound(col: Col, value: bool) -> (Col, BoundSide, BigRational) {
            if value {
                (col, BoundSide::Lower, BigRational::from_integer(1.into()))
            } else {
                (col, BoundSide::Upper, BigRational::zero())
            }
        }

        fn leaf_node(
            leaf: CertifiedBinaryAssignmentLeaf,
            branch_bounds: &[(Col, BoundSide, BigRational)],
            model: &Model,
            upper_row: Row,
        ) -> Option<TreeNode> {
            let farkas = match leaf {
                CertifiedBinaryAssignmentLeaf::ConditionalRow(row) => {
                    row.into_farkas_against_row_upper(model, upper_row, branch_bounds)?
                }
                CertifiedBinaryAssignmentLeaf::Infeasible(farkas) => farkas,
            };
            Some(TreeNode::Leaf { farkas })
        }

        let Self {
            root_split,
            root_hard_value,
            second_split,
            second_hard_value,
            third_split,
            root_easy,
            second_easy,
            third_zero,
            third_one,
        } = self;
        if root_split == second_split || root_split == third_split || second_split == third_split {
            return None;
        }
        if [root_split, second_split, third_split]
            .into_iter()
            .any(|col| col.index() >= model.num_cols())
        {
            return None;
        }

        let root_easy_node = leaf_node(
            root_easy,
            &[branch_bound(root_split, !root_hard_value)],
            model,
            upper_row,
        )?;
        let second_easy_node = leaf_node(
            second_easy,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, !second_hard_value),
            ],
            model,
            upper_row,
        )?;
        let third_zero_node = leaf_node(
            third_zero,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, second_hard_value),
                branch_bound(third_split, false),
            ],
            model,
            upper_row,
        )?;
        let third_one_node = leaf_node(
            third_one,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, second_hard_value),
                branch_bound(third_split, true),
            ],
            model,
            upper_row,
        )?;
        let third_node = TreeNode::Split {
            col: third_split,
            cut: BigRational::zero(),
            lo: Box::new(third_zero_node),
            hi: Box::new(third_one_node),
        };
        let (second_lo, second_hi) = if second_hard_value {
            (second_easy_node, third_node)
        } else {
            (third_node, second_easy_node)
        };
        let second_node = TreeNode::Split {
            col: second_split,
            cut: BigRational::zero(),
            lo: Box::new(second_lo),
            hi: Box::new(second_hi),
        };
        let (root_lo, root_hi) = if root_hard_value {
            (root_easy_node, second_node)
        } else {
            (second_node, root_easy_node)
        };
        let certificate = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: root_split,
                cut: BigRational::zero(),
                lo: Box::new(root_lo),
                hi: Box::new(root_hi),
            },
        };
        certificate.verify(model).ok()?;
        Some(certificate)
    }
}

/// Exact evidence for an asymmetric five-leaf binary comb.
///
/// The caller supplies the root split and its hard value. Three target-FSB
/// stages choose the remaining splits; the lower-scoring second and third
/// values continue the comb. Fields are deliberately private because their
/// leaf-to-path association is proof-critical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedAdaptiveFiveLeafComb {
    root_split: Col,
    root_hard_value: bool,
    second_split: Col,
    second_hard_value: bool,
    third_split: Col,
    third_hard_value: bool,
    fourth_split: Col,
    root_easy: CertifiedBinaryAssignmentLeaf,
    second_easy: CertifiedBinaryAssignmentLeaf,
    third_easy: CertifiedBinaryAssignmentLeaf,
    fourth_zero: CertifiedBinaryAssignmentLeaf,
    fourth_one: CertifiedBinaryAssignmentLeaf,
}

impl CertifiedAdaptiveFiveLeafComb {
    /// Caller-selected split at the root.
    #[must_use]
    pub fn root_split(&self) -> Col {
        self.root_split
    }

    /// Value of the root split refined by [`Self::second_split`].
    #[must_use]
    pub fn root_hard_value(&self) -> bool {
        self.root_hard_value
    }

    /// Target-FSB-selected split below the hard root child.
    #[must_use]
    pub fn second_split(&self) -> Col {
        self.second_split
    }

    /// Value of the second split refined by [`Self::third_split`].
    #[must_use]
    pub fn second_hard_value(&self) -> bool {
        self.second_hard_value
    }

    /// Target-FSB-selected split below the first two hard values.
    #[must_use]
    pub fn third_split(&self) -> Col {
        self.third_split
    }

    /// Value of the third split refined by [`Self::fourth_split`].
    #[must_use]
    pub fn third_hard_value(&self) -> bool {
        self.third_hard_value
    }

    /// Target-FSB-selected terminal split.
    #[must_use]
    pub fn fourth_split(&self) -> Col {
        self.fourth_split
    }

    /// Number of certificate leaves.
    #[must_use]
    pub const fn num_leaves(&self) -> usize {
        5
    }

    /// Close every feasible leaf's conditional lower row against `upper_row`,
    /// retain direct infeasible-leaf witnesses, and return a verified
    /// whole-comb infeasibility certificate.
    ///
    /// `model` must preserve the relaxation facts used to derive this carrier,
    /// restore all four split columns' integrality, and contain `upper_row`.
    /// Branch identities, orientations, leaf assumptions, and the completed
    /// arbitrary tree are rechecked exactly; any mismatch returns `None`.
    #[must_use]
    pub fn into_farkas_against_row_upper(
        self,
        model: &Model,
        upper_row: Row,
    ) -> Option<MilpInfeasibilityCertificate> {
        if upper_row.index() >= model.num_rows() {
            return None;
        }

        fn branch_bound(col: Col, value: bool) -> (Col, BoundSide, BigRational) {
            if value {
                (col, BoundSide::Lower, BigRational::from_integer(1.into()))
            } else {
                (col, BoundSide::Upper, BigRational::zero())
            }
        }

        fn leaf_node(
            leaf: CertifiedBinaryAssignmentLeaf,
            branch_bounds: &[(Col, BoundSide, BigRational)],
            model: &Model,
            upper_row: Row,
        ) -> Option<TreeNode> {
            let farkas = match leaf {
                CertifiedBinaryAssignmentLeaf::ConditionalRow(row) => {
                    row.into_farkas_against_row_upper(model, upper_row, branch_bounds)?
                }
                CertifiedBinaryAssignmentLeaf::Infeasible(farkas) => farkas,
            };
            Some(TreeNode::Leaf { farkas })
        }

        let Self {
            root_split,
            root_hard_value,
            second_split,
            second_hard_value,
            third_split,
            third_hard_value,
            fourth_split,
            root_easy,
            second_easy,
            third_easy,
            fourth_zero,
            fourth_one,
        } = self;
        let splits = [root_split, second_split, third_split, fourth_split];
        for (index, &split) in splits.iter().enumerate() {
            if split.index() >= model.num_cols() || splits[..index].contains(&split) {
                return None;
            }
        }

        let root_easy_node = leaf_node(
            root_easy,
            &[branch_bound(root_split, !root_hard_value)],
            model,
            upper_row,
        )?;
        let second_easy_node = leaf_node(
            second_easy,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, !second_hard_value),
            ],
            model,
            upper_row,
        )?;
        let third_easy_node = leaf_node(
            third_easy,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, second_hard_value),
                branch_bound(third_split, !third_hard_value),
            ],
            model,
            upper_row,
        )?;
        let fourth_zero_node = leaf_node(
            fourth_zero,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, second_hard_value),
                branch_bound(third_split, third_hard_value),
                branch_bound(fourth_split, false),
            ],
            model,
            upper_row,
        )?;
        let fourth_one_node = leaf_node(
            fourth_one,
            &[
                branch_bound(root_split, root_hard_value),
                branch_bound(second_split, second_hard_value),
                branch_bound(third_split, third_hard_value),
                branch_bound(fourth_split, true),
            ],
            model,
            upper_row,
        )?;

        let fourth_node = TreeNode::Split {
            col: fourth_split,
            cut: BigRational::zero(),
            lo: Box::new(fourth_zero_node),
            hi: Box::new(fourth_one_node),
        };
        let (third_lo, third_hi) = if third_hard_value {
            (third_easy_node, fourth_node)
        } else {
            (fourth_node, third_easy_node)
        };
        let third_node = TreeNode::Split {
            col: third_split,
            cut: BigRational::zero(),
            lo: Box::new(third_lo),
            hi: Box::new(third_hi),
        };
        let (second_lo, second_hi) = if second_hard_value {
            (second_easy_node, third_node)
        } else {
            (third_node, second_easy_node)
        };
        let second_node = TreeNode::Split {
            col: second_split,
            cut: BigRational::zero(),
            lo: Box::new(second_lo),
            hi: Box::new(second_hi),
        };
        let (root_lo, root_hi) = if root_hard_value {
            (root_easy_node, second_node)
        } else {
            (second_node, root_easy_node)
        };
        let certificate = MilpInfeasibilityCertificate {
            root: TreeNode::Split {
                col: root_split,
                cut: BigRational::zero(),
                lo: Box::new(root_lo),
                hi: Box::new(root_hi),
            },
        };
        certificate.verify(model).ok()?;
        Some(certificate)
    }
}

/// Solve and exactify one leaf of an adaptive assignment tree.
///
/// The returned [`Candidate`] lets the next exact leaf inherit this leaf's
/// basis. Both successful leaf forms are proof-bearing: an optimal float solve
/// must yield a strictly sufficient exact conditional row, while a
/// primal-infeasible solve must yield an exact Farkas witness.
#[allow(clippy::too_many_arguments)]
fn exactify_adaptive_tree_leaf(
    model: &Model,
    lp: &FloatLp,
    q: &[f64],
    assignments: &[(Col, bool)],
    warm: Option<&Candidate>,
    threshold: &BigRational,
    deadline: Option<Instant>,
    trace_context: &str,
) -> Option<(CertifiedBinaryAssignmentLeaf, Candidate)> {
    if deadline.is_some_and(|limit| Instant::now() >= limit) {
        return None;
    }
    let mut lower = lp.lower.clone();
    let mut upper = lp.upper.clone();
    let mut leaf_model = model.clone();
    for &(col, one) in assignments {
        let value = f64::from(u8::from(one));
        lower[col.index()] = value;
        upper[col.index()] = value;
        leaf_model.fix_col(col, value);
    }
    let warm = warm.map(|candidate| (&candidate.basis[..], &candidate.at[..]));
    let candidate = lp.solve_bounded(&lower, &upper, warm, deadline);
    let leaf = match candidate.status {
        SimplexStatus::Optimal => {
            CertifiedBinaryAssignmentLeaf::ConditionalRow(certified_weak_row_from_duals(
                &leaf_model,
                q,
                &candidate.duals,
                deadline,
                Some(threshold),
                trace_context,
            )?)
        }
        SimplexStatus::PrimalInfeasible => CertifiedBinaryAssignmentLeaf::Infeasible(
            exact_farkas_from_float_ray(&leaf_model, &candidate.farkas)?,
        ),
        _ => return None,
    };
    if deadline.is_some_and(|limit| Instant::now() >= limit) {
        return None;
    }
    Some((leaf, candidate))
}

/// An LP session: one continuous model, many objectives, warm re-solves, and
/// certificates on every verdict.
pub struct LpSession {
    model: Model,
    opts: SolveOpts,
    /// Materialized only when the float lane declines. Kept across exact
    /// re-solves for warm starts and dropped when the model box narrows.
    lp: Option<ExactLp>,
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
            lp: None,
        })
    }

    /// Lower one float LP with the path advice scoped to this session.
    fn float_lp(&self, objective: &[(u32, f64)], sense: Sense) -> Option<FloatLp> {
        let mut lp = FloatLp::from_model(&self.model, objective, sense)?;
        lp.set_chain_distress_probe_iters(self.opts.chain_distress_probe_iters());
        if self.opts.range_logical_triangular_crash() {
            lp.request_range_logical_triangular_crash();
        }
        Some(lp)
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
    fn try_float_lane(
        &self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        deadline: Option<Instant>,
    ) -> Option<Outcome> {
        if !float_lane_enabled() {
            return None;
        }
        let mut lp = self.float_lp(coeffs, sense)?;
        lp.plain_cold = true; // session lane: keep the classic measured path (see `FloatLp::plain_cold`)
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

    /// Large-model cut harvesting does not need an exact primal vertex or an
    /// exact optimum: it needs a valid inequality. Search for an optimal float
    /// candidate, then reinterpret each of its two possible row-dual sign
    /// conventions as arbitrary advice and derive an exact weak-duality row.
    ///
    /// The inexpensive directed-rounding bound evaluator chooses the stronger
    /// sign convention first; only that proposal pays exact construction and
    /// verification. The other convention is attempted if the first exact
    /// proposal declines—or, for threshold-aware harvesting, if its verified
    /// bound is insufficient—while time remains. Failure is only a decline;
    /// the public harvest methods retain their exact-optimum fallback. This
    /// lane is restricted to models above the exact-basis replay cap, so small
    /// harvests keep their historical tight optimum and path.
    fn try_weak_dual_harvest(
        &self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        deadline: Option<Instant>,
        stronger_than: Option<&BigRational>,
    ) -> Option<CertifiedRow> {
        if !float_lane_enabled() || self.model.num_rows() <= MAX_EXACT_BASIS_ROWS {
            return None;
        }

        // `FloatLp::from_model` overwrites duplicate objective columns whereas
        // the API's linear form sums them. Decline this advisory lane rather
        // than prove a row for a different objective; the exact fallback
        // handles duplicates canonically.
        let mut seen = vec![false; self.model.num_cols()];
        for &(c, _) in coeffs {
            let slot = seen.get_mut(c as usize)?;
            if std::mem::replace(slot, true) {
                return None;
            }
        }

        let mut lp = self.float_lp(coeffs, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let cand = lp.solve(deadline);
        if cand.status != SimplexStatus::Optimal {
            return None;
        }

        // `lp.cost` is already the lower-form objective: q=c for Minimize and
        // q=-c for Maximize, so every returned row has the public lower-bound
        // orientation without a second sign transform.
        let q = &lp.cost[..lp.n];
        certified_weak_row_from_duals(
            &self.model,
            q,
            &cand.duals,
            deadline,
            stronger_than,
            "harvest weak",
        )
    }

    fn optimize_linear(
        &mut self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        model_obj_exact: Option<ExactObjective>,
    ) -> Outcome {
        let deadline = self.opts.effective_deadline(Instant::now());
        self.optimize_linear_until(coeffs, sense, offset, model_obj_exact, deadline, true)
    }

    /// As [`Self::optimize_linear`], under a deadline already pinned by the
    /// outer public operation. This prevents a declined advisory lane from
    /// restarting a per-solve `time_limit` for the exact fallback.
    /// `allow_float_lane` is false only after large-model harvesting already
    /// ran its float search; exact basis certification cannot accept those
    /// models, so repeating the identical search would be pure deadline loss.
    fn optimize_linear_until(
        &mut self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        model_obj_exact: Option<ExactObjective>,
        deadline: Option<Instant>,
        allow_float_lane: bool,
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
        if allow_float_lane && !self.model.has_inexact_coeffs() {
            if let Some(fast) = self.try_float_lane(coeffs, sense, offset, deadline) {
                return finish(fast, &self.model, &solved, &self.opts);
            }
        }

        // The exact rim is the fallback authority. Materialize it only after
        // the float lane declines, under the SAME fallback budget its solve
        // will use. This avoids carrying both full LP representations through
        // float search and prevents exact construction from overrunning an
        // already-expired deadline.
        let budget = Budget {
            deadline,
            max_iters: Budget::default_iters(self.model.num_cols() + self.model.num_rows()),
        };
        if self.lp.is_none() {
            let Some(lp) = ExactLp::new_within(&self.model, budget.deadline) else {
                return finish(
                    Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    },
                    &self.model,
                    &solved,
                    &self.opts,
                );
            };
            self.lp = Some(lp);
        }
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
        let lp = self
            .lp
            .as_mut()
            .expect("exact rim was materialized immediately above");
        let outcome = match lp.minimize(&solve_obj, &budget) {
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
                    model_values: lp.structural_values(),
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
        let mut lp = self.float_lp(&[(col.0, coeff)], Sense::Minimize)?;
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
    /// the model automatically; any materialized exact rim is discarded.
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
        self.lp = None;
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

    /// The shared implementation of [`Self::harvest_cut`] and
    /// [`Self::harvest_cut_stronger_than`]. `stronger_than` is in the returned
    /// row's lower-bound coordinates and is exclusive.
    fn harvest_cut_with_threshold(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        stronger_than: Option<&BigRational>,
    ) -> Option<CertifiedRow> {
        if coeffs
            .iter()
            .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }
        let u32_coeffs: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        // Pin one absolute deadline around float search, both exact weak-dual
        // proposals, and the exact-rim fallback. An insufficient weak row does
        // not earn a fresh time_limit.
        let deadline = self.opts.effective_deadline(Instant::now());
        if let Some(row) = self.try_weak_dual_harvest(&u32_coeffs, sense, deadline, stronger_than) {
            return Some(row);
        }
        let allow_float_lane = self.model.num_rows() <= MAX_EXACT_BASIS_ROWS;
        match self.optimize_linear_until(&u32_coeffs, sense, 0.0, None, deadline, allow_float_lane)
        {
            Outcome::Optimal {
                cert: Some(cert), ..
            } => {
                let row = cert.into_certified_row();
                row.verify(&self.model).ok()?;
                let sufficient = stronger_than.is_none_or(|threshold| &row.lb > threshold);
                if std::env::var_os("AY_MILP_TRACE").is_some() {
                    match stronger_than {
                        Some(threshold) => eprintln!(
                            "AY_MILP_TRACE harvest exact fallback: lb={} threshold={threshold} sufficient={sufficient}",
                            row.lb
                        ),
                        None => eprintln!(
                            "AY_MILP_TRACE harvest exact fallback: lb={} accepted",
                            row.lb
                        ),
                    }
                }
                sufficient.then_some(row)
            }
            _ => None,
        }
    }

    /// Harvest a certified valid inequality on `coeffs·x`.
    ///
    /// On small models, solves the linear objective exactly and returns the
    /// tight row `coeffs·x >= optimum` for Minimize (or the re-oriented
    /// maximize analogue). Above the exact-basis replay cap it may instead
    /// return a weaker row derived from an optimal float candidate by exact
    /// weak duality. In either case the result is a
    /// [`crate::cert::CertifiedRow`] independently verified against true model
    /// facts. A weak row need not be tight; anything that cannot produce a
    /// finite verified inequality falls through to the historical exact solve
    /// and otherwise yields `None` (fail-closed).
    pub fn harvest_cut(&mut self, coeffs: &[(Col, f64)], sense: Sense) -> Option<CertifiedRow> {
        self.harvest_cut_with_threshold(coeffs, sense, None)
    }

    /// Harvest a certified row whose exact lower bound is strictly stronger
    /// than `threshold`.
    ///
    /// The comparison is exact and exclusive: only `row.lb > threshold`
    /// succeeds. `threshold` is expressed in the returned lower-form row's
    /// coordinates. Thus Minimize uses `coeffs·x >= row.lb`, while Maximize is
    /// re-oriented as `(-coeffs)·x >= row.lb` and the caller supplies the
    /// threshold in those same negated coordinates.
    ///
    /// On large models both float-dual sign conventions are independently
    /// converted to exact, verified weak-duality rows. A valid row that is
    /// equal to or below `threshold` is insufficient, not a verdict: the other
    /// sign is tried and then the exact rim runs under the same absolute
    /// deadline. Returns `None` if no verified proof clears the threshold.
    pub fn harvest_cut_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        threshold: &BigRational,
    ) -> Option<CertifiedRow> {
        self.harvest_cut_with_threshold(coeffs, sense, Some(threshold))
    }

    /// Harvest a strictly sufficient root row, or two strictly sufficient
    /// rows from one warm binary split.
    ///
    /// This is the proof-oriented large-model alternative to
    /// [`Self::harvest_cut_stronger_than`]. It performs exactly one float root
    /// solve for the requested objective and first converts that candidate's
    /// duals into an exact, verified weak row. If the root row exceeds
    /// `threshold`, [`CertifiedSplitHarvest::Root`] returns immediately. If
    /// not, the SAME root basis seeds two bound-only re-solves with `split`
    /// fixed to 0 and 1. Each child dual is exactified and verified against its
    /// own fixed box; [`CertifiedSplitHarvest::Split`] is returned only when
    /// BOTH child rows exceed the threshold exactly.
    ///
    /// `split` must have the exact relaxed box `[0, 1]`. This makes the two
    /// fixed child rows line up with a complete integer split `x <= 0` /
    /// `x >= 1` in a [`crate::TreeNode`]. The objective and threshold use the
    /// same lower-form convention as [`Self::harvest_cut_stronger_than`]:
    /// Minimize returns `coeffs·x >= lb`, Maximize returns
    /// `(-coeffs)·x >= lb`.
    ///
    /// One absolute session deadline is shared by the root solve, both sign
    /// proposals, both warm children, and exact row construction. Simplex and
    /// exact construction poll it internally; the two directed-rounding
    /// matrix scans check it between complete passes. There is deliberately no
    /// exact-optimum fallback: `None` is the fail-closed result when the warm
    /// proof probe is inconclusive or the deadline expires.
    #[must_use]
    pub fn harvest_cut_or_binary_split_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        split: Col,
        threshold: &BigRational,
    ) -> Option<CertifiedSplitHarvest> {
        if !float_lane_enabled()
            || split.index() >= self.model.num_cols()
            || self.model.col_bounds(split) != (0.0, 1.0)
            || coeffs
                .iter()
                .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }

        // FloatLp assigns rather than sums duplicate objective columns. This
        // weak-only API has no exact fallback, so duplicates must decline.
        let mut seen = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen.get_mut(col.index())?, true) {
                return None;
            }
        }

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        let deadline = self.opts.effective_deadline(Instant::now());
        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let root = lp.solve(deadline);
        if root.status != SimplexStatus::Optimal {
            return None;
        }
        let q = &lp.cost[..lp.n];
        if let Some(row) = certified_weak_row_from_duals(
            &self.model,
            q,
            &root.duals,
            deadline,
            Some(threshold),
            "split root weak",
        ) {
            return Some(CertifiedSplitHarvest::Root(row));
        }

        let expired = || deadline.is_some_and(|limit| Instant::now() >= limit);
        let derive_child = |value: f64, trace_context: &str| -> Option<CertifiedRow> {
            if expired() {
                return None;
            }
            let mut lower = lp.lower.clone();
            let mut upper = lp.upper.clone();
            lower[split.index()] = value;
            upper[split.index()] = value;
            let candidate =
                lp.solve_bounded(&lower, &upper, Some((&root.basis, &root.at)), deadline);
            if candidate.status != SimplexStatus::Optimal {
                return None;
            }
            let mut child_model = self.model.clone();
            child_model.fix_col(split, value);
            certified_weak_row_from_duals(
                &child_model,
                q,
                &candidate.duals,
                deadline,
                Some(threshold),
                trace_context,
            )
        };
        let zero = derive_child(0.0, "split zero weak")?;
        let one = derive_child(1.0, "split one weak")?;
        Some(CertifiedSplitHarvest::Split { zero, one })
    }

    /// Exactify every selected assignment from an already-solved target root.
    ///
    /// Both the fixed-tree and target-FSB APIs enter here. Keeping the root
    /// candidate and [`FloatLp`] explicit makes the fused contract visible:
    /// selection never earns a second cold solve. The default and target-FSB
    /// paths warm the first exact leaf from the original true-objective root;
    /// a fixed-tree canary may first build an advice-only prefix basis.
    fn harvest_binary_assignment_tree_from_root(
        &self,
        lp: &FloatLp,
        root: Candidate,
        splits: &[Col],
        threshold: &BigRational,
        deadline: Option<Instant>,
        warm_start: Option<FixedAssignmentTreeWarmStart>,
    ) -> Option<CertifiedBinaryTreeHarvest> {
        let depth = splits.len();
        let expired = || deadline.is_some_and(|limit| Instant::now() >= limit);
        if expired() {
            return None;
        }
        let leaf_count = 1usize.checked_shl(u32::try_from(depth).ok()?)?;
        let start_assignment = fixed_assignment_tree_start_assignment(warm_start);
        if start_assignment >= leaf_count {
            return None;
        }
        let mut leaves: Vec<Option<CertifiedBinaryAssignmentLeaf>> = vec![None; leaf_count];
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        let mut leaf_model = self.model.clone();
        let mut previous: Option<Candidate> = Some(root);
        let q = &lp.cost[..lp.n];

        if warm_start.is_some() {
            let prefix_time_limit = match warm_start? {
                FixedAssignmentTreeWarmStart::ProgressivePrefix {
                    prefix_time_limit, ..
                }
                | FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                    prefix_time_limit,
                    ..
                } => prefix_time_limit,
            };
            // Advice only: progressively approach the first complete
            // assignment by changing one bound at a time. Prefix calls take
            // the typed primal-advice lane: a local cap advances phase I from
            // the previous stopped basis instead of paying for a warm-dual
            // walk whose capped failure would roll all progress back. The last
            // split is deliberately left free here so step zero below remains
            // the first proof-bearing leaf.
            for prefix_len in 1..depth {
                if expired() {
                    return None;
                }
                let mut prefix_lower = lp.lower.clone();
                let mut prefix_upper = lp.upper.clone();
                for (level, &split) in splits[..prefix_len].iter().enumerate() {
                    let bit = depth - level - 1;
                    let value = if start_assignment & (1usize << bit) == 0 {
                        0.0
                    } else {
                        1.0
                    };
                    prefix_lower[split.index()] = value;
                    prefix_upper[split.index()] = value;
                }
                let prior = previous.take()?;
                let candidate = lp.solve_bounded_with_mode(
                    &prefix_lower,
                    &prefix_upper,
                    Some((&prior.basis[..], &prior.at[..])),
                    WarmSolveMode::PrimalAdvice,
                    capped_assignment_tree_advice_deadline(deadline, prefix_time_limit),
                );
                let basis_changes = prior
                    .basis
                    .iter()
                    .zip(&candidate.basis)
                    .filter(|(before, after)| before != after)
                    .count();
                drop(prior);
                if !matches!(
                    candidate.status,
                    SimplexStatus::Optimal
                        | SimplexStatus::PrimalInfeasible
                        | SimplexStatus::Stopped
                ) || expired()
                {
                    return None;
                }
                if std::env::var_os("AY_MILP_TRACE").is_some() {
                    eprintln!(
                        "AY_MILP_TRACE assignment tree prefix bridge: \
                         fixed={prefix_len}/{depth} start={start_assignment:0depth$b} \
                         mode={:?} status={:?} basis_changes={basis_changes}",
                        WarmSolveMode::PrimalAdvice,
                        candidate.status,
                    );
                }
                previous = Some(candidate);
            }
        }

        for step in 0..leaf_count {
            if expired() {
                return None;
            }
            let assignment = (step ^ (step >> 1)) ^ start_assignment;
            for (level, &split) in splits.iter().enumerate() {
                let bit = depth - level - 1;
                let value = if assignment & (1usize << bit) == 0 {
                    0.0
                } else {
                    1.0
                };
                lower[split.index()] = value;
                upper[split.index()] = value;
                leaf_model.fix_col(split, value);
            }

            let prior = previous.take()?;
            let incoming_status = prior.status;
            let warm_mode = fixed_assignment_tree_leaf_warm_mode(step, warm_start, incoming_status);
            // Every bounded solve, including a stopped `PrimalAdvice` prefix,
            // extracts row duals under the TRUE objective before returning its
            // candidate. Once the final assignment above is installed, those
            // cached floats are already legal weak-duality advice for this
            // narrower leaf. Try them before paying for another float solve.
            //
            // The exact row builder trusts none of the floats and accepts only
            // a verified row STRICTLY beyond `threshold`. On any decline the
            // untouched `prior` basis takes the historical continuation below.
            if warm_mode == WarmSolveMode::PrimalProofContinuation {
                let trace_context =
                    format!("assignment tree leaf {assignment:0depth$b} cached weak");
                if let Some(row) = certified_cached_assignment_tree_leaf_row(
                    warm_mode,
                    &leaf_model,
                    q,
                    &prior.duals,
                    deadline,
                    threshold,
                    &trace_context,
                ) {
                    if expired() {
                        return None;
                    }
                    if std::env::var_os("AY_MILP_TRACE").is_some() {
                        eprintln!(
                            "AY_MILP_TRACE assignment tree first proof leaf: \
                             incoming={incoming_status:?} mode={warm_mode:?} \
                             route=cached-dual-verified"
                        );
                    }
                    leaves[assignment] = Some(CertifiedBinaryAssignmentLeaf::ConditionalRow(row));
                    previous = Some(prior);
                    continue;
                }
            }
            // Exact reconstruction and verification are deadline-aware, but
            // may consume the last available instant before declining. Do not
            // enter warm-start setup after the outer proof budget has expired.
            if expired() {
                return None;
            }
            let candidate = lp.solve_bounded_with_mode(
                &lower,
                &upper,
                Some((&prior.basis[..], &prior.at[..])),
                warm_mode,
                deadline,
            );
            drop(prior);
            if step == 0 && warm_start.is_some() && std::env::var_os("AY_MILP_TRACE").is_some() {
                eprintln!(
                    "AY_MILP_TRACE assignment tree first proof leaf: \
                     incoming={incoming_status:?} mode={warm_mode:?} \
                     status={:?}",
                    candidate.status
                );
            }
            let leaf = match candidate.status {
                SimplexStatus::Optimal => {
                    let trace_context = format!("assignment tree leaf {assignment:0depth$b} weak");
                    CertifiedBinaryAssignmentLeaf::ConditionalRow(certified_weak_row_from_duals(
                        &leaf_model,
                        q,
                        &candidate.duals,
                        deadline,
                        Some(threshold),
                        &trace_context,
                    )?)
                }
                SimplexStatus::PrimalInfeasible => CertifiedBinaryAssignmentLeaf::Infeasible(
                    exact_farkas_from_float_ray(&leaf_model, &candidate.farkas)?,
                ),
                _ => return None,
            };
            if expired() {
                return None;
            }
            leaves[assignment] = Some(leaf);
            previous = Some(candidate);
        }

        let leaves = leaves.into_iter().collect::<Option<Vec<_>>>()?;
        Some(CertifiedBinaryTreeHarvest::Tree(
            CertifiedBinaryAssignmentTree {
                split_cols: splits.to_vec(),
                leaves,
            },
        ))
    }

    /// Harvest a strictly sufficient root row, or sufficient rows for every
    /// assignment to one through four relaxed binary-candidate columns.
    ///
    /// By default, the root relaxation is solved once, cold, with eager affine
    /// crash. A sufficient exact weak-duality row returns immediately.
    /// Otherwise all `2^splits.len()` fixed assignments are solved in Gray-code
    /// order, so consecutive warm re-solves change exactly one column bound.
    /// Each solve starts from the previous leaf's basis, while returned rows are
    /// stored in canonical binary order for deterministic tree composition.
    ///
    /// [`SolveOpts::with_fixed_assignment_tree_warm_start`] can default-off
    /// translate the Gray start, build its first leaf basis through progressive
    /// locally capped prefixes, and locally cap the optional root fast path.
    /// Those solves remain advice only—even when stopped at a local cap—and
    /// never enter the returned proof object. If that configured chain hands a
    /// non-optimal candidate to the first complete leaf, that leaf alone
    /// continues primal work directly; its result remains verdict-bearing and
    /// passes through the identical exact weak-row or Farkas gate below. Every
    /// later Gray leaf uses the historical normal warm solve.
    ///
    /// Every `split` must be distinct and have the exact relaxed box `[0, 1]`.
    /// A feasible leaf row is independently exactified and must satisfy the
    /// strict exact comparison `row.lb > threshold`; an LP-infeasible leaf is
    /// retained only when its phase-I ray exactifies to a verified Farkas
    /// witness. One inconclusive leaf rejects the entire harvest. One absolute
    /// session deadline is passed to every float solve and checked between
    /// exact passes. Individual directed-rounding scans and exact verification
    /// are not preemptible, so they can finish just after that deadline. There
    /// is no exact-optimum fallback.
    #[must_use]
    pub fn harvest_cut_or_binary_assignment_tree_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        splits: &[Col],
        threshold: &BigRational,
    ) -> Option<CertifiedBinaryTreeHarvest> {
        let depth = splits.len();
        if !float_lane_enabled()
            || depth == 0
            || depth > MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES.ilog2() as usize
            || coeffs
                .iter()
                .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }

        let mut seen_splits = vec![false; self.model.num_cols()];
        for &split in splits {
            if split.index() >= self.model.num_cols()
                || self.model.col_bounds(split) != (0.0, 1.0)
                || std::mem::replace(seen_splits.get_mut(split.index())?, true)
            {
                return None;
            }
        }

        // FloatLp assigns rather than sums duplicate objective columns. This
        // weak-only API has no exact fallback, so duplicates must decline.
        let mut seen_objective = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen_objective.get_mut(col.index())?, true) {
                return None;
            }
        }

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        let deadline = self.opts.effective_deadline(Instant::now());
        let expired = || deadline.is_some_and(|limit| Instant::now() >= limit);
        if expired() {
            return None;
        }

        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let warm_start = self.opts.fixed_assignment_tree_warm_start();
        let leaf_count = 1usize.checked_shl(u32::try_from(depth).ok()?)?;
        if fixed_assignment_tree_start_assignment(warm_start) >= leaf_count {
            return None;
        }
        let root_deadline = match warm_start {
            Some(FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                root_time_limit,
                ..
            }) => capped_assignment_tree_advice_deadline(deadline, root_time_limit),
            None | Some(FixedAssignmentTreeWarmStart::ProgressivePrefix { .. }) => deadline,
        };
        let root = lp.solve(root_deadline);
        if root.status == SimplexStatus::Optimal {
            let q = &lp.cost[..lp.n];
            if let Some(row) = certified_weak_row_from_duals(
                &self.model,
                q,
                &root.duals,
                deadline,
                Some(threshold),
                "assignment tree root weak",
            ) {
                return Some(CertifiedBinaryTreeHarvest::Root(row));
            }
        } else if !matches!(
            warm_start,
            Some(FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix { .. })
        ) || root.status != SimplexStatus::Stopped
            || expired()
        {
            return None;
        }
        if warm_start.is_some() && std::env::var_os("AY_MILP_TRACE").is_some() {
            eprintln!(
                "AY_MILP_TRACE assignment tree root start: strategy={warm_start:?} \
                 status={:?}",
                root.status
            );
        }

        self.harvest_binary_assignment_tree_from_root(
            &lp, root, splits, threshold, deadline, warm_start,
        )
    }

    /// Select and exactly harvest a depth-two tree with target-objective FSB.
    ///
    /// `candidates` is an ordered shortlist of two through eight distinct
    /// relaxed `[0, 1]` columns. The true requested objective is solved cold
    /// exactly once. A sufficient verified root row returns immediately.
    /// Otherwise the selector:
    ///
    /// 1. quick-probes both children of every candidate from that same saved
    ///    root basis and selects the largest worst-child rigorous lower bound;
    /// 2. quick-probes all four joint assignments with every remaining
    ///    candidate, again from the root basis, and selects the largest
    ///    worst-of-four bound; and
    /// 3. solves and exactifies the chosen pair's four leaves in Gray order.
    ///
    /// Strict `>` comparisons preserve caller order on every tie. Probe duals
    /// are advice only: each score is independently bounded by outward-rounded
    /// weak duality under the probed box, while only exact verified rows or
    /// Farkas witnesses enter the returned [`CertifiedBinaryTreeHarvest`].
    /// As with the other harvest APIs, Minimize scores `coeffs·x` while
    /// Maximize is represented in the lower form `(-coeffs)·x`; the report's
    /// lower bounds are expressed in that same lower-form frame.
    ///
    /// The advice scan costs exactly `6*candidates.len() - 4` calls. It is
    /// rejected before the first probe unless the configured pivot, call,
    /// wall, and local scoring-workspace caps cover that complete scan.
    /// Expiry or a simplex memory decline discards the whole selection; a
    /// partial ranking is never used. The probe wall cap does not shorten the
    /// session's outer deadline for the exact leaves.
    ///
    /// Models carrying rounded `f64` proxies plus an exact coefficient
    /// side-store decline this selector: its quick score scans the `f64`
    /// matrix. The fixed-tree proof API remains available there and exactifies
    /// every returned leaf against the true model.
    #[must_use]
    pub fn harvest_cut_or_target_fsb_assignment_tree_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        candidates: &[Col],
        threshold: &BigRational,
        fsb_opts: &TargetFsbOpts,
    ) -> Option<(CertifiedBinaryTreeHarvest, TargetFsbReport)> {
        let candidate_count = candidates.len();
        if !float_lane_enabled()
            || !(2..=MAX_TARGET_FSB_CANDIDATES).contains(&candidate_count)
            || self.model.has_inexact_coeffs()
            || coeffs
                .iter()
                .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }

        let mut seen_candidates = vec![false; self.model.num_cols()];
        for &candidate in candidates {
            if candidate.index() >= self.model.num_cols()
                || self.model.col_bounds(candidate) != (0.0, 1.0)
                || std::mem::replace(seen_candidates.get_mut(candidate.index())?, true)
            {
                return None;
            }
        }
        let mut seen_objective = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen_objective.get_mut(col.index())?, true) {
                return None;
            }
        }

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        let outer_deadline = self.opts.effective_deadline(Instant::now());
        let outer_expired = || outer_deadline.is_some_and(|limit| Instant::now() >= limit);
        if outer_expired() {
            return None;
        }

        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let root = lp.solve(outer_deadline);
        if root.status != SimplexStatus::Optimal {
            return None;
        }
        let q = &lp.cost[..lp.n];
        let root_row = certified_weak_row_from_duals(
            &self.model,
            q,
            &root.duals,
            outer_deadline,
            Some(threshold),
            "target FSB root weak",
        );
        if outer_expired() {
            return None;
        }
        if let Some(row) = root_row {
            return Some((
                CertifiedBinaryTreeHarvest::Root(row),
                TargetFsbReport {
                    candidate_count,
                    probe_calls: 0,
                    selected_splits: Vec::new(),
                    first_worst_lower_bound: None,
                    joint_worst_lower_bound: None,
                },
            ));
        }

        let required_calls = candidate_count.checked_mul(6)?.checked_sub(4)?;
        if fsb_opts.max_probe_pivots_per_call == 0
            || fsb_opts.probe_time_limit.is_zero()
            || fsb_opts.max_probe_calls < required_calls
        {
            return None;
        }

        // Incremental peak retained by the fused selector, in f64 slots:
        // lower+upper computational boxes, one reusable safe-bound
        // reduced-cost interval per structural column, probe extract's
        // transient values, the returned duals, safe-bound's clamped dual
        // copy, and a small score allowance. Root Candidate, FloatLp/Simplex
        // state, and the optional LU reuse snapshot are solver state governed
        // by the simplex LU fill guard rather than this local workspace cap.
        let n = self.model.num_cols();
        let m = self.model.num_rows();
        let cols = n.checked_add(m)?;
        let scratch_slots = cols
            .checked_mul(2)?
            .checked_add(n.checked_mul(2)?)?
            .checked_add(cols)?
            .checked_add(m.checked_mul(2)?)?
            .checked_add(candidate_count.checked_mul(4)?)?;
        let scratch_bytes = scratch_slots.checked_mul(size_of::<f64>())?;
        if scratch_bytes > fsb_opts.max_probe_scratch_bytes {
            return None;
        }

        let probe_start = Instant::now();
        let wall_deadline = probe_start.checked_add(fsb_opts.probe_time_limit)?;
        let probe_deadline = outer_deadline.map_or(wall_deadline, |outer| outer.min(wall_deadline));
        if Instant::now() >= probe_deadline {
            return None;
        }

        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        let mut rc_scratch = vec![(0.0, 0.0); lp.n];
        let mut probe_calls = 0usize;
        let reuse = lp.arm_probe_reuse();
        let mut probe_bound = |lower: &[f64], upper: &[f64]| -> Option<f64> {
            if probe_calls >= fsb_opts.max_probe_calls || Instant::now() >= probe_deadline {
                return None;
            }
            probe_calls += 1;
            let duals = lp.probe_duals_fail_closed(
                lower,
                upper,
                Some((&root.basis, &root.at)),
                fsb_opts.max_probe_pivots_per_call,
                Some(probe_deadline),
            )?;
            if Instant::now() >= probe_deadline {
                return None;
            }
            let score = target_fsb_probe_score(&lp, &duals, lower, upper, &mut rc_scratch);
            if Instant::now() >= probe_deadline {
                return None;
            }
            Some(score.unwrap_or(f64::NEG_INFINITY))
        };

        let mut first_index = 0usize;
        let mut first_worst = f64::NEG_INFINITY;
        for (index, &candidate) in candidates.iter().enumerate() {
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 0.0;
            let zero = probe_bound(&lower, &upper)?;
            lower[candidate.index()] = 1.0;
            upper[candidate.index()] = 1.0;
            let one = probe_bound(&lower, &upper)?;
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 1.0;
            let worst = zero.min(one);
            if trace {
                eprintln!(
                    "AY_MILP_TRACE target FSB first candidate: col={} zero={zero:.17e} \
                     one={one:.17e} worst={worst:.17e}",
                    candidate.index()
                );
            }
            if worst > first_worst {
                first_index = index;
                first_worst = worst;
            }
        }

        let first = candidates[first_index];
        let mut second_index = (0..candidate_count).find(|&i| i != first_index)?;
        let mut joint_worst = f64::NEG_INFINITY;
        for (index, &candidate) in candidates.iter().enumerate() {
            if index == first_index {
                continue;
            }
            let mut bounds = [f64::NEG_INFINITY; 4];
            for first_value in 0..=1usize {
                lower[first.index()] = first_value as f64;
                upper[first.index()] = first_value as f64;
                for second_value in 0..=1usize {
                    lower[candidate.index()] = second_value as f64;
                    upper[candidate.index()] = second_value as f64;
                    bounds[first_value * 2 + second_value] = probe_bound(&lower, &upper)?;
                }
                lower[candidate.index()] = 0.0;
                upper[candidate.index()] = 1.0;
            }
            lower[first.index()] = 0.0;
            upper[first.index()] = 1.0;
            let worst = bounds.into_iter().fold(f64::INFINITY, f64::min);
            if trace {
                eprintln!(
                    "AY_MILP_TRACE target FSB joint candidate: first_col={} \
                     second_col={} b00={:.17e} b01={:.17e} b10={:.17e} \
                     b11={:.17e} worst={worst:.17e}",
                    first.index(),
                    candidate.index(),
                    bounds[0],
                    bounds[1],
                    bounds[2],
                    bounds[3],
                );
            }
            if worst > joint_worst {
                second_index = index;
                joint_worst = worst;
            }
        }
        if probe_calls != required_calls || Instant::now() >= probe_deadline {
            return None;
        }
        let selected = [first, candidates[second_index]];
        if trace {
            eprintln!(
                "AY_MILP_TRACE target FSB selected: first_col={} first_worst={first_worst:.17e} \
                 second_col={} joint_worst={joint_worst:.17e} probes={probe_calls}/{required_calls}",
                selected[0].index(),
                selected[1].index(),
            );
        }
        drop(reuse);

        let harvest = self.harvest_binary_assignment_tree_from_root(
            &lp,
            root,
            &selected,
            threshold,
            outer_deadline,
            None,
        )?;
        Some((
            harvest,
            TargetFsbReport {
                candidate_count,
                probe_calls,
                selected_splits: selected.to_vec(),
                first_worst_lower_bound: first_worst.is_finite().then_some(first_worst),
                joint_worst_lower_bound: joint_worst.is_finite().then_some(joint_worst),
            },
        ))
    }

    /// Exactly harvest an adaptive three-leaf tree with target-objective FSB.
    ///
    /// `candidates` is an ordered shortlist of two through eight distinct
    /// relaxed `[0, 1]` columns. `root_candidate_index` chooses the root split,
    /// and `hard_value` chooses which root child (`false` = 0, `true` = 1) is
    /// refined. The opposite, easy child is solved and exactified first. This
    /// both fails closed before advice when the sibling cannot prove the target
    /// and retains an exact Farkas leaf when that child is LP-infeasible.
    ///
    /// If the root row is insufficient and the easy child is certified, every
    /// remaining candidate is quick-probed at values 0 and 1 below the hard
    /// root child. Every probe starts from the saved true-objective root basis,
    /// and its score is a rigorous [`crate::bab::safe_bound`] over that exact
    /// computational box. The largest worst-child score wins; strict `>`
    /// comparisons preserve caller order on ties. Only the selected partner's
    /// two hard grandchildren are then solved and exactified.
    ///
    /// The advice scan costs exactly `2 * (candidates.len() - 1)` calls. It is
    /// rejected before the first probe unless [`TargetFsbOpts`] covers the
    /// complete scan. Probe duals select a tree but never enter its proof: each
    /// returned leaf is either a verified exact conditional row strictly above
    /// `threshold` or an exact Farkas witness. The opaque carrier's
    /// [`CertifiedAdaptiveThreeLeafTree::into_farkas_against_row_upper`] method
    /// reconstructs and verifies the complete asymmetric tree before returning
    /// a certificate.
    ///
    /// The root fast path is allowed and ignores advice caps. Models carrying
    /// rounded `f64` coefficient proxies decline because selection scans the
    /// computational matrix. The existing complete depth-two target-FSB API is
    /// independent of this diagnostic surface.
    #[must_use]
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        candidates: &[Col],
        root_candidate_index: usize,
        hard_value: bool,
        threshold: &BigRational,
        fsb_opts: &TargetFsbOpts,
    ) -> Option<(
        CertifiedAdaptiveThreeLeafHarvest,
        AdaptiveThreeLeafTargetFsbReport,
    )> {
        let candidate_count = candidates.len();
        let root_split = *candidates.get(root_candidate_index)?;
        if !float_lane_enabled()
            || !(2..=MAX_TARGET_FSB_CANDIDATES).contains(&candidate_count)
            || self.model.has_inexact_coeffs()
            || coeffs
                .iter()
                .any(|&(c, a)| c.index() >= self.model.num_cols() || !a.is_finite())
        {
            return None;
        }

        let mut seen_candidates = vec![false; self.model.num_cols()];
        for &candidate in candidates {
            if candidate.index() >= self.model.num_cols()
                || self.model.col_bounds(candidate) != (0.0, 1.0)
                || std::mem::replace(seen_candidates.get_mut(candidate.index())?, true)
            {
                return None;
            }
        }
        let mut seen_objective = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen_objective.get_mut(col.index())?, true) {
                return None;
            }
        }

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(c, a)| (c.0, a)).collect();
        let outer_deadline = self.opts.effective_deadline(Instant::now());
        let outer_expired = || outer_deadline.is_some_and(|limit| Instant::now() >= limit);
        if outer_expired() {
            return None;
        }

        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let root = lp.solve(outer_deadline);
        if root.status != SimplexStatus::Optimal {
            return None;
        }
        let q = &lp.cost[..lp.n];
        let root_row = certified_weak_row_from_duals(
            &self.model,
            q,
            &root.duals,
            outer_deadline,
            Some(threshold),
            "adaptive three-leaf root weak",
        );
        if outer_expired() {
            return None;
        }
        if let Some(row) = root_row {
            return Some((
                CertifiedAdaptiveThreeLeafHarvest::Root(row),
                AdaptiveThreeLeafTargetFsbReport {
                    candidate_count,
                    probe_calls: 0,
                    root_candidate_index,
                    root_split,
                    hard_value,
                    second_candidate_index: None,
                    second_split: None,
                    hard_grandchild_lower_bounds: None,
                },
            ));
        }

        // Exactify the unsplit sibling before spending any selection work. The
        // candidate is deliberately dropped: every advice call and the first
        // hard grandchild start from the saved true-objective root basis.
        let (easy, easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[(root_split, !hard_value)],
            Some(&root),
            threshold,
            outer_deadline,
            "adaptive three-leaf easy weak",
        )?;
        drop(easy_candidate);

        let required_calls = candidate_count.checked_sub(1)?.checked_mul(2)?;
        if fsb_opts.max_probe_pivots_per_call == 0
            || fsb_opts.probe_time_limit.is_zero()
            || fsb_opts.max_probe_calls < required_calls
        {
            return None;
        }

        // Incremental selection workspace, under the same accounting contract
        // as complete target-FSB: two boxes, one safe-bound interval per
        // structural column, probe extraction/duals and clamped-dual scratch,
        // plus a small score allowance.
        let n = self.model.num_cols();
        let m = self.model.num_rows();
        let cols = n.checked_add(m)?;
        let scratch_slots = cols
            .checked_mul(2)?
            .checked_add(n.checked_mul(2)?)?
            .checked_add(cols)?
            .checked_add(m.checked_mul(2)?)?
            .checked_add(candidate_count.checked_mul(2)?)?;
        let scratch_bytes = scratch_slots.checked_mul(size_of::<f64>())?;
        if scratch_bytes > fsb_opts.max_probe_scratch_bytes {
            return None;
        }

        let probe_start = Instant::now();
        let wall_deadline = probe_start.checked_add(fsb_opts.probe_time_limit)?;
        let probe_deadline = outer_deadline.map_or(wall_deadline, |outer| outer.min(wall_deadline));
        if Instant::now() >= probe_deadline {
            return None;
        }

        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        let hard = f64::from(u8::from(hard_value));
        lower[root_split.index()] = hard;
        upper[root_split.index()] = hard;
        let mut rc_scratch = vec![(0.0, 0.0); lp.n];
        let mut probe_calls = 0usize;
        let reuse = lp.arm_probe_reuse();
        let mut probe_bound = |lower: &[f64], upper: &[f64]| -> Option<f64> {
            if probe_calls >= fsb_opts.max_probe_calls || Instant::now() >= probe_deadline {
                return None;
            }
            probe_calls += 1;
            let duals = lp.probe_duals_fail_closed(
                lower,
                upper,
                Some((&root.basis, &root.at)),
                fsb_opts.max_probe_pivots_per_call,
                Some(probe_deadline),
            )?;
            if Instant::now() >= probe_deadline {
                return None;
            }
            let score = target_fsb_probe_score(&lp, &duals, lower, upper, &mut rc_scratch);
            if Instant::now() >= probe_deadline {
                return None;
            }
            Some(score.unwrap_or(f64::NEG_INFINITY))
        };

        let mut second_index = None;
        let mut selected_bounds = [f64::NEG_INFINITY; 2];
        let mut selected_worst = f64::NEG_INFINITY;
        for (index, &candidate) in candidates.iter().enumerate() {
            if index == root_candidate_index {
                continue;
            }
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 0.0;
            let zero = probe_bound(&lower, &upper)?;
            lower[candidate.index()] = 1.0;
            upper[candidate.index()] = 1.0;
            let one = probe_bound(&lower, &upper)?;
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 1.0;
            let worst = zero.min(one);
            if trace {
                eprintln!(
                    "AY_MILP_TRACE adaptive three-leaf candidate: root_col={} hard={} \
                     second_col={} zero={zero:.17e} one={one:.17e} worst={worst:.17e}",
                    root_split.index(),
                    u8::from(hard_value),
                    candidate.index(),
                );
            }
            if second_index.is_none() || worst > selected_worst {
                second_index = Some(index);
                selected_bounds = [zero, one];
                selected_worst = worst;
            }
        }
        if probe_calls != required_calls || Instant::now() >= probe_deadline {
            return None;
        }
        drop(reuse);

        let second_candidate_index = second_index?;
        let second_split = candidates[second_candidate_index];
        if trace {
            eprintln!(
                "AY_MILP_TRACE adaptive three-leaf selected: root_col={} hard={} \
                 second_col={} zero={:.17e} one={:.17e} worst={selected_worst:.17e} \
                 probes={probe_calls}/{required_calls}",
                root_split.index(),
                u8::from(hard_value),
                second_split.index(),
                selected_bounds[0],
                selected_bounds[1],
            );
        }

        let (hard_zero, hard_zero_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[(root_split, hard_value), (second_split, false)],
            Some(&root),
            threshold,
            outer_deadline,
            "adaptive three-leaf hard-zero weak",
        )?;
        let (hard_one, hard_one_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[(root_split, hard_value), (second_split, true)],
            Some(&hard_zero_candidate),
            threshold,
            outer_deadline,
            "adaptive three-leaf hard-one weak",
        )?;
        drop(hard_zero_candidate);
        drop(hard_one_candidate);

        Some((
            CertifiedAdaptiveThreeLeafHarvest::Tree(Box::new(CertifiedAdaptiveThreeLeafTree {
                root_split,
                hard_value,
                second_split,
                easy,
                hard_zero,
                hard_one,
            })),
            AdaptiveThreeLeafTargetFsbReport {
                candidate_count,
                probe_calls,
                root_candidate_index,
                root_split,
                hard_value,
                second_candidate_index: Some(second_candidate_index),
                second_split: Some(second_split),
                hard_grandchild_lower_bounds: Some(selected_bounds),
            },
        ))
    }

    /// Harvest a tree-only adaptive four-leaf comb with two target-FSB stages.
    ///
    /// `candidates` is an ordered shortlist of three through eight distinct
    /// relaxed `[0, 1]` columns. `root_candidate_index` and
    /// `root_hard_value` fix the comb's first edge. The hard root child is
    /// solved cold to optimality as an advice anchor. Stage one quick-probes
    /// both values of every remaining candidate below that child and selects
    /// the largest worst-child rigorous lower bound. The strictly lower
    /// selected child becomes the hard second value; `false` wins a tie. Stage
    /// two immediately selects a terminal split under both hard assignments.
    /// Only after both contiguous scans does the method exactify the root-easy,
    /// second-easy, and two terminal leaves.
    ///
    /// Every advice call starts from the saved root-hard anchor basis and is
    /// scored by [`crate::bab::safe_bound`] over its full computational box.
    /// Strict `>` comparisons preserve caller order on all candidate ties.
    /// Successful exact leaves carry only verified conditional rows strictly
    /// above `threshold` or exact Farkas witnesses. Root-easy and second-easy
    /// each warm-start directly from the hard anchor; terminal zero starts from
    /// second-easy and terminal one from terminal zero.
    ///
    /// The two complete scans cost exactly `2*(n-1)` and `2*(n-2)` quick calls,
    /// totaling `4*n-6` probes, plus one cold optimal root-hard anchor solve.
    /// Pivot, call, wall, and incremental scratch caps are preflighted for the
    /// complete quick-probe work before that anchor; partial rankings are never
    /// used. The per-call pivot and shared probe-wall caps do not govern the
    /// anchor, which remains bounded by the session's outer deadline and the
    /// simplex LU guard. One shared probe deadline spans the two contiguous
    /// advice stages only. The scratch account includes the retained root-hard
    /// candidate used as every probe's warm seed. Probe basis/`at` retention is
    /// deliberately deferred: this diagnostic pass uses the existing dual-only
    /// probe API.
    ///
    /// This surface is tree-only: it deliberately skips the unfixed-root solve
    /// entirely and has no root fast path. The returned opaque carrier rebuilds
    /// the exact asymmetric comb and verifies the whole certificate in
    /// [`CertifiedAdaptiveFourLeafComb::into_farkas_against_row_upper`].
    #[must_use]
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        candidates: &[Col],
        root_candidate_index: usize,
        root_hard_value: bool,
        threshold: &BigRational,
        fsb_opts: &TargetFsbOpts,
    ) -> Option<(
        CertifiedAdaptiveFourLeafComb,
        AdaptiveFourLeafCombTargetFsbReport,
    )> {
        let candidate_count = candidates.len();
        let root_split = *candidates.get(root_candidate_index)?;
        if !float_lane_enabled()
            || !(3..=MAX_TARGET_FSB_CANDIDATES).contains(&candidate_count)
            || self.model.has_inexact_coeffs()
            || coeffs
                .iter()
                .any(|&(col, value)| col.index() >= self.model.num_cols() || !value.is_finite())
        {
            return None;
        }

        let mut seen_candidates = vec![false; self.model.num_cols()];
        for &candidate in candidates {
            if candidate.index() >= self.model.num_cols()
                || self.model.col_bounds(candidate) != (0.0, 1.0)
                || std::mem::replace(seen_candidates.get_mut(candidate.index())?, true)
            {
                return None;
            }
        }
        let mut seen_objective = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen_objective.get_mut(col.index())?, true) {
                return None;
            }
        }

        let second_stage_probe_calls = candidate_count.checked_sub(1)?.checked_mul(2)?;
        let third_stage_probe_calls = candidate_count.checked_sub(2)?.checked_mul(2)?;
        let required_calls = second_stage_probe_calls.checked_add(third_stage_probe_calls)?;
        if required_calls != candidate_count.checked_mul(4)?.checked_sub(6)?
            || fsb_opts.max_probe_pivots_per_call == 0
            || fsb_opts.probe_time_limit.is_zero()
            || fsb_opts.max_probe_calls < required_calls
        {
            return None;
        }

        // Selection workspace under the TargetFsbOpts contract. The first five
        // terms mirror complete/adaptive target-FSB (boxes, safe-bound
        // intervals, probe extraction/duals and score allowance). The final
        // terms conservatively account one retained optimal root-hard Candidate:
        // at+values as two full computational columns, and basis+duals+Farkas
        // as three row vectors. The pooled simplex remains solver state governed
        // by the LU fill guard, as in the existing selectors.
        let n = self.model.num_cols();
        let m = self.model.num_rows();
        let cols = n.checked_add(m)?;
        let scratch_slots = cols
            .checked_mul(2)?
            .checked_add(n.checked_mul(2)?)?
            .checked_add(cols)?
            .checked_add(m.checked_mul(2)?)?
            .checked_add(candidate_count.checked_mul(2)?)?
            .checked_add(cols.checked_mul(2)?)?
            .checked_add(m.checked_mul(3)?)?;
        let scratch_bytes = scratch_slots.checked_mul(size_of::<f64>())?;
        if scratch_bytes > fsb_opts.max_probe_scratch_bytes {
            return None;
        }
        // Prove the requested duration is representable before the cold
        // root-hard solve. This is only a static preflight: the actual probe
        // window starts after the cold anchor below.
        let _ = Instant::now().checked_add(fsb_opts.probe_time_limit)?;

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(col, a)| (col.0, a)).collect();
        let outer_deadline = self.opts.effective_deadline(Instant::now());
        let outer_expired = || outer_deadline.is_some_and(|limit| Instant::now() >= limit);
        if outer_expired() {
            return None;
        }

        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        let root_hard = f64::from(u8::from(root_hard_value));
        lower[root_split.index()] = root_hard;
        upper[root_split.index()] = root_hard;
        let hard_anchor = lp.solve_bounded(&lower, &upper, None, outer_deadline);
        if hard_anchor.status != SimplexStatus::Optimal || outer_expired() {
            return None;
        }
        let q = &lp.cost[..lp.n];

        let probe_start = Instant::now();
        let wall_deadline = probe_start.checked_add(fsb_opts.probe_time_limit)?;
        let probe_deadline = outer_deadline.map_or(wall_deadline, |outer| outer.min(wall_deadline));
        if Instant::now() >= probe_deadline {
            return None;
        }

        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        if trace {
            eprintln!(
                "AY_MILP_TRACE adaptive four-leaf anchor: root_col={} root_hard={} status=optimal",
                root_split.index(),
                u8::from(root_hard_value),
            );
        }
        let mut rc_scratch = vec![(0.0, 0.0); lp.n];
        let mut probe_calls = 0usize;

        let probe_reuse = lp.arm_probe_reuse();
        let mut second_candidate_index = None;
        let mut second_bounds = [f64::NEG_INFINITY; 2];
        let mut second_worst = f64::NEG_INFINITY;
        for (index, &candidate) in candidates.iter().enumerate() {
            if index == root_candidate_index {
                continue;
            }
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 0.0;
            let zero = adaptive_target_fsb_probe_box(
                &lp,
                &hard_anchor,
                &lower,
                &upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
            )?;
            lower[candidate.index()] = 1.0;
            upper[candidate.index()] = 1.0;
            let one = adaptive_target_fsb_probe_box(
                &lp,
                &hard_anchor,
                &lower,
                &upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
            )?;
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 1.0;
            let worst = zero.min(one);
            if trace {
                eprintln!(
                    "AY_MILP_TRACE adaptive four-leaf second candidate: root_col={} \
                     root_hard={} second_col={} zero={zero:.17e} one={one:.17e} \
                     worst={worst:.17e}",
                    root_split.index(),
                    u8::from(root_hard_value),
                    candidate.index(),
                );
            }
            if second_candidate_index.is_none() || worst > second_worst {
                second_candidate_index = Some(index);
                second_bounds = [zero, one];
                second_worst = worst;
            }
        }
        if probe_calls != second_stage_probe_calls || Instant::now() >= probe_deadline {
            return None;
        }

        let second_candidate_index = second_candidate_index?;
        let second_split = candidates[second_candidate_index];
        // The harder child is the STRICTLY lower score. Equal scores choose
        // false deterministically, independent of candidate ordering.
        let second_hard_value = second_bounds[1] < second_bounds[0];
        lower[second_split.index()] = f64::from(u8::from(second_hard_value));
        upper[second_split.index()] = f64::from(u8::from(second_hard_value));
        let stage_two_start = probe_calls;
        let mut third_candidate_index = None;
        let mut third_bounds = [f64::NEG_INFINITY; 2];
        let mut third_worst = f64::NEG_INFINITY;
        for (index, &candidate) in candidates.iter().enumerate() {
            if index == root_candidate_index || index == second_candidate_index {
                continue;
            }
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 0.0;
            let zero = adaptive_target_fsb_probe_box(
                &lp,
                &hard_anchor,
                &lower,
                &upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
            )?;
            lower[candidate.index()] = 1.0;
            upper[candidate.index()] = 1.0;
            let one = adaptive_target_fsb_probe_box(
                &lp,
                &hard_anchor,
                &lower,
                &upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
            )?;
            lower[candidate.index()] = 0.0;
            upper[candidate.index()] = 1.0;
            let worst = zero.min(one);
            if trace {
                eprintln!(
                    "AY_MILP_TRACE adaptive four-leaf third candidate: root_col={} \
                     root_hard={} second_col={} second_hard={} third_col={} \
                     zero={zero:.17e} one={one:.17e} worst={worst:.17e}",
                    root_split.index(),
                    u8::from(root_hard_value),
                    second_split.index(),
                    u8::from(second_hard_value),
                    candidate.index(),
                );
            }
            if third_candidate_index.is_none() || worst > third_worst {
                third_candidate_index = Some(index);
                third_bounds = [zero, one];
                third_worst = worst;
            }
        }
        if probe_calls.checked_sub(stage_two_start)? != third_stage_probe_calls
            || probe_calls != required_calls
            || Instant::now() >= probe_deadline
        {
            return None;
        }
        drop(probe_reuse);
        drop(lower);
        drop(upper);
        drop(rc_scratch);

        let third_candidate_index = third_candidate_index?;
        let third_split = candidates[third_candidate_index];
        if trace {
            eprintln!(
                "AY_MILP_TRACE adaptive four-leaf selected: root_col={} root_hard={} \
                 second_col={} second_hard={} second_zero={:.17e} second_one={:.17e} \
                 second_worst={second_worst:.17e} third_col={} third_zero={:.17e} \
                 third_one={:.17e} third_worst={third_worst:.17e} \
                 probes={probe_calls}/{required_calls}",
                root_split.index(),
                u8::from(root_hard_value),
                second_split.index(),
                u8::from(second_hard_value),
                second_bounds[0],
                second_bounds[1],
                third_split.index(),
                third_bounds[0],
                third_bounds[1],
            );
        }

        let (root_easy, root_easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[(root_split, !root_hard_value)],
            Some(&hard_anchor),
            threshold,
            outer_deadline,
            "adaptive four-leaf root-easy weak",
        )?;
        drop(root_easy_candidate);
        let (second_easy, second_easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[
                (root_split, root_hard_value),
                (second_split, !second_hard_value),
            ],
            Some(&hard_anchor),
            threshold,
            outer_deadline,
            "adaptive four-leaf second-easy weak",
        )?;
        drop(hard_anchor);
        let deep_prefix = [
            (root_split, root_hard_value),
            (second_split, second_hard_value),
        ];
        let (third_zero, third_zero_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[deep_prefix[0], deep_prefix[1], (third_split, false)],
            Some(&second_easy_candidate),
            threshold,
            outer_deadline,
            "adaptive four-leaf third-zero weak",
        )?;
        drop(second_easy_candidate);
        let (third_one, third_one_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[deep_prefix[0], deep_prefix[1], (third_split, true)],
            Some(&third_zero_candidate),
            threshold,
            outer_deadline,
            "adaptive four-leaf third-one weak",
        )?;
        drop(third_zero_candidate);
        drop(third_one_candidate);

        Some((
            CertifiedAdaptiveFourLeafComb {
                root_split,
                root_hard_value,
                second_split,
                second_hard_value,
                third_split,
                root_easy,
                second_easy,
                third_zero,
                third_one,
            },
            AdaptiveFourLeafCombTargetFsbReport {
                candidate_count,
                probe_calls,
                second_stage_probe_calls,
                third_stage_probe_calls,
                root_candidate_index,
                root_split,
                root_hard_value,
                second_candidate_index,
                second_split,
                second_hard_value,
                second_child_lower_bounds: second_bounds,
                third_candidate_index,
                third_split,
                third_child_lower_bounds: third_bounds,
            },
        ))
    }

    /// Harvest a tree-only adaptive five-leaf comb with three target-FSB stages.
    ///
    /// `candidates` is an ordered shortlist of four through eight distinct
    /// relaxed `[0, 1]` columns. `root_candidate_index` and
    /// `root_hard_value` fix the first comb edge. The hard root child is solved
    /// cold to optimality as the common advice anchor. Three contiguous
    /// complete scans then select the second, third, and terminal fourth split.
    /// At the first two selected splits, the strictly lower child bound
    /// continues the comb; `false` wins an exact tie.
    ///
    /// Every quick probe warm-starts from the saved root-hard anchor and is
    /// scored by [`crate::bab::safe_bound`] over its full computational box.
    /// Strict `>` comparisons preserve caller order on rank ties. Only after
    /// all three scans does the method exactify five leaves: root-easy,
    /// second-easy, third-easy, and fourth zero/one. Each leaf carries either a
    /// verified conditional row strictly above `threshold` or an exact Farkas
    /// witness.
    ///
    /// The scans cost exactly `2*(n-1)`, `2*(n-2)`, and `2*(n-3)` quick calls,
    /// totaling `6*n-12` probes, plus one cold optimal root-hard anchor solve.
    /// All quick-probe arithmetic and resource caps are preflighted before the
    /// anchor. The per-call pivot, call, and shared probe-wall caps do not
    /// govern that anchor; the session's outer deadline and simplex LU guard
    /// do. One probe deadline spans the three scans only. Selection buffers are
    /// dropped before exactification. Root-, second-, and third-easy start from
    /// the anchor; fourth zero starts from third-easy and fourth one from zero.
    ///
    /// This API never solves the unfixed root and has no root fast path. The
    /// opaque carrier reconstructs and verifies the exact arbitrary tree in
    /// [`CertifiedAdaptiveFiveLeafComb::into_farkas_against_row_upper`].
    #[must_use]
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
        &mut self,
        coeffs: &[(Col, f64)],
        sense: Sense,
        candidates: &[Col],
        root_candidate_index: usize,
        root_hard_value: bool,
        threshold: &BigRational,
        fsb_opts: &TargetFsbOpts,
    ) -> Option<(
        CertifiedAdaptiveFiveLeafComb,
        AdaptiveFiveLeafCombTargetFsbReport,
    )> {
        let candidate_count = candidates.len();
        let root_split = *candidates.get(root_candidate_index)?;
        if !float_lane_enabled()
            || !(4..=MAX_TARGET_FSB_CANDIDATES).contains(&candidate_count)
            || self.model.has_inexact_coeffs()
            || coeffs
                .iter()
                .any(|&(col, value)| col.index() >= self.model.num_cols() || !value.is_finite())
        {
            return None;
        }

        let mut seen_candidates = vec![false; self.model.num_cols()];
        for &candidate in candidates {
            if candidate.index() >= self.model.num_cols()
                || self.model.col_bounds(candidate) != (0.0, 1.0)
                || std::mem::replace(seen_candidates.get_mut(candidate.index())?, true)
            {
                return None;
            }
        }
        let mut seen_objective = vec![false; self.model.num_cols()];
        for &(col, _) in coeffs {
            if std::mem::replace(seen_objective.get_mut(col.index())?, true) {
                return None;
            }
        }

        let second_stage_probe_calls = candidate_count.checked_sub(1)?.checked_mul(2)?;
        let third_stage_probe_calls = candidate_count.checked_sub(2)?.checked_mul(2)?;
        let fourth_stage_probe_calls = candidate_count.checked_sub(3)?.checked_mul(2)?;
        let required_calls = second_stage_probe_calls
            .checked_add(third_stage_probe_calls)?
            .checked_add(fourth_stage_probe_calls)?;
        if required_calls != candidate_count.checked_mul(6)?.checked_sub(12)?
            || fsb_opts.max_probe_pivots_per_call == 0
            || fsb_opts.probe_time_limit.is_zero()
            || fsb_opts.max_probe_calls < required_calls
        {
            return None;
        }

        // Three scans reuse the same boxes, safe-bound scratch and score
        // storage. The final terms account one retained optimal root-hard
        // Candidate: at+values as two full computational columns and
        // basis+duals+Farkas as three row vectors. The pooled simplex remains
        // governed by its LU fill guard.
        let n = self.model.num_cols();
        let m = self.model.num_rows();
        let cols = n.checked_add(m)?;
        let scratch_slots = cols
            .checked_mul(2)?
            .checked_add(n.checked_mul(2)?)?
            .checked_add(cols)?
            .checked_add(m.checked_mul(2)?)?
            .checked_add(candidate_count.checked_mul(2)?)?
            .checked_add(cols.checked_mul(2)?)?
            .checked_add(m.checked_mul(3)?)?;
        let scratch_bytes = scratch_slots.checked_mul(size_of::<f64>())?;
        if scratch_bytes > fsb_opts.max_probe_scratch_bytes {
            return None;
        }
        // Static representability preflight only; the actual probe window
        // begins after the cold root-hard anchor.
        let _ = Instant::now().checked_add(fsb_opts.probe_time_limit)?;

        let objective: Vec<(u32, f64)> = coeffs.iter().map(|&(col, a)| (col.0, a)).collect();
        let outer_deadline = self.opts.effective_deadline(Instant::now());
        let outer_expired = || outer_deadline.is_some_and(|limit| Instant::now() >= limit);
        if outer_expired() {
            return None;
        }

        let mut lp = self.float_lp(&objective, sense)?;
        lp.plain_cold = true;
        lp.request_eager_affine_crash();
        let mut lower = lp.lower.clone();
        let mut upper = lp.upper.clone();
        let root_hard = f64::from(u8::from(root_hard_value));
        lower[root_split.index()] = root_hard;
        upper[root_split.index()] = root_hard;
        let hard_anchor = lp.solve_bounded(&lower, &upper, None, outer_deadline);
        if hard_anchor.status != SimplexStatus::Optimal || outer_expired() {
            return None;
        }
        let q = &lp.cost[..lp.n];

        let probe_start = Instant::now();
        let wall_deadline = probe_start.checked_add(fsb_opts.probe_time_limit)?;
        let probe_deadline = outer_deadline.map_or(wall_deadline, |outer| outer.min(wall_deadline));
        if Instant::now() >= probe_deadline {
            return None;
        }

        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        if trace {
            eprintln!(
                "AY_MILP_TRACE adaptive five-leaf anchor: root_col={} root_hard={} status=optimal",
                root_split.index(),
                u8::from(root_hard_value),
            );
        }
        let mut rc_scratch = vec![(0.0, 0.0); lp.n];
        let mut probe_calls = 0usize;
        let probe_reuse = lp.arm_probe_reuse();

        let stage_one_start = probe_calls;
        let (second_candidate_index, second_bounds, second_worst) =
            adaptive_target_fsb_select_stage(
                &lp,
                &hard_anchor,
                candidates,
                &[root_candidate_index],
                &mut lower,
                &mut upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
                "adaptive five-leaf second candidate",
            )?;
        if probe_calls.checked_sub(stage_one_start)? != second_stage_probe_calls
            || Instant::now() >= probe_deadline
        {
            return None;
        }
        let second_split = candidates[second_candidate_index];
        let second_hard_value = second_bounds[1] < second_bounds[0];
        let second_hard = f64::from(u8::from(second_hard_value));
        lower[second_split.index()] = second_hard;
        upper[second_split.index()] = second_hard;

        let stage_two_start = probe_calls;
        let (third_candidate_index, third_bounds, third_worst) = adaptive_target_fsb_select_stage(
            &lp,
            &hard_anchor,
            candidates,
            &[root_candidate_index, second_candidate_index],
            &mut lower,
            &mut upper,
            fsb_opts,
            probe_deadline,
            &mut rc_scratch,
            &mut probe_calls,
            "adaptive five-leaf third candidate",
        )?;
        if probe_calls.checked_sub(stage_two_start)? != third_stage_probe_calls
            || Instant::now() >= probe_deadline
        {
            return None;
        }
        let third_split = candidates[third_candidate_index];
        let third_hard_value = third_bounds[1] < third_bounds[0];
        let third_hard = f64::from(u8::from(third_hard_value));
        lower[third_split.index()] = third_hard;
        upper[third_split.index()] = third_hard;

        let stage_three_start = probe_calls;
        let (fourth_candidate_index, fourth_bounds, fourth_worst) =
            adaptive_target_fsb_select_stage(
                &lp,
                &hard_anchor,
                candidates,
                &[
                    root_candidate_index,
                    second_candidate_index,
                    third_candidate_index,
                ],
                &mut lower,
                &mut upper,
                fsb_opts,
                probe_deadline,
                &mut rc_scratch,
                &mut probe_calls,
                "adaptive five-leaf fourth candidate",
            )?;
        if probe_calls.checked_sub(stage_three_start)? != fourth_stage_probe_calls
            || probe_calls != required_calls
            || Instant::now() >= probe_deadline
        {
            return None;
        }
        drop(probe_reuse);
        drop(lower);
        drop(upper);
        drop(rc_scratch);

        let fourth_split = candidates[fourth_candidate_index];
        if trace {
            eprintln!(
                "AY_MILP_TRACE adaptive five-leaf selected: root_col={} root_hard={} \
                 second_col={} second_hard={} second_zero={:.17e} second_one={:.17e} \
                 second_worst={second_worst:.17e} third_col={} third_hard={} \
                 third_zero={:.17e} third_one={:.17e} third_worst={third_worst:.17e} \
                 fourth_col={} fourth_zero={:.17e} fourth_one={:.17e} \
                 fourth_worst={fourth_worst:.17e} probes={probe_calls}/{required_calls}",
                root_split.index(),
                u8::from(root_hard_value),
                second_split.index(),
                u8::from(second_hard_value),
                second_bounds[0],
                second_bounds[1],
                third_split.index(),
                u8::from(third_hard_value),
                third_bounds[0],
                third_bounds[1],
                fourth_split.index(),
                fourth_bounds[0],
                fourth_bounds[1],
            );
        }

        let (root_easy, root_easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[(root_split, !root_hard_value)],
            Some(&hard_anchor),
            threshold,
            outer_deadline,
            "adaptive five-leaf root-easy weak",
        )?;
        drop(root_easy_candidate);
        let (second_easy, second_easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[
                (root_split, root_hard_value),
                (second_split, !second_hard_value),
            ],
            Some(&hard_anchor),
            threshold,
            outer_deadline,
            "adaptive five-leaf second-easy weak",
        )?;
        drop(second_easy_candidate);
        let (third_easy, third_easy_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[
                (root_split, root_hard_value),
                (second_split, second_hard_value),
                (third_split, !third_hard_value),
            ],
            Some(&hard_anchor),
            threshold,
            outer_deadline,
            "adaptive five-leaf third-easy weak",
        )?;
        drop(hard_anchor);
        let deep_prefix = [
            (root_split, root_hard_value),
            (second_split, second_hard_value),
            (third_split, third_hard_value),
        ];
        let (fourth_zero, fourth_zero_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[
                deep_prefix[0],
                deep_prefix[1],
                deep_prefix[2],
                (fourth_split, false),
            ],
            Some(&third_easy_candidate),
            threshold,
            outer_deadline,
            "adaptive five-leaf fourth-zero weak",
        )?;
        drop(third_easy_candidate);
        let (fourth_one, fourth_one_candidate) = exactify_adaptive_tree_leaf(
            &self.model,
            &lp,
            q,
            &[
                deep_prefix[0],
                deep_prefix[1],
                deep_prefix[2],
                (fourth_split, true),
            ],
            Some(&fourth_zero_candidate),
            threshold,
            outer_deadline,
            "adaptive five-leaf fourth-one weak",
        )?;
        drop(fourth_zero_candidate);
        drop(fourth_one_candidate);

        Some((
            CertifiedAdaptiveFiveLeafComb {
                root_split,
                root_hard_value,
                second_split,
                second_hard_value,
                third_split,
                third_hard_value,
                fourth_split,
                root_easy,
                second_easy,
                third_easy,
                fourth_zero,
                fourth_one,
            },
            AdaptiveFiveLeafCombTargetFsbReport {
                candidate_count,
                probe_calls,
                second_stage_probe_calls,
                third_stage_probe_calls,
                fourth_stage_probe_calls,
                root_candidate_index,
                root_split,
                root_hard_value,
                second_candidate_index,
                second_split,
                second_hard_value,
                second_child_lower_bounds: second_bounds,
                third_candidate_index,
                third_split,
                third_hard_value,
                third_child_lower_bounds: third_bounds,
                fourth_candidate_index,
                fourth_split,
                fourth_child_lower_bounds: fourth_bounds,
            },
        ))
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
    /// Advice-only incumbent seeds and branching guidance for the native engine.
    incumbent_seed: Option<Vec<f64>>,
    branch_hints: Vec<Col>,
    root_strong_branch_shortlist: Vec<Col>,
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
            root_strong_branch_shortlist: Vec::new(),
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

    /// Supply an ordered shortlist of binary columns to measure with
    /// reliability/strong branching at the root node when that branching mode
    /// is active.
    ///
    /// Advice only: at the top-level root, the native engine restricts its
    /// bounded probe pool to the currently fractional members of this list, in
    /// caller order. In pseudocost/reliability selection, caller order breaks
    /// equal-score root ties, including the all-zero gains common in
    /// zero-objective feasibility models. The eventual branch is still chosen
    /// from every live fractional integer column, and a stronger measured
    /// score, another configured branching mode, or a later structural split
    /// may override the shortlist. Deeper nodes keep the historical pool. If
    /// no supplied column is live at the root, the historical pool is used
    /// there too. Stale, fixed, non-binary, and duplicate handles are ignored.
    pub fn shortlist_root_strong_branch_candidates(&mut self, cols: &[Col]) {
        self.root_strong_branch_shortlist = cols.to_vec();
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
                        &self.root_strong_branch_shortlist,
                    ),
                    None if self.branch_hints.is_empty()
                        && self.root_strong_branch_shortlist.is_empty() =>
                    {
                        crate::bab::solve_milp(&self.model, &self.opts)
                    }
                    None => crate::bab::solve_milp_advised(
                        &self.model,
                        &self.opts,
                        &self.branch_hints,
                        &self.root_strong_branch_shortlist,
                    ),
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
    pub fn harvest_cuts(&mut self) -> Vec<CertifiedRow> {
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

    /// The stored root strong-branch shortlist (advice; native engine).
    #[must_use]
    pub fn root_strong_branch_shortlist(&self) -> &[Col] {
        &self.root_strong_branch_shortlist
    }
}

#[cfg(test)]
mod target_fsb_score_tests {
    use super::*;

    #[test]
    fn probe_score_clamps_opposite_wrong_signs_on_one_sided_logicals() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0)]);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0)]);
        let objective = [(x.0, 1.0)];
        let lp =
            FloatLp::from_model(&model, &objective, Sense::Minimize).expect("finite lower form");

        // A limited probe may stop with either logical sign. Here the first
        // >= row has a wrong negative dual while the second has a positive
        // dual. The old target-FSB scorer tried raw y and -y: raw y fails on
        // row 0's missing upper bound, while -y fails on row 1's.
        let duals = [-0.5, 0.5];
        let structural_lower = &lp.lower[..lp.n];
        let structural_upper = &lp.upper[..lp.n];
        assert!(crate::ns::rigorous_lower_bound_with_box(
            &model,
            &lp.cost[..lp.n],
            &duals,
            structural_lower,
            structural_upper,
        )
        .is_none());
        let negated: Vec<f64> = duals.iter().map(|&y| -y).collect();
        assert!(crate::ns::rigorous_lower_bound_with_box(
            &model,
            &lp.cost[..lp.n],
            &negated,
            structural_lower,
            structural_upper,
        )
        .is_none());

        let mut rc_scratch = vec![(0.0, 0.0); lp.n];
        let score = target_fsb_probe_score(&lp, &duals, &lp.lower, &lp.upper, &mut rc_scratch)
            .expect("safe-bound clamping must retain a finite probe score");
        assert!(score.is_finite());
        assert!(
            (-1e-12..=0.0).contains(&score),
            "score {score} must rigorously bound the exact minimum 0"
        );
    }
}

#[cfg(test)]
mod lp_lazy_tests {
    use super::*;

    fn exact_only_model() -> (Model, Col) {
        let mut model = Model::new();
        let x = model.add_col(0.0, 2.0);
        let row = model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        // The rounded matrix says x >= 1, while the authoritative side-store
        // says 2x >= 1. Side-store models deliberately skip the float lane.
        model.record_inexact_row_coeff(row, x.0, BigRational::from_integer(2_i32.into()));
        (model, x)
    }

    #[test]
    fn construction_defers_the_exact_rim() {
        let (model, _) = exact_only_model();
        let session = LpSession::new(&model, &SolveOpts::new()).expect("valid continuous session");
        assert!(
            session.lp.is_none(),
            "session construction must not eagerly rationalize the matrix"
        );
    }

    #[test]
    fn certified_float_verdict_never_materializes_the_exact_rim() {
        if !float_lane_enabled() {
            return;
        }
        let mut model = Model::new();
        let x = model.add_col(0.0, 2.0);
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        let mut session =
            LpSession::new(&model, &SolveOpts::new()).expect("valid continuous session");

        match session
            .optimize(x, Sense::Minimize)
            .expect("valid objective")
        {
            Outcome::Optimal {
                value,
                cert: Some(cert),
                ..
            } => {
                assert_eq!(value, BigRational::from_integer(1_i32.into()));
                cert.verify(&model)
                    .expect("float-lane certificate verifies");
            }
            other => panic!("expected certified float optimum, got {other:?}"),
        }
        assert!(
            session.lp.is_none(),
            "a certified float verdict must not allocate the fallback rim"
        );
    }

    #[test]
    fn exact_fallback_materializes_warm_state_and_narrowing_discards_it() {
        let (model, x) = exact_only_model();
        let mut session =
            LpSession::new(&model, &SolveOpts::new()).expect("valid continuous session");

        match session
            .optimize(x, Sense::Minimize)
            .expect("valid objective")
        {
            Outcome::Optimal { value, .. } => {
                assert_eq!(value, BigRational::new(1_i32.into(), 2_i32.into()));
            }
            other => panic!("expected exact optimum, got {other:?}"),
        }
        assert!(
            session.lp.is_some(),
            "an exact fallback remains materialized for warm re-solves"
        );

        assert!(session.narrow_col_bounds(x, 0.75, 2.0));
        assert!(
            session.lp.is_none(),
            "a narrowed model must discard stale exact bounds immediately"
        );
        match session
            .optimize(x, Sense::Minimize)
            .expect("valid objective")
        {
            Outcome::Optimal {
                value,
                cert: Some(cert),
                ..
            } => {
                assert_eq!(value, BigRational::new(3_i32.into(), 4_i32.into()));
                cert.verify(&session.model)
                    .expect("rebuilt rim certifies the narrowed model");
            }
            other => panic!("expected certified narrowed optimum, got {other:?}"),
        }
        assert!(session.lp.is_some(), "fallback is materialized again");
    }

    #[test]
    fn expired_deadline_during_lazy_build_fails_closed_without_partial_state() {
        let (model, x) = exact_only_model();
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("test clock supports a one-second lookback");
        let opts = SolveOpts::new().with_deadline(expired);
        let mut session = LpSession::new(&model, &opts).expect("valid continuous session");

        assert!(matches!(
            session
                .optimize(x, Sense::Minimize)
                .expect("valid objective"),
            Outcome::Unknown {
                reason: UnknownReason::Timeout
            }
        ));
        assert!(
            session.lp.is_none(),
            "a timed-out build must publish no partial exact state"
        );
    }
}

#[cfg(test)]
mod range_logical_opts_tests {
    use super::*;

    #[test]
    fn lp_session_threads_typed_range_logical_request_without_policy_bleed() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let default = LpSession::new(&model, &SolveOpts::new()).expect("default session");
        let explicit = LpSession::new(
            &model,
            &SolveOpts::new().with_range_logical_triangular_crash(),
        )
        .expect("explicit session");

        let default_lp = default
            .float_lp(&[(x.0, 1.0)], Sense::Minimize)
            .expect("default float LP");
        let explicit_lp = explicit
            .float_lp(&[(x.0, 1.0)], Sense::Minimize)
            .expect("explicit float LP");

        assert!(!default_lp.range_logical_triangular_crash_requested());
        assert!(explicit_lp.range_logical_triangular_crash_requested());
    }
}

#[cfg(test)]
mod chain_distress_probe_opts_tests {
    use super::*;

    #[test]
    fn lp_session_threads_chain_probe_override_into_every_lowered_lp() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let default = LpSession::new(&model, &SolveOpts::new()).expect("default session");
        let explicit = LpSession::new(
            &model,
            &SolveOpts::new().with_chain_distress_probe_iters(Some(7_777)),
        )
        .expect("configured session");

        let default_lp = default
            .float_lp(&[(x.0, 1.0)], Sense::Minimize)
            .expect("default float LP");
        let first = explicit
            .float_lp(&[(x.0, 1.0)], Sense::Minimize)
            .expect("first configured float LP");
        let rebuilt = explicit
            .float_lp(&[(x.0, 1.0)], Sense::Maximize)
            .expect("rebuilt configured float LP");

        assert_eq!(default_lp.chain_distress_probe_iters_override(), None);
        assert_eq!(first.chain_distress_probe_iters_override(), Some(7_777));
        assert_eq!(
            rebuilt.chain_distress_probe_iters_override(),
            Some(7_777),
            "re-lowering another objective must retain the session override"
        );
    }

    #[test]
    fn chain_probe_override_survives_clone_and_row_reload() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let row = model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        let session = LpSession::new(
            &model,
            &SolveOpts::new().with_chain_distress_probe_iters(Some(456)),
        )
        .expect("configured session");
        let objective = [(x.0, 1.0)];
        let mut lp = session
            .float_lp(&objective, Sense::Minimize)
            .expect("configured float LP");

        assert_eq!(
            lp.clone().chain_distress_probe_iters_override(),
            Some(456),
            "ordinary LP clones must retain the typed override"
        );

        model.set_row(row, f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
        assert!(lp.reload_rows(&model, &objective, Sense::Minimize));
        assert_eq!(
            lp.chain_distress_probe_iters_override(),
            Some(456),
            "same-shape row reconstruction must retain the typed override"
        );
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
