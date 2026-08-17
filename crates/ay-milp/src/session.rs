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
use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::{BoundSide, CertifiedRow, FarkasCertificate, OptimalityCertificate};
use crate::certify::{
    certified_weak_dual_row, certify, certify_model_basis_with_deadline, certify_with_deadline,
    MAX_EXACT_BASIS_ROWS,
};
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

/// Budget for the experimental binary-master/continuous-LP route.
///
/// The route has not yet earned default ownership of a production solve.  When
/// explicitly enabled for an A/B, it receives at most one fifth of the caller's
/// remaining time and never more than two seconds.  A structural or resource
/// decline therefore leaves a deterministic native-MILP reserve instead of
/// consuming the whole outer deadline.
fn hybrid_pb_lp_trial_deadline(
    enabled: bool,
    outer_deadline: Option<Instant>,
    now: Instant,
) -> Option<Instant> {
    if !enabled {
        return None;
    }
    const CAP: Duration = Duration::from_secs(2);
    match outer_deadline {
        Some(outer) => {
            let slice = outer.saturating_duration_since(now) / 5;
            Some(now.checked_add(slice.min(CAP)).unwrap_or(outer).min(outer))
        }
        None => now.checked_add(CAP),
    }
}

/// Budget for the compact exact bounded-PB portfolio trial.
///
/// Translation and every adopted result are exact, but the general portfolio
/// is still search.  It receives at most one tenth of the remaining caller
/// budget and never more than 500 ms; a decline therefore cannot consume the
/// native solver's solve.  The adapter has independent variable/row/term caps.
fn pb_portfolio_trial_deadline(outer_deadline: Option<Instant>, now: Instant) -> Option<Instant> {
    const CAP: Duration = Duration::from_millis(500);
    match outer_deadline {
        Some(outer) => {
            let slice = outer.saturating_duration_since(now) / 10;
            let deadline = now.checked_add(slice.min(CAP)).unwrap_or(outer).min(outer);
            (deadline > now).then_some(deadline)
        }
        None => now.checked_add(CAP),
    }
}

/// Bound a speculative prelude arm by the cost of a cheaper arm already run on
/// the SAME model, rather than by a slice of the caller's patience.
///
/// THE UNIT PROBLEM. `pb_portfolio_trial_deadline` returns `min(500ms,
/// deadline/10)`: it mentions how long the user is willing to wait and never
/// mentions the model. Three infeasibility probes then share that one absolute
/// deadline, so on a FEASIBLE model — where by construction none of them can
/// succeed — the trio may burn the whole slice before native search starts.
/// Measured on the general MIPLIB corpus, `try_prove_multi_row_infeasibility`
/// did exactly that, to the millisecond, and hit ZERO times:
///
/// ```text
///   p0201  0.502s   gt2    0.502s   mod010 0.500s
///   misc07 0.499s   qnet1  0.410s   ...      0 hits, 12 of 12 instances
/// ```
///
/// while the single-row probe ahead of it declined the same models in
/// 0.07–17 ms. That ratio is the fix: the cheap probe is a structural pass over
/// the same rows, so its cost is a free, exact, model-derived estimate of what
/// this model costs to look at. An arm that needs two dozen times that and
/// still has nothing is not about to produce a proof.
///
/// The caller's cap and deadline still bound the result from above, and a model
/// whose cheap probe was too fast to time keeps a real floor. This cannot
/// refuse a lane — it only declines to spend the user's wall on a shape the
/// cheap pass already failed to recognise.
fn probe_scaled_deadline(
    reference: Duration,
    outer_trial_deadline: Option<Instant>,
    now: Instant,
) -> Option<Instant> {
    const MULTIPLE: u32 = 24;
    // The floor must clear the arm's own START-UP cost, or the slice buys
    // nothing: the lane is entered, sets up, and is cut off before it can
    // conclude — strictly worse than declining, since the wall is spent either
    // way.
    //
    // THIS NUMBER IS NOW MEASURED FOR THESE LANES; THE PREVIOUS ONE WAS NOT.
    // It was first set to 48 ms by INHERITING the exact-PB portfolio's measured
    // 32.3 ms set-up (`GENERIC_PORTFOLIO_TRIAL_FLOOR`), reasoning that these are
    // the same family of exact PB/BDD engines and that no test covered them
    // through the session budget. The inheritance was wrong, and it was
    // expensive. On a genuine two-row weighted-binary contradiction the
    // multi-row lane reaches `hit=true` in 0.000060 s — sixty MICROseconds,
    // eight hundred times under the inherited floor. Meanwhile that floor was
    // being consumed IN FULL, to the millisecond, by lanes that never succeed:
    //
    //   khb05250   hybrid_pb_lp  0.048288s  hit=false
    //   p0201      multi_row     0.048203s  hit=false
    //   dcmulti    hybrid_pb_lp  0.056337s  hit=false
    //
    // — 7-13% of those solves spent on arms that cannot conclude. 2 ms still
    // leaves 33x headroom over the measured set-up.
    //
    // The 60 us figure is from instrumenting THIS call site, not a sibling. And
    // the capability does not rest on this budget alone: mutation-testing the
    // new session-level routing test (starving MULTIPLE and FLOOR to zero) does
    // NOT break it, because `multi_row_bdd_infeasibility_certificate` has two
    // further assignment sites inside the specialized/portfolio route handling,
    // each with its own budget. A starved probe loses time, not the verdict.
    const FLOOR: Duration = Duration::from_millis(2);
    let outer = outer_trial_deadline?;
    let slice = reference
        .checked_mul(MULTIPLE)
        .unwrap_or(FLOOR)
        .max(FLOOR)
        .min(outer.saturating_duration_since(now));
    let deadline = now.checked_add(slice)?.min(outer);
    (deadline > now).then_some(deadline)
}

/// Budget for an exactly recognized SAT/ReLU model's proof-producing CDCL run.
///
/// Recognition has already rebuilt the complete CNF, so this is not a blind
/// portfolio arm: this is the production engine for the recognized family.
/// Give it the caller's complete remaining budget so a slower conclusive CDCL
/// run is never discarded and restarted in a generic lane. The bounded ay-sat
/// API requires an absolute deadline, so an otherwise-unlimited solve receives
/// a documented 60-second route deadline; this is above the known production
/// corpus maximum while retaining a finite control-loop bound.
fn sat_relu_proof_trial_deadline(outer_deadline: Option<Instant>, now: Instant) -> Option<Instant> {
    const DEFAULT_ROUTE_LIMIT: Duration = Duration::from_mins(1);
    match outer_deadline {
        Some(outer) => (outer > now).then_some(outer),
        None => now.checked_add(DEFAULT_ROUTE_LIMIT),
    }
}

#[cfg(test)]
mod hybrid_pb_lp_trial_deadline_tests {
    use super::*;

    #[test]
    fn disabled_route_gets_no_deadline_or_work() {
        assert_eq!(
            hybrid_pb_lp_trial_deadline(false, None, Instant::now()),
            None
        );
    }

    #[test]
    fn finite_trial_preserves_native_time_and_honours_outer_deadline() {
        let now = Instant::now();
        let outer = now + Duration::from_secs(5);
        assert_eq!(
            hybrid_pb_lp_trial_deadline(true, Some(outer), now),
            Some(now + Duration::from_secs(1))
        );

        let short_outer = now + Duration::from_millis(10);
        assert_eq!(
            hybrid_pb_lp_trial_deadline(true, Some(short_outer), now),
            Some(now + Duration::from_millis(2))
        );
    }

    #[test]
    fn unlimited_outer_still_gets_a_bounded_trial() {
        let now = Instant::now();
        assert_eq!(
            hybrid_pb_lp_trial_deadline(true, None, now),
            Some(now + Duration::from_secs(2))
        );
    }
}

#[cfg(test)]
mod pb_portfolio_trial_deadline_tests {
    use super::*;

    #[test]
    fn finite_trial_is_capped_and_preserves_native_time() {
        let now = Instant::now();
        let long = now + Duration::from_secs(60);
        assert_eq!(
            pb_portfolio_trial_deadline(Some(long), now),
            Some(now + Duration::from_millis(500))
        );

        let short = now + Duration::from_millis(100);
        assert_eq!(
            pb_portfolio_trial_deadline(Some(short), now),
            Some(now + Duration::from_millis(10))
        );
    }

    #[test]
    fn unlimited_and_expired_trials_are_bounded_or_declined() {
        let now = Instant::now();
        assert_eq!(
            pb_portfolio_trial_deadline(None, now),
            Some(now + Duration::from_millis(500))
        );
        assert_eq!(pb_portfolio_trial_deadline(Some(now), now), None);
    }
}

#[cfg(test)]
mod sat_relu_proof_trial_deadline_tests {
    use super::*;

    #[test]
    fn production_route_receives_the_full_caller_deadline() {
        let now = Instant::now();
        assert_eq!(
            sat_relu_proof_trial_deadline(Some(now + Duration::from_secs(10)), now),
            Some(now + Duration::from_secs(10))
        );
        assert_eq!(
            sat_relu_proof_trial_deadline(Some(now + Duration::from_millis(80)), now),
            Some(now + Duration::from_millis(80))
        );
        assert_eq!(
            sat_relu_proof_trial_deadline(None, now),
            Some(now + Duration::from_secs(60))
        );
        assert_eq!(sat_relu_proof_trial_deadline(Some(now), now), None);
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

/// Whether the float lane runs. Off via `the no-float knob`, which forces every
/// solve down the exact rim — the A/B switch the float lane's speedup is
/// measured with, and the escape hatch if it ever misbehaves. Read once: this
/// sits on the per-solve path.
fn float_lane_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::NoFloat) != Some(true))
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
/// `--cert-grace-secs` (`0` selects the uncapped behavior). The verdict
/// is never at stake: a budget miss only leaves `cert` as `None`.
fn cert_budget_native(model: &Model, opts: &SolveOpts) -> Budget {
    let uncapped = cert_budget_for(model, opts);
    let cap = match crate::tune::real_opt(crate::tune::Knob::CertGraceSecs) {
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
    let mut unlimited = |_| true;
    exact_obj_with_work(coeffs, &mut unlimited).expect("unbounded objective conversion")
}

fn exact_obj_with_work<F>(coeffs: &[(u32, f64)], work: &mut F) -> Option<Vec<(u32, Rational)>>
where
    F: FnMut(usize) -> bool + ?Sized,
{
    let mut out = Vec::with_capacity(coeffs.len());
    for (index, &(c, a)) in coeffs.iter().enumerate() {
        if index & 0xff == 0 && !work(0x100.min(coeffs.len().saturating_sub(index))) {
            return None;
        }
        if a != 0.0 {
            out.push((
                c,
                Rational::from_big(exact(a).expect("validated objective coefficient")),
            ));
        }
    }
    out.sort_unstable_by_key(|&(c, _)| c);
    Some(out)
}

/// Independently checked evidence carried beside [`Outcome`].  Most proof
/// objects live directly in the outcome; exact reduction artifacts have their
/// own typed export channel and must be named explicitly at this policy gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SupplementalProof {
    None,
    VerifiedSatReluInfeasibility,
    VerifiedBlockAngularOptimality,
    VerifiedParityInfeasibility,
    VerifiedNetworkDesignInfeasibility,
    VerifiedNetworkDesignOptimality,
    VerifiedSingleMachineSchedulingOptimality,
    VerifiedSingleRowDpInfeasibility,
    VerifiedMultiRowBddInfeasibility,
    VerifiedOpenDomainSingleRowDpInfeasibility,
    VerifiedOpenDomainMultiRowBddInfeasibility,
    VerifiedOpenDomainHybridPbLpInfeasibility,
    VerifiedOpenDomainHybridIntegerLiftInfeasibility,
    VerifiedHybridPbLpInfeasibility,
    VerifiedHybridIntegerLiftInfeasibility,
}

impl SupplementalProof {
    fn certifies_infeasibility(self) -> bool {
        matches!(
            self,
            Self::VerifiedSatReluInfeasibility
                | Self::VerifiedParityInfeasibility
                | Self::VerifiedNetworkDesignInfeasibility
                | Self::VerifiedSingleRowDpInfeasibility
                | Self::VerifiedMultiRowBddInfeasibility
                | Self::VerifiedOpenDomainSingleRowDpInfeasibility
                | Self::VerifiedOpenDomainMultiRowBddInfeasibility
                | Self::VerifiedOpenDomainHybridPbLpInfeasibility
                | Self::VerifiedOpenDomainHybridIntegerLiftInfeasibility
                | Self::VerifiedHybridPbLpInfeasibility
                | Self::VerifiedHybridIntegerLiftInfeasibility
        )
    }

    fn certifies_optimality(self) -> bool {
        matches!(
            self,
            Self::VerifiedBlockAngularOptimality
                | Self::VerifiedNetworkDesignOptimality
                | Self::VerifiedSingleMachineSchedulingOptimality
        )
    }
}

/// Apply `require_certificates` policy: strip-or-degrade uncertified
/// verdicts.
fn apply_cert_policy(
    outcome: Outcome,
    model: &Model,
    opts: &SolveOpts,
    supplemental_proof: SupplementalProof,
) -> Outcome {
    if !opts.require_certificates {
        return outcome;
    }
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            cert: Some(cert),
        } if cert.bound.clone() + model.obj_offset_exact() == value => Outcome::Optimal {
            value,
            model_values,
            cert: Some(cert),
        },
        Outcome::Optimal {
            value,
            model_values,
            cert: None,
        } if supplemental_proof.certifies_optimality() => Outcome::Optimal {
            value,
            model_values,
            cert: None,
        },
        Outcome::Optimal { .. } => Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
        },
        // A feasible point is independently checked against the exact model,
        // but its interrupted-tree dual bound has no exported proof object.
        Outcome::Feasible {
            model_values,
            incumbent_only,
            ..
        } => Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: None,
        },
        // Root Farkas, whole-tree, and typed exact-reduction artifacts are all
        // independently replayable infeasibility evidence.
        Outcome::Infeasible { cert, tree_cert }
            if cert.is_some()
                || tree_cert.is_some()
                || supplemental_proof.certifies_infeasibility() =>
        {
            Outcome::Infeasible { cert, tree_cert }
        }
        Outcome::Infeasible { .. } | Outcome::Unbounded | Outcome::Bound { .. } => {
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable,
            }
        }
        Outcome::Unknown { reason } => Outcome::Unknown { reason },
    }
}

/// A model objective in exact rationals: `(coeffs, offset)`. Materialized when
/// the model carries any authoritative exact side store; then the re-derivation
/// gate must read the TRUE objective, not assume every `f64` proxy is complete.
type ExactObjective = (Vec<(u32, BigRational)>, BigRational);

fn authoritative_exact_objective(model: &Model) -> Option<ExactObjective> {
    if !model.has_inexact_coeffs() {
        return None;
    }
    Some((
        (0..model.num_cols())
            .filter_map(|column| {
                let column = column as u32;
                let proxy = model.obj_coeff(Col(column));
                let exact = model.obj_coeff_exact_at(column, proxy);
                (!exact.is_zero()).then_some((column, exact))
            })
            .collect(),
        model.obj_offset_exact(),
    ))
}

/// The objective a solve actually ran against. Not always the model's own:
/// `LpSession::optimize` bounds a single column, and `tighten_col_bounds`
/// leans on that.
struct SolvedObjective<'a> {
    coeffs: &'a [(u32, f64)],
    sense: Sense,
    offset: f64,
    /// The TRUE rational objective, set ONLY when `coeffs` IS the model's own
    /// objective AND the model carries an exact side store. When present
    /// `value_at` and `value_at_with_work` re-derive the reported value from
    /// it, closing the
    /// rounded-objective wrong-value hole (a rounded reported value and the
    /// rounded re-derivation would otherwise agree with each other).
    exact: Option<ExactObjective>,
}

impl SolvedObjective<'_> {
    /// Whether every variable coefficient is exactly zero. The constant offset
    /// is intentionally irrelevant: an empty multiplier certificate bounds the
    /// variable part by zero, and the session adds the caller's exact offset.
    fn coefficients_are_zero(&self) -> bool {
        self.exact.as_ref().map_or_else(
            || self.coeffs.is_empty(),
            |(coeffs, _)| coeffs.iter().all(|(_, coefficient)| coefficient.is_zero()),
        )
    }

    /// The exact objective value at an exact point.
    fn value_at(&self, values: &[BigRational]) -> BigRational {
        let mut unlimited = |_| true;
        self.value_at_with_work(values, &mut unlimited)
            .expect("unbounded objective replay cannot decline")
    }

    fn value_at_with_work<F>(&self, values: &[BigRational], work: &mut F) -> Option<BigRational>
    where
        F: FnMut(usize) -> bool + ?Sized,
    {
        if let Some((coeffs, offset)) = &self.exact {
            let mut acc = offset.clone();
            for (index, (c, a)) in coeffs.iter().enumerate() {
                if index & 0xff == 0 && !work(0x100.min(coeffs.len().saturating_sub(index))) {
                    return None;
                }
                acc += a * &values[*c as usize];
            }
            return Some(acc);
        }
        let mut acc = exact(self.offset).unwrap_or_else(BigRational::zero);
        for (index, &(c, a)) in self.coeffs.iter().enumerate() {
            if index & 0xff == 0 && !work(0x100.min(self.coeffs.len().saturating_sub(index))) {
                return None;
            }
            if let Some(a) = exact(a) {
                acc += a * &values[c as usize];
            }
        }
        Some(acc)
    }
}

fn zero_cost_optimality_certificate(
    objective: &SolvedObjective<'_>,
) -> Option<OptimalityCertificate> {
    objective
        .coefficients_are_zero()
        .then(|| OptimalityCertificate {
            sense: objective.sense,
            objective: Vec::new(),
            bound: BigRational::zero(),
            multipliers: Vec::new(),
        })
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
    let mut unlimited = |_| true;
    validate_witnesses_with_work_inner(outcome, model, obj, &mut unlimited)
}

fn validate_witnesses_with_work<F>(
    outcome: &Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
    work: &mut F,
) -> Result<(), String>
where
    F: FnMut(usize) -> bool + ?Sized,
{
    validate_witnesses_with_work_inner(outcome, model, obj, work)
}

fn validate_witnesses_with_work_inner<F>(
    outcome: &Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
    work: &mut F,
) -> Result<(), String>
where
    F: FnMut(usize) -> bool + ?Sized,
{
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
            if let Err(v) = model.check_point_with_work(model_values, work) {
                return Err(format!("the point claimed optimal is infeasible: {v:?}"));
            }
            let attained = obj
                .value_at_with_work(model_values, work)
                .ok_or_else(|| "objective replay exceeded its resource envelope".to_owned())?;
            if attained != *value {
                return Err(format!(
                    "the point attains {attained}, not the reported optimum {value}"
                ));
            }
            if let Some(cert) = cert {
                let mut cert_work = |units| {
                    if work(units) {
                        Ok(())
                    } else {
                        Err(crate::CertificateError::DeadlineExceeded)
                    }
                };
                cert.verify_with_work(model, &mut cert_work)
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
                .check_point_with_work(model_values, work)
                .map_err(|v| format!("the point claimed feasible is infeasible: {v:?}"))?;
            if let Some(bound) = dual_bound {
                // The tree's bound may trail the incumbent across the remaining
                // gap, but it may never cross it — a "bound" beyond the point in
                // hand is a contradiction, not a gap.
                let attained = obj
                    .value_at_with_work(model_values, work)
                    .ok_or_else(|| "objective replay exceeded its resource envelope".to_owned())?;
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
                let mut cert_work = |units| {
                    if work(units) {
                        Ok(())
                    } else {
                        Err(crate::CertificateError::DeadlineExceeded)
                    }
                };
                cert.verify_with_work(model, &mut cert_work)
                    .map_err(|e| format!("Farkas certificate does not verify: {e}"))?;
            }
            if let Some(tree_cert) = tree_cert {
                if !work(1) {
                    return Err("tree certificate replay exceeded its resource envelope".into());
                }
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
        Ok(()) => apply_cert_policy(outcome, model, opts, SupplementalProof::None),
        Err(detail) => Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { detail },
        },
    }
}

/// Finalize a SAT point already checked against the complete source model by
/// [`crate::sat_route::lift_and_check_assignment`].
///
/// The [`crate::sat_route::CheckedSatPoint`] token cannot be constructed by a
/// reduction, so consuming it here skips exactly one duplicate full-model
/// primal scan without weakening the boundary. Objective semantics are still
/// re-derived from the session's exact objective, and the pinned deadline is
/// polled both before and after that derivation.
fn finish_checked_sat_point(
    checked: crate::sat_route::CheckedSatPoint,
    has_objective: bool,
    model: &Model,
    obj: &SolvedObjective<'_>,
    opts: &SolveOpts,
) -> Outcome {
    let expired = || opts.deadline.is_some_and(|limit| Instant::now() >= limit);
    if expired() {
        return Outcome::Unknown {
            reason: UnknownReason::Timeout,
        };
    }
    let model_values = checked.into_values();
    if model_values.len() != model.num_cols() {
        return Outcome::Unknown {
            reason: UnknownReason::WitnessRejected {
                detail: format!(
                    "checked SAT point has {} values for a {}-column model",
                    model_values.len(),
                    model.num_cols()
                ),
            },
        };
    }
    let outcome = if has_objective {
        // All exact SAT routes currently admit only zero variable costs. Keep
        // the explicit-objective semantics (`Optimal`, not `Feasible`) and
        // carry the same exact empty-multiplier bound as native B&B. This is
        // essential in full posture: returning an uncertified optimum here
        // would degrade a conclusive checked SAT result to
        // `CertificateUnavailable`.
        let cert = zero_cost_optimality_certificate(obj);
        Outcome::Optimal {
            value: obj.value_at(&model_values),
            model_values,
            cert,
        }
    } else {
        Outcome::Feasible {
            model_values,
            incumbent_only: false,
            dual_bound: None,
        }
    };
    if expired() {
        return Outcome::Unknown {
            reason: UnknownReason::Timeout,
        };
    }
    apply_cert_policy(outcome, model, opts, SupplementalProof::None)
}

/// Resource-bounded twin of [`finish`] for a speculative route that owns one
/// cumulative work/deadline meter.  It preserves the exact same witness and
/// policy boundary; only the loop checkpoints differ.
fn finish_with_work<F>(
    outcome: Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
    opts: &SolveOpts,
    work: &mut F,
) -> Outcome
where
    F: FnMut(usize) -> bool + ?Sized,
{
    let outcome = fail_closed_for_inexact(outcome, model);
    match validate_witnesses_with_work(&outcome, model, obj, work) {
        Ok(()) => apply_cert_policy(outcome, model, opts, SupplementalProof::None),
        Err(detail) => Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { detail },
        },
    }
}

/// Exit for a reduction that read the authoritative exact model throughout.
///
/// [`fail_closed_for_inexact`] protects verdicts produced by float search over
/// rounded proxy coefficients. An exact structural reduction has no such proxy
/// dependency: its admission read every objective/row fact through `Model`'s
/// rational side store. SAT lifts now leave through the private checked-point
/// finalizer above; this function retains the independent witness gate for the
/// other exact reductions. Applying the float-search backstop here would turn
/// a sound Direct-CNF UNSAT into `CertificateUnavailable` merely because its
/// exact coefficient needed a side-store entry.
fn finish_exact_reduction(
    outcome: Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
    opts: &SolveOpts,
) -> Outcome {
    match validate_witnesses(&outcome, model, obj) {
        Ok(()) => apply_cert_policy(outcome, model, opts, SupplementalProof::None),
        Err(detail) => Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { detail },
        },
    }
}

/// Exit for an exact reduction whose typed side-channel artifact has already
/// been independently rebuilt and replayed against `model`.
fn finish_exact_reduction_with_supplemental_proof(
    outcome: Outcome,
    model: &Model,
    obj: &SolvedObjective<'_>,
    opts: &SolveOpts,
    supplemental_proof: SupplementalProof,
) -> Outcome {
    match validate_witnesses(&outcome, model, obj) {
        Ok(()) => apply_cert_policy(outcome, model, opts, supplemental_proof),
        Err(detail) => Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { detail },
        },
    }
}

#[cfg(test)]
mod certificate_policy_tests {
    use super::*;
    use crate::cert::OptimalityCertificate;
    use num_traits::One as _;

    fn full_opts() -> SolveOpts {
        SolveOpts::new().with_require_certificates(true)
    }

    #[test]
    fn zero_proxy_nonzero_exact_objective_refuses_the_empty_bound() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.set_objective(&[], Sense::Minimize);
        let tiny = BigRational::new(1.into(), num_bigint::BigInt::from(10u8).pow(400));
        model.record_inexact_obj_coeff(x.0, tiny.clone());
        assert_eq!(model.obj_coeff(x), 0.0, "the search proxy underflowed");

        let proxy_coeffs: Vec<(u32, f64)> = Vec::new();
        let objective = SolvedObjective {
            coeffs: &proxy_coeffs,
            sense: model.sense(),
            offset: model.objective_offset(),
            exact: authoritative_exact_objective(&model),
        };
        assert_eq!(
            objective.value_at(&[BigRational::one()]),
            tiny,
            "reported values retain the authoritative side-store coefficient"
        );
        assert!(
            zero_cost_optimality_certificate(&objective).is_none(),
            "a nonzero exact objective must never receive the empty zero-cost bound"
        );
    }

    #[test]
    fn full_policy_requires_an_optcert_that_meets_the_offset_value() {
        let mut model = Model::new();
        model.set_objective_offset(2.0);
        let cert = OptimalityCertificate {
            sense: Sense::Minimize,
            objective: Vec::new(),
            bound: BigRational::zero(),
            multipliers: Vec::new(),
        };
        let value = BigRational::from_integer(2.into());
        let accepted = apply_cert_policy(
            Outcome::Optimal {
                value: value.clone(),
                model_values: Vec::new(),
                cert: Some(cert.clone()),
            },
            &model,
            &full_opts(),
            SupplementalProof::None,
        );
        assert!(matches!(accepted, Outcome::Optimal { .. }));

        let rejected = apply_cert_policy(
            Outcome::Optimal {
                value: value + BigRational::one(),
                model_values: Vec::new(),
                cert: Some(cert),
            },
            &model,
            &full_opts(),
            SupplementalProof::None,
        );
        assert!(matches!(
            rejected,
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        ));
    }

    #[test]
    fn full_policy_keeps_only_the_verified_primal_part_of_feasible() {
        let model = Model::new();
        let kept = apply_cert_policy(
            Outcome::Feasible {
                model_values: Vec::new(),
                incumbent_only: true,
                dual_bound: Some(BigRational::zero()),
            },
            &model,
            &full_opts(),
            SupplementalProof::None,
        );
        assert!(matches!(
            kept,
            Outcome::Feasible {
                dual_bound: None,
                ..
            }
        ));
    }

    #[test]
    fn full_policy_accepts_typed_side_refutations_only_when_named() {
        let model = Model::new();
        let bare = || Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        };
        assert!(matches!(
            apply_cert_policy(bare(), &model, &full_opts(), SupplementalProof::None),
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedParityInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedNetworkDesignInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedSingleRowDpInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedOpenDomainHybridPbLpInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedOpenDomainHybridIntegerLiftInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedHybridPbLpInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedHybridIntegerLiftInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedMultiRowBddInfeasibility
            ),
            Outcome::Infeasible { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedNetworkDesignOptimality
            ),
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        ));
    }

    #[test]
    fn full_policy_accepts_only_the_named_network_optimality_artifact() {
        let model = Model::new();
        let bare = || Outcome::Optimal {
            value: BigRational::zero(),
            model_values: Vec::new(),
            cert: None,
        };
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedNetworkDesignOptimality
            ),
            Outcome::Optimal { .. }
        ));
        assert!(matches!(
            apply_cert_policy(
                bare(),
                &model,
                &full_opts(),
                SupplementalProof::VerifiedNetworkDesignInfeasibility
            ),
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        ));
    }

    #[test]
    fn full_policy_withholds_unexported_bound_and_unbounded_claims() {
        let model = Model::new();
        for outcome in [
            Outcome::Unbounded,
            Outcome::Bound {
                dual_bound: BigRational::zero(),
                rigorous: true,
            },
        ] {
            assert!(matches!(
                apply_cert_policy(outcome, &model, &full_opts(), SupplementalProof::None),
                Outcome::Unknown {
                    reason: UnknownReason::CertificateUnavailable
                }
            ));
        }
        assert!(matches!(
            apply_cert_policy(
                Outcome::Unknown {
                    reason: UnknownReason::Timeout
                },
                &model,
                &full_opts(),
                SupplementalProof::None
            ),
            Outcome::Unknown {
                reason: UnknownReason::Timeout
            }
        ));
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
        // A bare `Bound` from the search is the SAME object as the `Feasible`
        // dual bound just above, minus a primal point to keep — an NS/safe-dual
        // number valid for the LP the rounded `f64` matrix denotes, which is not
        // this model. There is nothing left to report once it is dropped, so the
        // verdict degrades whole. (The `LpSession::rigorous_bound` lane does not
        // pass through here: its NS side declines outright on an inexact model
        // and its exact-rim side builds the `Bound` from an already-finished
        // `Optimal`.)
        Outcome::Bound { .. } => Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
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
    let trace = crate::debug_flags::milp_debug_flags().trace;
    for (proposal, duals) in [first, second].into_iter().enumerate() {
        if let Some(row) = certified_weak_dual_row(model, q, duals, deadline) {
            let sufficient = stronger_than.is_none_or(|threshold| &row.lb > threshold);
            if trace {
                let lb = &row.lb;
                match stronger_than {
                    Some(threshold) => eprintln!(
                        "--trace {trace_context} proposal {proposal}: \
                         lb={lb} threshold={threshold} sufficient={sufficient}"
                    ),
                    None => {
                        eprintln!("--trace {trace_context} proposal {proposal}: lb={lb} accepted")
                    }
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

/// Maximum caller shortlist for the staged four-column shared-prefix selector.
///
/// The selector probes every candidate only at the root, then keeps five and
/// follows one rigorous-bound bottleneck box for its remaining three stages.
/// At this cap it therefore spends at most 34 quick advice calls rather than
/// probing the complete 16-leaf prefix tree.
pub const MAX_TARGET_FSB_PREFIX_CANDIDATES: usize = 8;

/// Resource caps for staged target-objective shared-prefix selection.
///
/// This policy is used only by the explicit marked-margin prefix-candidate
/// entry. It reuses the native tree's already-solved target root; its bounded
/// child LPs rank four prefix columns and have no proof or verdict authority.
/// The local wall limit is hard-clamped to 750 milliseconds by the selector,
/// even if a caller supplies a larger value, and is also bounded by the
/// session's already-pinned search deadline. The clock is polled before and
/// after every quick solve and safe-bound sweep; a single in-progress O(nnz)
/// bound sweep may cross the wall, but its result is then discarded with the
/// whole scan. A partial scan is never used. The local scratch cap includes the
/// bounded safe-bound repair workspace; optional LU reuse remains governed by
/// the simplex's separate LU fill guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetFsbPrefixOpts {
    max_probe_pivots_per_call: u64,
    max_probe_calls: usize,
    probe_time_limit: Duration,
    max_probe_scratch_bytes: usize,
}

impl Default for TargetFsbPrefixOpts {
    fn default() -> Self {
        Self {
            max_probe_pivots_per_call: 8,
            max_probe_calls: 34,
            probe_time_limit: Duration::from_millis(750),
            max_probe_scratch_bytes: 64 << 20,
        }
    }
}

impl TargetFsbPrefixOpts {
    /// Default bounded staged-prefix policy.
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

    /// Set the local advice wall cap. Values above 750 milliseconds are
    /// clamped by the selector; smaller values are useful for tighter callers.
    #[must_use]
    pub fn with_probe_time_limit(mut self, limit: Duration) -> Self {
        self.probe_time_limit = limit;
        self
    }

    /// Set the cap on incremental prefix-selection workspace.
    #[must_use]
    pub fn with_max_probe_scratch_bytes(mut self, bytes: usize) -> Self {
        self.max_probe_scratch_bytes = bytes;
        self
    }

    pub(crate) fn max_probe_pivots_per_call(self) -> u64 {
        self.max_probe_pivots_per_call
    }

    pub(crate) fn max_probe_calls(self) -> usize {
        self.max_probe_calls
    }

    pub(crate) fn probe_time_limit(self) -> Duration {
        self.probe_time_limit
    }

    pub(crate) fn max_probe_scratch_bytes(self) -> usize {
        self.max_probe_scratch_bytes
    }
}

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
    let trace = crate::debug_flags::milp_debug_flags().trace;
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
                "--trace {trace_context}: candidate_col={} zero={zero:.17e} \
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

    /// Bounded constructor for a continuous model assembled internally by a
    /// speculative route from already-validated exact data.  It avoids a
    /// second uninterruptible validation scan and clones every retained row
    /// through the caller's shared work/deadline callback.
    pub(crate) fn new_prevalidated_with_work(
        model: &Model,
        opts: &SolveOpts,
        work: &mut dyn FnMut(usize) -> bool,
    ) -> Result<Option<Self>, MilpError> {
        if !work(model.num_cols()) {
            return Ok(None);
        }
        if model.has_integrality() {
            return Err(MilpError::Model(ModelError::Unsupported {
                reason: "LpSession requires a continuous model; use BabSession for MILP".to_owned(),
            }));
        }
        let Some(model) = model.clone_with_work(work) else {
            return Ok(None);
        };
        Ok(Some(Self {
            model,
            opts: opts.clone(),
            lp: None,
        }))
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
        // This entry always optimizes the model's own objective.  Scan every
        // column so an authoritative nonzero whose f64 proxy underflowed to
        // zero is still present in witness/value replay.
        let exact = authoritative_exact_objective(&self.model);
        Ok(self.optimize_linear(
            &coeffs,
            self.model.sense(),
            self.model.objective_offset(),
            exact,
        ))
    }

    /// Attempt only the float search plus its exact basis/certificate rim.
    ///
    /// This is a crate-private bounded-materialization entry for speculative
    /// structure routes.  Unlike [`Self::optimize_model_objective`], a float
    /// decline returns `None`; it never materializes the independently much
    /// larger [`ExactLp`] fallback.  A returned verdict has passed the same
    /// exact `certify`/`finish` authority as the ordinary float fast path.
    /// Models carrying an exact side store use the rounded matrix only to find
    /// a combinatorial basis; that basis is reconstructed and certified from
    /// the authoritative rational [`Model`] before it can return a verdict.
    pub(crate) fn optimize_model_objective_float_only(
        &mut self,
        work: &mut dyn FnMut(usize) -> bool,
    ) -> Result<Option<Outcome>, MilpError> {
        let Some((coeffs, exact)) = self.model_objective_with_work(work) else {
            return Ok(None);
        };
        let sense = self.model.sense();
        let offset = self.model.objective_offset();
        let solved = SolvedObjective {
            coeffs: &coeffs,
            sense,
            offset,
            exact,
        };
        let deadline = self.opts.effective_deadline(Instant::now());
        Ok(self
            .try_float_lane_deadline_bounded(&coeffs, sense, offset, deadline)
            .map(|outcome| finish_with_work(outcome, &self.model, &solved, &self.opts, work)))
    }

    /// Authoritative exact-only twin used after a speculative route's rounded
    /// advice misses.  ExactLp remains the search engine, while the existing
    /// `finish_with_work` boundary replays the primal, objective, certificate,
    /// and certificate policy under the caller's shared envelope.
    pub(crate) fn optimize_model_objective_exact_only(
        &mut self,
        work: &mut dyn FnMut(usize) -> bool,
    ) -> Result<Option<Outcome>, MilpError> {
        let Some((coeffs, exact_objective)) = self.model_objective_with_work(work) else {
            return Ok(None);
        };
        let sense = self.model.sense();
        let offset = self.model.objective_offset();
        let deadline = self.opts.effective_deadline(Instant::now());
        Ok(Some(self.optimize_linear_until_with_work(
            &coeffs,
            sense,
            offset,
            exact_objective,
            deadline,
            false,
            work,
        )))
    }

    #[cfg(test)]
    pub(crate) fn exact_rim_is_materialized(&self) -> bool {
        self.lp.is_some()
    }

    /// Materialize the rounded search objective and, when present, its
    /// authoritative rational twin under the caller's shared work envelope.
    ///
    /// The exact census deliberately visits every column.  A nonzero rational
    /// coefficient can have an `f64` proxy of zero after underflow and must
    /// still participate in witness replay and certificate policy.
    fn model_objective_with_work(
        &self,
        work: &mut dyn FnMut(usize) -> bool,
    ) -> Option<(Vec<(u32, f64)>, Option<ExactObjective>)> {
        let mut coeffs = Vec::new();
        let mut exact_coefficients = self.model.has_inexact_coeffs().then(Vec::new);
        for i in 0..self.model.num_cols() {
            if i & 0xff == 0 && !work(0x100.min(self.model.num_cols().saturating_sub(i))) {
                return None;
            }
            let column = i as u32;
            let rounded = self.model.obj_coeff(Col(column));
            if rounded != 0.0 {
                coeffs.push((column, rounded));
            }
            if let Some(exact_coefficients) = &mut exact_coefficients {
                let coefficient = self.model.obj_coeff_exact_at(column, rounded);
                if !coefficient.is_zero() {
                    exact_coefficients.push((column, coefficient));
                }
            }
        }
        Some((
            coeffs,
            exact_coefficients.map(|coefficients| (coefficients, self.model.obj_offset_exact())),
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

    /// The float-only speculative-route twin of [`Self::try_float_lane`].
    /// It uses the same exact authority, but threads the route's already-pinned
    /// deadline through basis construction and elimination; a miss declines
    /// instead of falling through to `ExactLp`.
    fn try_float_lane_deadline_bounded(
        &self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        deadline: Option<Instant>,
    ) -> Option<Outcome> {
        if !float_lane_enabled() {
            return None;
        }
        let mut lp = FloatLp::from_model_with_deadline(&self.model, coeffs, sense, deadline)?;
        lp.set_chain_distress_probe_iters(self.opts.chain_distress_probe_iters());
        if self.opts.range_logical_triangular_crash() {
            lp.request_range_logical_triangular_crash();
        }
        lp.plain_cold = true;
        let cand = lp.solve(deadline);
        if cand.status != SimplexStatus::Optimal {
            return None;
        }
        let proven = if self.model.has_inexact_coeffs() {
            certify_model_basis_with_deadline(&self.model, &cand.basis, &cand.at, deadline)?
        } else {
            certify_with_deadline(&self.model, &lp, &cand, deadline)?
        };
        let offset = if self.model.has_inexact_coeffs() {
            self.model.obj_offset_exact()
        } else {
            exact(offset).unwrap_or_else(BigRational::zero)
        };
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
        let mut unlimited = |_| true;
        self.optimize_linear_until_with_work(
            coeffs,
            sense,
            offset,
            model_obj_exact,
            deadline,
            allow_float_lane,
            &mut unlimited,
        )
    }

    fn optimize_linear_until_with_work<F>(
        &mut self,
        coeffs: &[(u32, f64)],
        sense: Sense,
        offset: f64,
        model_obj_exact: Option<ExactObjective>,
        deadline: Option<Instant>,
        allow_float_lane: bool,
        work: &mut F,
    ) -> Outcome
    where
        F: FnMut(usize) -> bool + ?Sized,
    {
        let exact_terms = model_obj_exact
            .as_ref()
            .map_or(0, |(coefficients, _)| coefficients.len());
        if !work(exact_terms.saturating_add(1)) {
            return Outcome::Unknown {
                reason: UnknownReason::Timeout,
            };
        }
        let solved = SolvedObjective {
            coeffs,
            sense,
            offset,
            exact: model_obj_exact,
        };
        // The float certificate lane is built from ROUNDED `f64` coefficients;
        // on an inexact model its certificate would bound the wrong linear form.
        // Decline it and let the exact rim (which reads the true rationals)
        // answer. The exact-coeff fast path is unchanged.
        if allow_float_lane && !self.model.has_inexact_coeffs() {
            if let Some(fast) = self.try_float_lane(coeffs, sense, offset, deadline) {
                return finish_with_work(fast, &self.model, &solved, &self.opts, work);
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
                return finish_with_work(
                    Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    },
                    &self.model,
                    &solved,
                    &self.opts,
                    work,
                );
            };
            self.lp = Some(lp);
        }
        // On an inexact model the exact rim minimizes the TRUE objective from
        // the side-store, and its certificate names that same true objective.
        let obj: Vec<(u32, Rational)> = match &solved.exact {
            Some((c, _)) => {
                let mut v = Vec::with_capacity(c.len());
                for (index, (column, coefficient)) in c.iter().enumerate() {
                    if index & 0xff == 0 && !work(0x100.min(c.len().saturating_sub(index))) {
                        return Outcome::Unknown {
                            reason: UnknownReason::Timeout,
                        };
                    }
                    v.push((*column, Rational::from_big(coefficient.clone())));
                }
                v.sort_unstable_by_key(|&(i, _)| i);
                v
            }
            None => {
                let Some(objective) = exact_obj_with_work(coeffs, work) else {
                    return Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    };
                };
                objective
            }
        };
        // Minimize form: negate for Maximize, un-negate the optimum below.
        let mut solve_obj = Vec::with_capacity(obj.len());
        for (index, (column, coefficient)) in obj.iter().enumerate() {
            if index & 0xff == 0 && !work(0x100.min(obj.len().saturating_sub(index))) {
                return Outcome::Unknown {
                    reason: UnknownReason::Timeout,
                };
            }
            solve_obj.push(match sense {
                Sense::Minimize => (*column, coefficient.clone()),
                Sense::Maximize => (*column, -coefficient.clone()),
            });
        }
        if !work(1) {
            return Outcome::Unknown {
                reason: UnknownReason::Timeout,
            };
        }
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
                let offset = match &solved.exact {
                    Some((_, o)) => o.clone(),
                    None => exact(offset).unwrap_or_else(BigRational::zero),
                };
                let mut certificate_objective = Vec::with_capacity(obj.len());
                for (index, (column, coefficient)) in obj.iter().enumerate() {
                    if index & 0xff == 0 && !work(0x100.min(obj.len().saturating_sub(index))) {
                        return Outcome::Unknown {
                            reason: UnknownReason::Timeout,
                        };
                    }
                    certificate_objective.push((*column, coefficient.to_big()));
                }
                let cert = OptimalityCertificate {
                    sense,
                    objective: certificate_objective,
                    bound: bound.clone(),
                    multipliers,
                };
                let Some(model_values) = lp.structural_values_with_work(work) else {
                    return Outcome::Unknown {
                        reason: UnknownReason::Timeout,
                    };
                };
                Outcome::Optimal {
                    value: bound + offset,
                    model_values,
                    cert: Some(cert),
                }
            }
            LpOptimum::Unbounded => Outcome::Unbounded,
            LpOptimum::Infeasible(cert) => Outcome::Infeasible {
                cert: Some(cert),
                tree_cert: None,
            },
            LpOptimum::Unknown(reason) => Outcome::Unknown { reason },
        };
        finish_with_work(outcome, &self.model, &solved, &self.opts, work)
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
    /// The FLOAT lane's dual vector for a linear objective — fast, and explicitly UNTRUSTED.
    ///
    /// ## Why this is exposed
    ///
    /// [`Self::rigorous_bound_expr`] is rigorous but pays for it: when Neumaier–Shcherbina
    /// declines it falls to the exact rational rim, which on tight, near-degenerate polytopes
    /// is the common case and costs ~300 ms. A caller that can VERIFY a bound itself does not
    /// need the rim — it only needs a good multiplier vector, and the float simplex produces
    /// one in microseconds.
    ///
    /// This is the untrusted half of an untrusted-solver / trusted-verifier split. Weak LP
    /// duality makes any `y` of the right sign yield a valid bound, so the caller can turn
    /// this into a sound result with its own directed-rounding evaluation and never trust the
    /// float lane at all. Star-set reachability does exactly that: it holds the box
    /// `α ∈ [-1,1]` explicitly, so its own Lagrangian evaluation is always finite — which is
    /// precisely where NS's infinite-row-bound case bites.
    ///
    /// SOUNDNESS: the returned duals carry NO guarantee. Using them as if they were a bound
    /// is unsound. They are only useful to a caller that re-derives a bound from them.
    ///
    /// Returns `None` when the float lane is disabled or the simplex does not settle.
    ///
    /// # Errors
    /// [`MilpError::Session`] if a column index is out of range or a weight is non-finite.
    pub fn float_dual_for_expr(
        &mut self,
        expr: &[(Col, f64)],
        sense: Sense,
    ) -> Result<Option<Vec<f64>>, MilpError> {
        for (col, w) in expr {
            if col.index() >= self.model.num_cols() {
                return Err(MilpError::Session {
                    message: format!("column {} out of range", col.index()),
                });
            }
            if !w.is_finite() {
                return Err(MilpError::Session {
                    message: "non-finite objective weight".to_string(),
                });
            }
        }
        if expr.is_empty() || !float_lane_enabled() {
            return Ok(None);
        }
        let scale = match sense {
            Sense::Minimize => 1.0_f64,
            Sense::Maximize => -1.0_f64,
        };
        let scaled: Vec<(u32, f64)> = expr.iter().map(|(c, w)| (c.0, w * scale)).collect();
        let Some(mut lp) = self.float_lp(&scaled, Sense::Minimize) else {
            return Ok(None);
        };
        lp.plain_cold = true;
        let cand = lp.solve(self.opts.effective_deadline(Instant::now()));
        if cand.status != SimplexStatus::Optimal {
            return Ok(None);
        }
        Ok(Some(cand.duals))
    }

    /// Rigorous bound on an arbitrary LINEAR EXPRESSION `Σ wᵢ·x_{cᵢ}`, without
    /// materialising a column for it.
    ///
    /// [`Self::rigorous_bound`] can only bound a single column, so a caller wanting a bound
    /// on a linear form has to add a column plus an equality row tying it to that form. That
    /// is expensive twice over: the model grows by a column AND a row per form, and solve
    /// time scales with model size. A caller bounding many forms over one polytope (star-set
    /// reachability, for instance) pays it on every query.
    ///
    /// This takes the objective directly. The model is untouched, so bounding N forms costs
    /// N solves over the ORIGINAL model rather than N solves over a model that has grown by
    /// 2N entries.
    ///
    /// ## Soundness
    ///
    /// Identical to [`Self::rigorous_bound`]: the Neumaier–Shcherbina bound is valid for the
    /// exact LP no matter how wrong the float dual is, because soundness rests on weak
    /// duality and directed rounding, never on the dual being optimal.
    ///
    /// Two tiers, exactly like [`Self::rigorous_bound`]: the NS bound first, then the EXACT
    /// rim. The rim needs no materialised column — `optimize_linear` already takes an
    /// objective vector and `optimize` is merely its one-entry case — so the expression form
    /// is as TIGHT as the column form, not just cheaper. Anything the rim cannot decide
    /// (infeasible, unbounded, timeout) passes through unchanged; never a non-rigorous
    /// answer.
    ///
    /// An empty expression bounds the constant `0` and returns that exactly.
    ///
    /// # Errors
    /// [`MilpError::Session`] if any column index is out of range.
    pub fn rigorous_bound_expr(
        &mut self,
        expr: &[(Col, f64)],
        sense: Sense,
    ) -> Result<Outcome, MilpError> {
        for (col, w) in expr {
            if col.index() >= self.model.num_cols() {
                return Err(MilpError::Session {
                    message: format!("column {} out of range", col.index()),
                });
            }
            if !w.is_finite() {
                return Err(MilpError::Session {
                    message: "non-finite objective weight".to_string(),
                });
            }
        }
        if expr.is_empty() {
            return Ok(Outcome::Bound {
                dual_bound: BigRational::from_integer(0.into()),
                rigorous: true,
            });
        }
        // Tier 1 — Neumaier-Shcherbina off a single float solve. Cheap, and rigorous
        // however wrong the float dual is.
        if let Some(dual_bound) = self.ns_bound_expr(expr, sense) {
            return Ok(Outcome::Bound {
                dual_bound,
                rigorous: true,
            });
        }
        // Tier 2 — the EXACT rim, same as `rigorous_bound` falls back to. `optimize_linear`
        // already takes an objective vector (`optimize` is just its one-entry case), so the
        // rim never needed a materialised column — only the public API did. Without this
        // tier a weak or declined NS answer was final, which made the expression form lose
        // to the column form on exactly the queries where tightness matters.
        let scaled: Vec<(u32, f64)> = expr.iter().map(|(c, w)| (c.0, *w)).collect();
        Ok(match self.optimize_linear(&scaled, sense, 0.0, None) {
            Outcome::Optimal { value, .. } => Outcome::Bound {
                dual_bound: value,
                rigorous: true,
            },
            other => other,
        })
    }

    /// [`Self::ns_bound`] generalised from a single column to a linear expression.
    ///
    /// The single-column case is exactly this with a one-entry objective, so the two share
    /// their soundness argument: run the float lane once for a dual vector, then evaluate the
    /// weak-duality bound with directed rounding.
    fn ns_bound_expr(&self, expr: &[(Col, f64)], sense: Sense) -> Option<BigRational> {
        // Same side-store caveat as `ns_bound`: NS encloses the f64 matrix, not a different
        // true rational held alongside it.
        if self.model.has_inexact_coeffs() || !float_lane_enabled() {
            return None;
        }
        // Minimize form; `-1` scaling encodes maximize.
        let (scale, flip) = match sense {
            Sense::Minimize => (1.0_f64, false),
            Sense::Maximize => (-1.0_f64, true),
        };
        let scaled: Vec<(u32, f64)> = expr.iter().map(|(c, w)| (c.0, w * scale)).collect();
        let mut lp = self.float_lp(&scaled, Sense::Minimize)?;
        lp.plain_cold = true;
        let cand = lp.solve(self.opts.effective_deadline(Instant::now()));
        if cand.status != SimplexStatus::Optimal {
            return None;
        }
        let mut obj = vec![0.0_f64; self.model.num_cols()];
        for (c, w) in &scaled {
            // Accumulate: a caller may legitimately repeat a column.
            obj[*c as usize] += *w;
        }
        let neg_y: Vec<f64> = cand.duals.iter().map(|d| -d).collect();
        // A dual component paired with an INFINITE row bound sends the NS slack term
        // `min_{s in [lb,ub]} y_r*s` to -inf, and the whole bound with it. The two global
        // sign candidates fix that only when one flip suits EVERY row — true for a
        // single-column objective, but not once the objective spans several columns and the
        // true dual carries mixed signs across one-sided rows.
        //
        // Zeroing the offending component is SOUND: it is exactly dropping that constraint
        // from the dual, and weak duality holds for any validly-signed multiplier vector.
        // The bound is weaker but FINITE, which beats declining outright.
        let clamp = |src: &[f64]| -> Vec<f64> {
            src.iter()
                .enumerate()
                .map(|(r, &yr)| {
                    let (_coeffs, lb, ub) = self.model.row(Row(r as u32));
                    if (yr > 0.0 && !lb.is_finite()) || (yr < 0.0 && !ub.is_finite()) {
                        0.0
                    } else {
                        yr
                    }
                })
                .collect()
        };
        let clamped_y = clamp(&cand.duals);
        let clamped_neg = clamp(&neg_y);
        let best = [
            crate::ns::rigorous_lower_bound(&self.model, &obj, &cand.duals),
            crate::ns::rigorous_lower_bound(&self.model, &obj, &neg_y),
            crate::ns::rigorous_lower_bound(&self.model, &obj, &clamped_y),
            crate::ns::rigorous_lower_bound(&self.model, &obj, &clamped_neg),
        ]
        .into_iter()
        .flatten()
        .fold(f64::NEG_INFINITY, f64::max);
        if !best.is_finite() {
            return None;
        }
        exact(if flip { -best } else { best })
    }

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
                if crate::debug_flags::milp_debug_flags().trace {
                    match stronger_than {
                        Some(threshold) => eprintln!(
                            "--trace harvest exact fallback: lb={} threshold={threshold} sufficient={sufficient}",
                            row.lb
                        ),
                        None => eprintln!(
                            "--trace harvest exact fallback: lb={} accepted",
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
                if crate::debug_flags::milp_debug_flags().trace {
                    eprintln!(
                        "--trace assignment tree prefix bridge: \
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
                    if crate::debug_flags::milp_debug_flags().trace {
                        eprintln!(
                            "--trace assignment tree first proof leaf: \
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
            if step == 0 && warm_start.is_some() && crate::debug_flags::milp_debug_flags().trace {
                eprintln!(
                    "--trace assignment tree first proof leaf: \
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
        if warm_start.is_some() && crate::debug_flags::milp_debug_flags().trace {
            eprintln!(
                "--trace assignment tree root start: strategy={warm_start:?} \
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

        let trace = crate::debug_flags::milp_debug_flags().trace;
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
                    "--trace target FSB first candidate: col={} zero={zero:.17e} \
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
                    "--trace target FSB joint candidate: first_col={} \
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
                "--trace target FSB selected: first_col={} first_worst={first_worst:.17e} \
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

        let trace = crate::debug_flags::milp_debug_flags().trace;
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
                    "--trace adaptive three-leaf candidate: root_col={} hard={} \
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
                "--trace adaptive three-leaf selected: root_col={} hard={} \
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

        let trace = crate::debug_flags::milp_debug_flags().trace;
        if trace {
            eprintln!(
                "--trace adaptive four-leaf anchor: root_col={} root_hard={} status=optimal",
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
                    "--trace adaptive four-leaf second candidate: root_col={} \
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
                    "--trace adaptive four-leaf third candidate: root_col={} \
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
                "--trace adaptive four-leaf selected: root_col={} root_hard={} \
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

        let trace = crate::debug_flags::milp_debug_flags().trace;
        if trace {
            eprintln!(
                "--trace adaptive five-leaf anchor: root_col={} root_hard={} status=optimal",
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
                "--trace adaptive five-leaf selected: root_col={} root_hard={} \
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

/// Convert an exact, independently checked point into native MILP incumbent
/// advice. This conversion carries no proof authority: `solve_milp_seeded`
/// validates the resulting floating candidate against the original model and
/// simply drops it if rounding moved it outside the feasible set.
fn exact_point_to_f64_seed(point: &[BigRational]) -> Option<Vec<f64>> {
    use num_traits::ToPrimitive;

    point
        .iter()
        .map(|value| value.to_f64().filter(|value| value.is_finite()))
        .collect()
}

/// A feasible point closes a decision problem, but on an optimization model an
/// explicitly anytime result is only an incumbent. It must not pre-empt the
/// complete native proof path.
fn exact_reduction_feasible_must_continue_native(
    has_objective: bool,
    incumbent_only: bool,
) -> bool {
    has_objective && incumbent_only
}

#[cfg(test)]
mod exact_reduction_fallback_tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn anytime_pb_point_never_terminates_optimization() {
        assert!(exact_reduction_feasible_must_continue_native(true, true));
        assert!(!exact_reduction_feasible_must_continue_native(false, true));
        assert!(!exact_reduction_feasible_must_continue_native(true, false));
    }

    #[test]
    fn checked_network_replay_handoff_is_one_shot_and_model_scoped() {
        let mut model = Model::new();
        model.add_binary_col();
        let mut session = BabSession::new(model, &SolveOpts::new()).expect("valid session");
        session.pending_network_design_replay = Some(NetworkDesignReplayHandoff::ReadyReplay(
            crate::pb_route::PbRouteDecision::Infeasible,
        ));

        assert!(matches!(
            session.take_pending_network_design_replay(),
            Some(NetworkDesignReplayHandoff::ReadyReplay(
                crate::pb_route::PbRouteDecision::Infeasible
            ))
        ));
        assert!(session.take_pending_network_design_replay().is_none());

        session.pending_network_design_replay = Some(NetworkDesignReplayHandoff::LazyOnly(None));
        assert!(matches!(
            session.take_pending_network_design_replay(),
            Some(NetworkDesignReplayHandoff::LazyOnly(None))
        ));
        assert!(session.take_pending_network_design_replay().is_none());

        session.pending_network_design_replay = Some(NetworkDesignReplayHandoff::LazyOnly(None));
        session.invalidate_last_evidence();
        assert!(session.take_pending_network_design_replay().is_none());
    }

    #[test]
    fn pending_network_continuation_keeps_priority_over_block_angular() {
        let mut model = Model::new();
        model.add_binary_col();
        let mut session = BabSession::new(model, &SolveOpts::new()).expect("valid session");
        assert!(session.may_offer_block_angular_before_network_replay());

        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::LazyOnly(None));
        assert!(
            !session.may_offer_block_angular_before_network_replay(),
            "a speculative block route must not spend the shared deadline before a checked \
             lazy-network continuation"
        );
        assert!(matches!(
            session.take_pending_network_design_replay(),
            Some(NetworkDesignReplayHandoff::LazyOnly(None))
        ));
        assert!(session.may_offer_block_angular_before_network_replay());
    }

    #[test]
    fn checked_network_optimum_seeds_native_before_full_policy_drops_replay() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.set_objective(&[(x, 1.0)], Sense::Minimize);
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("valid full-policy session");
        let point = vec![BigRational::from_integer(BigInt::from(1))];

        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::ReadyReplay(
            crate::pb_route::PbRouteDecision::Optimal {
                value: BigRational::from_integer(BigInt::from(1)),
                model_values: point,
            },
        ));

        assert_eq!(session.incumbent_seed, Some(vec![1.0]));
        assert!(session.take_pending_network_design_replay().is_none());
    }

    #[test]
    fn default_policy_keeps_seeded_network_replay_one_shot() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.set_objective(&[(x, 1.0)], Sense::Maximize);
        let mut session = BabSession::new(model, &SolveOpts::new()).expect("valid session");

        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::ReadyReplay(
            crate::pb_route::PbRouteDecision::Optimal {
                value: BigRational::from_integer(BigInt::from(1)),
                model_values: vec![BigRational::from_integer(BigInt::from(1))],
            },
        ));

        assert_eq!(session.incumbent_seed, Some(vec![1.0]));
        assert!(matches!(
            session.take_pending_network_design_replay(),
            Some(NetworkDesignReplayHandoff::ReadyReplay(
                crate::pb_route::PbRouteDecision::Optimal { .. }
            ))
        ));
        assert!(session.take_pending_network_design_replay().is_none());
    }

    #[test]
    fn full_policy_drops_lazy_network_handoff_without_disturbing_existing_seed() {
        let mut model = Model::new();
        model.add_binary_col();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("valid full-policy session");
        session.incumbent_seed = Some(vec![0.0]);

        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::LazyOnly(None));

        assert_eq!(session.incumbent_seed, Some(vec![0.0]));
        assert!(session.take_pending_network_design_replay().is_none());
    }

    #[test]
    fn full_policy_seeds_checked_lazy_incumbent_before_dropping_handoff() {
        let mut model = Model::new();
        model.add_binary_col();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("valid full-policy session");

        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::LazyOnly(Some(
            crate::pb_route::PbRouteDecision::Feasible {
                model_values: vec![BigRational::from_integer(BigInt::from(1))],
                incumbent_only: true,
            },
        )));

        assert_eq!(session.incumbent_seed, Some(vec![1.0]));
        assert!(session.take_pending_network_design_replay().is_none());
    }

    #[test]
    fn exact_point_seed_conversion_fails_closed_on_non_finite_values() {
        let finite = vec![
            BigRational::from_integer(BigInt::from(0)),
            BigRational::new(BigInt::from(1), BigInt::from(3)),
        ];
        let converted = exact_point_to_f64_seed(&finite).expect("finite point");
        assert_eq!(converted.len(), 2);
        assert_eq!(converted[0], 0.0);
        assert!(converted[1].is_finite());

        let enormous = vec![BigRational::from_integer(BigInt::from(1) << 20_000usize)];
        assert!(exact_point_to_f64_seed(&enormous).is_none());
    }

    #[test]
    fn full_policy_adopts_revalidated_parity_infeasibility() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y0 = model.add_int_col(0.0, f64::INFINITY);
        let y1 = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(x, 1.0), (y0, -2.0)]);
        model.add_row(-1.0, -1.0, &[(x, 1.0), (y1, -2.0)]);
        model.set_objective(&[(x, 1.0)], Sense::Minimize);

        let opts = SolveOpts::new()
            .with_time_limit(Duration::from_secs(5))
            .with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("parity solve");
        assert!(matches!(outcome, Outcome::Infeasible { .. }));
        let certificate = session
            .parity_infeasibility_certificate()
            .expect("typed parity refutation");
        crate::verify_parity_infeasibility_certificate(session.model(), certificate)
            .expect("session certificate must replay against its source model");
    }

    #[test]
    fn native_session_adopts_revalidated_open_domain_infeasibility() {
        for require_certificates in [false, true] {
            let mut model = Model::new();
            let x = model.add_binary_col();
            let open = model.add_int_col(0.0, f64::INFINITY);
            model.add_row(2.0, f64::INFINITY, &[(open, 1.0)]);
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);

            let opts = SolveOpts::new()
                .with_time_limit(Duration::from_secs(5))
                .with_require_certificates(require_certificates);
            let mut session = BabSession::new(model, &opts).expect("session");
            let outcome = session.check().expect("open-domain solve");
            assert!(matches!(outcome, Outcome::Infeasible { .. }));
            assert!(session.replay_claims().is_empty());
            assert!(
                session
                    .open_domain_single_row_dp_infeasibility_certificate()
                    .is_some()
                    || session
                        .open_domain_multi_row_bdd_infeasibility_certificate()
                        .is_some()
            );
        }
    }

    #[test]
    fn native_session_adopts_revalidated_open_domain_optimum() {
        let mut model = Model::new();
        let bounded = model.add_int_col(0.0, 2.0);
        let open = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(3.0, f64::INFINITY, &[(bounded, 1.0), (open, 1.0)]);
        model.set_objective(&[(bounded, 1.0), (open, 2.0)], Sense::Minimize);

        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(5));
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("open-domain solve");
        let Outcome::Optimal {
            value,
            model_values,
            ..
        } = outcome
        else {
            panic!("open-domain route must close the model")
        };
        assert_eq!(value, BigRational::from_integer(BigInt::from(4)));
        session.model().check_point(&model_values).unwrap();
        assert!(session
            .replay_claims()
            .iter()
            .any(|claim| claim.claim == "open-domain-cap-optimal"));
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
    /// ay-dpll typed-Solver fallback, forced with `--smt-lane`.
    #[cfg(feature = "smt")]
    Smt(Box<crate::smt::SmtMilp>),
    /// Exact rim (continuous models).
    Exact,
}

/// How one [`BabSession`] entry treats a marked margin.
enum MarginMode<'a> {
    Auto,
    Disabled,
    Required,
    ReframedProof(crate::margin::MarginProofTarget<'a>),
}

/// One-shot continuation passed from certificate-first network work to the
/// later default/replay boundary in the same `check`. It either carries a
/// checked conclusive raw result or authorizes exactly the distinct lazy
/// Hoffman/Benders arm, optionally seeded by a checked incumbent.
enum NetworkDesignReplayHandoff {
    ReadyReplay(crate::pb_route::PbRouteDecision),
    LazyOnly(Option<crate::pb_route::PbRouteDecision>),
}

/// Whether a MILP goes down the old ay-dpll lowering instead of the native
/// branch-and-bound. The A/B switch the native lane is measured against.
fn smt_lane_forced() -> bool {
    static FORCED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FORCED.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::SmtLane) == Some(true))
}

fn structure_trace_enabled() -> bool {
    crate::debug_flags::milp_debug_flags().trace
}

/// The verdict word, for the one message a consumer must be able to read
/// without a debugger: the portfolio disagreement trap.
fn verdict_word(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Optimal { .. } => "OPTIMAL",
        Outcome::Feasible { .. } => "FEASIBLE",
        Outcome::Infeasible { .. } => "INFEASIBLE",
        Outcome::Unbounded => "UNBOUNDED",
        Outcome::Bound { .. } => "BOUND",
        Outcome::Unknown { .. } => "UNKNOWN",
    }
}

/// Which single exit a lane's verdict leaves through.
///
/// `ExactReduction` re-validates the witness against the caller's exact model;
/// `AlreadyFinished` preserves a private checked-point or supplemental-proof
/// finalizer. Naming them lets
/// [`BabSession::admit_or_defer`] be the ONE place the evidence floor is
/// consulted, instead of the floor being re-implemented at every lane's own
/// `return`.
#[derive(Clone, Copy)]
enum Finisher {
    ExactReduction,
    /// The lane's private finalizer has already checked the exact point or
    /// supplemental artifact and applied certificate policy. Admission still
    /// owns whether the resulting claim may end the solve, but must not erase
    /// proof information that is carried outside `Outcome`.
    AlreadyFinished,
}

/// A MILP session with scoped `fix_col`/`add_row`, feasibility and
/// optimization checks, cut harvesting (native engine only).
pub struct BabSession {
    model: Model,
    opts: SolveOpts,
    lane: MilpLane,
    scopes: Vec<ScopeFrame>,
    /// A verdict a lane produced that is NOT allowed to end the solve yet,
    /// because [`crate::claim::may_close`] found its evidence below what the
    /// anchor could still reach on this model.
    ///
    /// This is where the `W1_unsat_v9_c14_000008` evidence downgrade is
    /// repaired. It is a HOLDING slot, never a discard slot: the claim is
    /// published verbatim the moment the anchor's bounded first refusal fails
    /// to do better, so the portfolio can lose latency here and can never lose
    /// a verdict.
    deferred_claim: Option<crate::claim::Deferred>,
    /// `(lane, claim)` the evidence floor held back during the last check.
    /// Reported by [`BabSession::deferred_lane`]; see it for why this is
    /// recorded rather than inferred.
    last_deferred: Option<(&'static str, &'static str)>,
    /// Advice-only incumbent seeds and branching guidance for the native engine.
    incumbent_seed: Option<Vec<f64>>,
    branch_hints: Vec<Col>,
    root_strong_branch_shortlist: Vec<Col>,
    /// One continuation produced by certificate-first network work. The later
    /// replay/default boundary consumes it instead of rebuilding and searching
    /// the identical eager projection a second time in the same check.
    pending_network_design_replay: Option<NetworkDesignReplayHandoff>,
    /// Replay claims filed by the LAST [`Self::check`]: verdicts a device
    /// reached by exhaustive computation with NO exportable certificate.
    ///
    /// Per SESSION, not per process. A process-global would let one solve's
    /// "trust me" annotation attach to another solve's verdict, which is
    /// precisely the failure the certificate format exists to prevent.
    replay_claims: Vec<crate::cert_io::ReplayClaim>,
    /// Exact source-row parity contradiction produced by the GF(2) route.
    parity_infeasibility_certificate: Option<crate::ParityInfeasibilityCertificate>,
    /// Exact SAT/ReLU projection plus independently replayed RUP refutation.
    sat_relu_infeasibility_certificate: Option<crate::SatReluInfeasibilityCertificate>,
    /// Exact Hoffman-master refutation produced by the last certified network
    /// design route.
    network_design_infeasibility_certificate: Option<crate::NetworkDesignInfeasibilityCertificate>,
    /// Exact strict-better-face refutation produced by the last certified
    /// network design optimum.
    network_design_optimality_certificate: Option<crate::NetworkDesignOptimalityCertificate>,
    /// Exact Lagrangian lower bound for the last recognized integral
    /// conservation-chain block-angular optimum.
    block_angular_optimality_certificate: Option<crate::BlockAngularOptimalityCertificate>,
    /// Exact sequence and independently replayed DP optimum produced by the
    /// last recognized single-machine scheduling solve.
    single_machine_scheduling_optimality_certificate:
        Option<crate::SingleMachineSchedulingOptimalityCertificate>,
    /// Independently replayable proof exported by the last exact single-row
    /// PB infeasibility route, when that route owned the verdict.
    single_row_dp_infeasibility_certificate:
        Option<ay_pb_core::SingleRowDpInfeasibilityCertificate>,
    /// Independently replayable proof exported by the last exact general PB
    /// infeasibility route, when that route owned the verdict.
    multi_row_bdd_infeasibility_certificate:
        Option<ay_pb_core::MultiRowBddInfeasibilityCertificate>,
    /// Residual PB proof exported by the last exact open-domain projection.
    /// It is intentionally distinct from a direct source-model PB proof.
    open_domain_single_row_dp_infeasibility_certificate:
        Option<ay_pb_core::SingleRowDpInfeasibilityCertificate>,
    /// General residual PB proof from the last exact open-domain projection.
    open_domain_multi_row_bdd_infeasibility_certificate:
        Option<ay_pb_core::MultiRowBddInfeasibilityCertificate>,
    /// Hybrid proof over a deterministically rebuilt open-domain residual.
    open_domain_hybrid_pb_lp_infeasibility_certificate:
        Option<crate::HybridPbLpInfeasibilityCertificate>,
    /// Integer-lifted hybrid proof over a rebuilt open-domain residual.
    open_domain_hybrid_integer_lift_infeasibility_certificate:
        Option<crate::HybridIntegerLiftInfeasibilityCertificate>,
    /// Exact cut ledger plus final PB refutation from the last binary-master /
    /// continuous-recourse hybrid verdict.
    hybrid_pb_lp_infeasibility_certificate: Option<crate::HybridPbLpInfeasibilityCertificate>,
    /// Nested hybrid proof whose bounded general-integer radix lift is rebuilt
    /// from the source model by the independent checker.
    hybrid_integer_lift_infeasibility_certificate:
        Option<crate::HybridIntegerLiftInfeasibilityCertificate>,
}

/// Census-frame ownership for one `BabSession::check`.
///
/// Only a check with no inherited carrier is a `TopLevelOwner`: it creates the
/// frame and defines the one-solve census unit. Internal checks, currently the
/// margin reframe, are `NestedBorrower`s and must retain that exact frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FtAdoptionFrameOwnership {
    TopLevelOwner,
    NestedBorrower,
}

#[cfg(test)]
std::thread_local! {
    static FT_ADOPTION_FRAME_ENTRY_COUNTS: std::cell::Cell<(u64, u64)> =
        const { std::cell::Cell::new((0, 0)) };
}

#[cfg(test)]
fn ft_adoption_frame_entry_counts() -> (u64, u64) {
    FT_ADOPTION_FRAME_ENTRY_COUNTS.with(std::cell::Cell::get)
}

/// Installs one census frame for the duration of a check and removes its local
/// carriers on every return or unwind.
///
/// A nested session owns cloned model/options carriers, so clearing them does
/// not disturb the outer session's carriers or the shared latch.
struct FtAdoptionFrame<'a> {
    session: &'a mut BabSession,
    _ownership: FtAdoptionFrameOwnership,
}

impl<'a> FtAdoptionFrame<'a> {
    fn enter(session: &'a mut BabSession) -> Self {
        let model_latch = session.model.ft_adoption_solve_latch();
        let opts_latch = session.opts.ft_adoption_solve_latch();
        let (latch, ownership) = match (model_latch, opts_latch) {
            (Some(model_latch), Some(opts_latch)) => {
                debug_assert!(
                    model_latch.same_frame(&opts_latch),
                    "model and solve options carried different FT-adoption frames"
                );
                (opts_latch, FtAdoptionFrameOwnership::NestedBorrower)
            }
            (Some(latch), None) | (None, Some(latch)) => {
                (latch, FtAdoptionFrameOwnership::NestedBorrower)
            }
            (None, None) => (
                crate::sepstat::FtAdoptionSolveLatch::new(),
                FtAdoptionFrameOwnership::TopLevelOwner,
            ),
        };
        #[cfg(test)]
        FT_ADOPTION_FRAME_ENTRY_COUNTS.with(|counts| {
            let (owners, borrowers) = counts.get();
            counts.set(match ownership {
                FtAdoptionFrameOwnership::TopLevelOwner => (owners + 1, borrowers),
                FtAdoptionFrameOwnership::NestedBorrower => (owners, borrowers + 1),
            });
        });
        session.model.set_ft_adoption_solve_latch(latch.clone());
        session.opts.set_ft_adoption_solve_latch(latch);
        Self {
            session,
            _ownership: ownership,
        }
    }

    #[cfg(test)]
    fn ownership(&self) -> FtAdoptionFrameOwnership {
        self._ownership
    }
}

impl Drop for FtAdoptionFrame<'_> {
    fn drop(&mut self) {
        self.session.model.clear_ft_adoption_solve_latch();
        self.session.opts.clear_ft_adoption_solve_latch();
    }
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
            deferred_claim: None,
            last_deferred: None,
            incumbent_seed: None,
            branch_hints: Vec::new(),
            root_strong_branch_shortlist: Vec::new(),
            pending_network_design_replay: None,
            replay_claims: Vec::new(),
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
        })
    }

    /// Replay claims filed by the last [`Self::check`].
    ///
    /// Each names a claim this build proved by RUNNING A COMPUTATION rather than
    /// by producing a checkable object. A consumer that wants only certified
    /// verdicts checks that this slice is empty; a consumer writing a
    /// certificate emits them as `REPLAY`, which can never be reported as
    /// verified. If this set GROWS between releases, something regressed from
    /// provable to trusted.
    #[must_use]
    pub fn replay_claims(&self) -> &[crate::cert_io::ReplayClaim] {
        &self.replay_claims
    }

    /// Which lane, if any, had a verdict HELD BACK by the evidence floor during
    /// the last [`Self::check`], and what it asserted.
    ///
    /// `None` means every lane that produced a verdict was allowed to publish it
    /// — either because its evidence already matched what the anchor could reach,
    /// or because no lane produced one at all.
    ///
    /// This exists because "did the floor engage?" is otherwise only observable
    /// through wall-clock behaviour, and a test that infers it from timing is a
    /// test that passes on a fast machine and fails on a slow one. It is also
    /// the honest thing to be able to ask a solver: *did you hold something
    /// back, and what was it?*
    #[must_use]
    pub fn deferred_lane(&self) -> Option<(&'static str, &'static str)> {
        self.last_deferred
    }

    /// **THE ONE PLACE A LANE IS ALLOWED TO END THE SOLVE.**
    ///
    /// `Some(out)` — the lane's evidence for every claim its verdict asserts is
    /// at least as strong as anything the anchor could still have attached, so
    /// it publishes and the solve is over.
    ///
    /// `None` — at least one claim is below the anchor's reach. The verdict is
    /// NOT discarded and NOT weakened: it is parked in `deferred_claim` and the
    /// caller falls through to native search, which gets a bounded first
    /// refusal at producing something better. Whatever native comes back with,
    /// [`Self::publish_deferred_if_native_did_not_decide`] guarantees the
    /// deferred verdict is published if native did not decide — so deferring
    /// costs latency and can never cost a verdict.
    ///
    /// The lane's replay claims travel WITH the deferred verdict rather than
    /// staying in the thread-local ledger. That is not tidiness: a claim left in
    /// the ledger would attach to whatever verdict is returned next, which is
    /// exactly the cross-attribution the `replay_claims` doc comment warns
    /// about and which speculation makes more likely, not less.
    fn admit_or_defer(
        &mut self,
        lane: &crate::claim::LaneFloor,
        outcome: Outcome,
        solved: &SolvedObjective<'_>,
        lane_claims: Vec<crate::cert_io::ReplayClaim>,
        finisher: Finisher,
    ) -> Option<Outcome> {
        // `--anchor-first-refusal-ms` is the DEGENERATE POINT: deferral
        // off, every lane closes exactly as it did before the evidence floor
        // existed. Keeping that arm alive is what lets a differential test
        // assert the invariant on one binary instead of arguing about two.
        let deferral_available = !crate::claim::anchor_first_refusal_cap().is_zero();
        if !deferral_available
            || crate::claim::may_close_outcome(lane, &outcome, &self.model, &self.opts)
        {
            for claim in lane_claims {
                crate::cert_io::ledger::record(claim);
            }
            return Some(match finisher {
                Finisher::ExactReduction => {
                    finish_exact_reduction(outcome, &self.model, solved, &self.opts)
                }
                Finisher::AlreadyFinished => outcome,
            });
        }
        if structure_trace_enabled() {
            // Name the claim AND both sides of the comparison. "deferred" on its
            // own is not diagnosable; "infeasible REPLAY < SUCCINCT" says which
            // cell of the floor table fired and what would change it.
            let below: Vec<String> = crate::claim::claims_of(&outcome)
                .iter()
                .filter(|&&c| !crate::claim::may_close(lane, c, &self.model, &self.opts))
                .map(|&c| {
                    format!(
                        "{} {} < {}",
                        c.token(),
                        lane.get(c).token(),
                        crate::claim::anchor_cap(&self.model, &self.opts, c).token(),
                    )
                })
                .collect();
            eprintln!(
                "--trace portfolio: lane={} DEFERRED ({}) — native gets first refusal",
                lane.lane,
                below.join("; "),
            );
        }
        // First writer wins, deterministically: lanes run in source order, so
        // the first below-floor verdict is the one held. A second lane reaching
        // here has produced the same verdict with no better evidence (or it
        // would have closed), so replacing the held one would change nothing.
        //
        // Its replay claim is still FILED rather than dropped. Two independent
        // exact devices that both refuted the model is worth more in the `.ayc`
        // than one, and silently discarding evidence is the habit this whole
        // change exists to break.
        if self.deferred_claim.is_some() {
            for claim in lane_claims {
                crate::cert_io::ledger::record(claim);
            }
            return None;
        }
        self.last_deferred = Some((
            lane.lane,
            crate::claim::claims_of(&outcome)
                .first()
                .copied()
                .unwrap_or(crate::claim::ClaimKind::Infeasible)
                .token(),
        ));
        self.deferred_claim = Some(crate::claim::Deferred {
            lane: lane.lane,
            outcome,
            replay_claims: lane_claims,
        });
        None
    }

    /// Succinct exact GF(2) source-row contradiction produced by the last check.
    #[must_use]
    pub fn parity_infeasibility_certificate(
        &self,
    ) -> Option<&crate::ParityInfeasibilityCertificate> {
        self.parity_infeasibility_certificate.as_ref()
    }

    /// Model-bound resolution refutation produced by the SAT/ReLU route.
    #[must_use]
    pub fn sat_relu_infeasibility_certificate(
        &self,
    ) -> Option<&crate::SatReluInfeasibilityCertificate> {
        self.sat_relu_infeasibility_certificate.as_ref()
    }

    /// Succinct exact Hoffman-projection refutation produced by the last check.
    #[must_use]
    pub fn network_design_infeasibility_certificate(
        &self,
    ) -> Option<&crate::NetworkDesignInfeasibilityCertificate> {
        self.network_design_infeasibility_certificate.as_ref()
    }

    /// Succinct strict-better-face proof for the last network-design optimum.
    #[must_use]
    pub fn network_design_optimality_certificate(
        &self,
    ) -> Option<&crate::NetworkDesignOptimalityCertificate> {
        self.network_design_optimality_certificate.as_ref()
    }

    /// Succinct exact Lagrangian proof for the last block-angular optimum.
    #[must_use]
    pub fn block_angular_optimality_certificate(
        &self,
    ) -> Option<&crate::BlockAngularOptimalityCertificate> {
        self.block_angular_optimality_certificate.as_ref()
    }

    /// Exact source sequence plus independently replayable scheduling optimum.
    #[must_use]
    pub fn single_machine_scheduling_optimality_certificate(
        &self,
    ) -> Option<&crate::SingleMachineSchedulingOptimalityCertificate> {
        self.single_machine_scheduling_optimality_certificate
            .as_ref()
    }

    /// Succinct exact single-row PB proof produced by the last check.
    #[must_use]
    pub fn single_row_dp_infeasibility_certificate(
        &self,
    ) -> Option<&ay_pb_core::SingleRowDpInfeasibilityCertificate> {
        self.single_row_dp_infeasibility_certificate.as_ref()
    }

    /// Succinct exact multi-row PB decision-DAG proof produced by the last check.
    #[must_use]
    pub fn multi_row_bdd_infeasibility_certificate(
        &self,
    ) -> Option<&ay_pb_core::MultiRowBddInfeasibilityCertificate> {
        self.multi_row_bdd_infeasibility_certificate.as_ref()
    }

    /// Succinct single-row proof over a deterministically rebuilt open-domain
    /// residual produced by the last check.
    #[must_use]
    pub fn open_domain_single_row_dp_infeasibility_certificate(
        &self,
    ) -> Option<&ay_pb_core::SingleRowDpInfeasibilityCertificate> {
        self.open_domain_single_row_dp_infeasibility_certificate
            .as_ref()
    }

    /// Succinct general PB proof over a deterministically rebuilt open-domain
    /// residual produced by the last check.
    #[must_use]
    pub fn open_domain_multi_row_bdd_infeasibility_certificate(
        &self,
    ) -> Option<&ay_pb_core::MultiRowBddInfeasibilityCertificate> {
        self.open_domain_multi_row_bdd_infeasibility_certificate
            .as_ref()
    }

    /// Succinct hybrid refutation over a rebuilt open-domain residual.
    #[must_use]
    pub fn open_domain_hybrid_pb_lp_infeasibility_certificate(
        &self,
    ) -> Option<&crate::HybridPbLpInfeasibilityCertificate> {
        self.open_domain_hybrid_pb_lp_infeasibility_certificate
            .as_ref()
    }

    /// Succinct integer-lifted hybrid refutation over an open-domain residual.
    #[must_use]
    pub fn open_domain_hybrid_integer_lift_infeasibility_certificate(
        &self,
    ) -> Option<&crate::HybridIntegerLiftInfeasibilityCertificate> {
        self.open_domain_hybrid_integer_lift_infeasibility_certificate
            .as_ref()
    }

    /// Succinct hybrid PB/LP cut-ledger refutation produced by the last check.
    #[must_use]
    pub fn hybrid_pb_lp_infeasibility_certificate(
        &self,
    ) -> Option<&crate::HybridPbLpInfeasibilityCertificate> {
        self.hybrid_pb_lp_infeasibility_certificate.as_ref()
    }

    /// Succinct exact integer-lifted hybrid refutation produced by the last check.
    #[must_use]
    pub fn hybrid_integer_lift_infeasibility_certificate(
        &self,
    ) -> Option<&crate::HybridIntegerLiftInfeasibilityCertificate> {
        self.hybrid_integer_lift_infeasibility_certificate.as_ref()
    }

    /// The model this session owns (Lever A accessor). Callers that used to keep
    /// their own copy of the pre-`new` model — e.g. to compute the objective value
    /// of an outcome — read it here instead, so only ONE f64 matrix is resident.
    #[must_use]
    pub fn model(&self) -> &Model {
        &self.model
    }

    /// Evidence belongs to the exact model state solved by the last check.
    /// Any model mutation invalidates every replay annotation and typed side
    /// artifact before the mutation can become externally observable.
    fn invalidate_last_evidence(&mut self) {
        self.pending_network_design_replay = None;
        self.replay_claims.clear();
        self.parity_infeasibility_certificate = None;
        self.sat_relu_infeasibility_certificate = None;
        crate::parity::clear_pending_infeasibility_certificate();
        self.network_design_infeasibility_certificate = None;
        self.network_design_optimality_certificate = None;
        self.block_angular_optimality_certificate = None;
        self.single_machine_scheduling_optimality_certificate = None;
        self.single_row_dp_infeasibility_certificate = None;
        self.multi_row_bdd_infeasibility_certificate = None;
        self.open_domain_single_row_dp_infeasibility_certificate = None;
        self.open_domain_multi_row_bdd_infeasibility_certificate = None;
        self.open_domain_hybrid_pb_lp_infeasibility_certificate = None;
        self.open_domain_hybrid_integer_lift_infeasibility_certificate = None;
        self.hybrid_pb_lp_infeasibility_certificate = None;
        self.hybrid_integer_lift_infeasibility_certificate = None;
    }

    fn take_pending_network_design_replay(&mut self) -> Option<NetworkDesignReplayHandoff> {
        self.pending_network_design_replay.take()
    }

    fn may_offer_block_angular_before_network_replay(&self) -> bool {
        self.pending_network_design_replay.is_none()
    }

    /// Install a checked one-shot network continuation for the replay posture.
    /// A checked witness is useful incumbent advice even when full-certificate
    /// policy disables replay routes. In that posture retain the seed but not
    /// the otherwise-unconsumable exact handoff.
    fn install_network_design_replay_handoff(&mut self, handoff: NetworkDesignReplayHandoff) {
        if self.incumbent_seed.is_none() {
            let checked_decision = match &handoff {
                NetworkDesignReplayHandoff::ReadyReplay(decision)
                | NetworkDesignReplayHandoff::LazyOnly(Some(decision)) => Some(decision),
                NetworkDesignReplayHandoff::LazyOnly(None) => None,
            };
            if let Some(decision) = checked_decision {
                match decision {
                    crate::pb_route::PbRouteDecision::Feasible { model_values, .. }
                    | crate::pb_route::PbRouteDecision::Optimal { model_values, .. } => {
                        self.incumbent_seed = exact_point_to_f64_seed(model_values);
                    }
                    crate::pb_route::PbRouteDecision::Infeasible
                    | crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                    | crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible { .. } => {}
                }
            }
        }
        self.pending_network_design_replay = if self.opts.require_certificates {
            None
        } else {
            Some(handoff)
        };
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
        self.invalidate_last_evidence();
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
        self.invalidate_last_evidence();
        self.model.fix_col(col, value);
        #[cfg(feature = "smt")]
        if let MilpLane::Smt(smt) = &mut self.lane {
            smt.fix_col(col, value)?;
        }
        Ok(())
    }

    /// Add a row `lb <= coeffs·x <= ub` in the current scope (lazy cuts).
    pub fn add_row(&mut self, lb: f64, ub: f64, coeffs: &[(Col, f64)]) -> Result<Row, MilpError> {
        self.invalidate_last_evidence();
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
        self.check_with_shared_binary_prefix(&[], None, MarginMode::Auto, None)
    }

    /// Solve one complete binary-prefix partition inside ONE native
    /// branch-and-bound session.
    ///
    /// The ordered `split_cols` define all `2^k` assignments (`0` before `1`,
    /// first column most significant). Unlike a caller loop that clones and
    /// fixes the model once per assignment, this path prepares presolve, root
    /// cuts, the root LP, incumbent state, pseudocosts, and conflict learning
    /// exactly once, then seats every assignment in the native open frontier.
    /// It is the serial, deterministic state boundary for a later worker pool:
    /// one thread already consumes the same shared frontier without changing
    /// the default [`Self::check`] path.
    ///
    /// This API is deliberately narrow and default-dark:
    ///
    /// - one through four distinct, currently-live binary columns;
    /// - native MILP lane only;
    /// - no external incumbent seed yet (a future snapshot must define its
    ///   replay frame rather than silently mixing ownership);
    /// - one absolute session deadline for root preparation and every region.
    ///
    /// Any incomplete region leaves the common search incomplete and therefore
    /// returns the ordinary fail-closed `Unknown`/incumbent-only outcome. An
    /// infeasibility certificate is emitted only by the existing whole-tree
    /// capture and is independently replay-verified against this session's
    /// caller-frame model by [`finish`].
    pub fn check_shared_binary_prefix(&mut self, split_cols: &[Col]) -> Result<Outcome, MilpError> {
        self.validate_shared_binary_prefix(split_cols)?;
        self.check_with_shared_binary_prefix(split_cols, None, MarginMode::Disabled, None)
    }

    /// Solve one marked decision margin over a complete binary-prefix
    /// partition in one native branch-and-bound session.
    ///
    /// This explicit API requires a clean one-sided margin named by
    /// [`Model::mark_margin_row`]. A rigorous interrupted-tree bound may
    /// trigger caller-frame proof replay only after a strict exact threshold
    /// crossing; the bound itself is never verdict authority. Infeasibility
    /// still requires an independently verified
    /// [`MilpInfeasibilityCertificate`] against the original model, even when
    /// the generic [`SolveOpts::with_require_certificates`] policy is disabled.
    ///
    /// Prefix validation, incumbent ownership, and the single absolute
    /// deadline are identical to [`Self::check_shared_binary_prefix`].
    pub fn check_marked_margin_shared_binary_prefix(
        &mut self,
        split_cols: &[Col],
    ) -> Result<Outcome, MilpError> {
        self.validate_shared_binary_prefix(split_cols)?;
        self.check_with_shared_binary_prefix(split_cols, None, MarginMode::Required, None)
    }

    /// Select four marked-margin shared-prefix columns with a bounded staged
    /// target-FSB scan, then solve the same complete prefix partition.
    ///
    /// `fallback_prefix` is the exact prefix used when advice is disabled or
    /// declines. `candidates` is an independent ordered shortlist of four
    /// through eight binary columns. The selector runs
    /// only after the reframed native solver has prepared its ordinary root LP,
    /// so it reuses that target-objective basis instead of paying for a second
    /// root. It probes every candidate at the root, retains five, then selects
    /// the remaining columns only inside one worst-bound child at each stage.
    /// It never probes the complete 16-leaf prefix.
    ///
    /// Every probe bound is rigorous weak-duality arithmetic but remains
    /// ranking advice only. The selected columns merely replace the ordered
    /// inputs to the existing complete frontier; all pruning, replay, and
    /// verdict authority remain unchanged. An invalid shortlist, incomplete
    /// scan, memory refusal, or local/caller deadline returns to
    /// `fallback_prefix` as a whole. A completed probe with no finite safe bound
    /// remains the weakest possible (`-infinity`) advice, so mixed or
    /// all-missing numerical evidence backfills deterministically in caller
    /// order without acquiring proof authority. No partial scan is used.
    pub fn check_marked_margin_target_fsb_shared_binary_prefix(
        &mut self,
        fallback_prefix: &[Col; 4],
        candidates: &[Col],
        fsb_opts: &TargetFsbPrefixOpts,
    ) -> Result<Outcome, MilpError> {
        self.validate_shared_binary_prefix(fallback_prefix)?;
        let request = crate::bab::TargetFsbPrefixRequest::new(candidates, *fsb_opts);
        self.check_with_shared_binary_prefix(
            fallback_prefix,
            None,
            MarginMode::Required,
            Some(request),
        )
    }

    /// Solve a complete binary-prefix partition with proof-first parallel
    /// relaxation preparation.
    ///
    /// This explicit path omits the ordinary root cut, symmetry, and
    /// primal-heuristic suites. These are optional advice, while a fixed-prefix
    /// proof first needs literal coverage and time to adjudicate every region.
    /// It solves the root relaxation once, then gives canonical prefix ranks to
    /// `workers` owned `FloatLp` clones under the same absolute session
    /// deadline. Worker results are merged in rank order into the one native
    /// tree. A worker may close a region only with the ordinary
    /// interval-verified Farkas license; every other result remains advice for
    /// the serial proof engine.
    ///
    /// The global verdict is never assembled from partial worker verdicts. Any
    /// unresolved region remains open, so a deadline, spawn failure, panic, or
    /// non-authoritative float result yields the ordinary fail-closed
    /// `Unknown`/incumbent-only outcome. A complete infeasibility result still
    /// leaves only through the existing caller-frame tree-certificate
    /// finalization and independent replay gate.
    pub fn check_shared_binary_prefix_proof_first(
        &mut self,
        split_cols: &[Col],
        workers: NonZeroUsize,
    ) -> Result<Outcome, MilpError> {
        self.validate_shared_binary_prefix(split_cols)?;
        self.check_with_shared_binary_prefix(split_cols, Some(workers), MarginMode::Disabled, None)
    }

    fn validate_shared_binary_prefix(&self, split_cols: &[Col]) -> Result<(), MilpError> {
        const MAX_SHARED_PREFIX_COLS: usize = 4;
        if split_cols.is_empty() || split_cols.len() > MAX_SHARED_PREFIX_COLS {
            return Err(MilpError::Session {
                message: format!(
                    "shared binary prefix needs 1..={MAX_SHARED_PREFIX_COLS} columns, got {}",
                    split_cols.len()
                ),
            });
        }
        if !matches!(&self.lane, MilpLane::Native) {
            return Err(MilpError::Session {
                message: "shared binary prefix requires the native integral lane".to_owned(),
            });
        }
        if self.incumbent_seed.is_some() {
            return Err(MilpError::Session {
                message:
                    "shared binary prefix does not yet compose with an external incumbent seed"
                        .to_owned(),
            });
        }
        let mut seen = vec![false; self.model.num_cols()];
        for &col in split_cols {
            if col.index() >= self.model.num_cols() {
                return Err(MilpError::Session {
                    message: format!("shared-prefix column {} out of range", col.index()),
                });
            }
            if self.model.col_kind(col) != crate::model::ColKind::Binary
                || self.model.col_bounds(col) != (0.0, 1.0)
            {
                return Err(MilpError::Session {
                    message: format!(
                        "shared-prefix column {} is not a live binary with box [0, 1]",
                        col.index()
                    ),
                });
            }
            if std::mem::replace(&mut seen[col.index()], true) {
                return Err(MilpError::Session {
                    message: format!("shared-prefix column {} is duplicated", col.index()),
                });
            }
        }
        Ok(())
    }

    fn check_with_shared_binary_prefix(
        &mut self,
        shared_binary_prefix: &[Col],
        proof_first_workers: Option<NonZeroUsize>,
        margin_mode: MarginMode<'_>,
        target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
    ) -> Result<Outcome, MilpError> {
        let frame = FtAdoptionFrame::enter(self);
        frame.session.check_with_shared_binary_prefix_in_frame(
            shared_binary_prefix,
            proof_first_workers,
            margin_mode,
            target_fsb_prefix,
        )
    }

    /// THE ONE EXIT A DEFERRED CLAIM CANNOT ESCAPE.
    ///
    /// The routing prelude has twenty-odd `return Ok(out)` sites, and a claim
    /// parked by [`Self::admit_or_defer`] must be resolved on EVERY one of them,
    /// not just on the native path. Two things go wrong otherwise, and the
    /// second is the dangerous one:
    ///
    /// * a claim held when some later lane closes would survive into the NEXT
    ///   `check()` on this session and attach to a different model's verdict;
    /// * a later lane that CONTRADICTS the deferred claim would win silently,
    ///   which is exactly the "first recogniser wins" failure a portfolio is
    ///   uniquely able to see.
    ///
    /// Wrapping the body is what makes the resolution total. Rather than
    /// auditing every early return — the audit that has to be redone each time
    /// someone adds a lane — the claim is resolved HERE, once, on whatever the
    /// body returned.
    fn check_with_shared_binary_prefix_in_frame(
        &mut self,
        shared_binary_prefix: &[Col],
        proof_first_workers: Option<NonZeroUsize>,
        margin_mode: MarginMode<'_>,
        target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
    ) -> Result<Outcome, MilpError> {
        // A claim from a PREVIOUS check on this session is never live here.
        self.deferred_claim = None;
        self.last_deferred = None;
        // The same objective view the body builds, rebuilt here because the
        // body owns its copy. Identical construction, deliberately duplicated
        // rather than plumbed out of twenty return sites.
        let objective_for_exit: Vec<(u32, f64)> = (0..self.model.num_cols())
            .map(|i| (i as u32, self.model.obj_coeff(Col(i as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let exact_for_exit = authoritative_exact_objective(&self.model);
        let result = self.check_with_shared_binary_prefix_in_frame_inner(
            shared_binary_prefix,
            proof_first_workers,
            margin_mode,
            target_fsb_prefix,
        );
        let Ok(outcome) = result else {
            // An error path publishes nothing, so a held claim is simply
            // dropped rather than attached to a verdict that does not exist.
            self.deferred_claim = None;
            return result;
        };
        if self.deferred_claim.is_none() {
            return Ok(outcome);
        }
        let solved = SolvedObjective {
            coeffs: &objective_for_exit,
            sense: self.model.sense(),
            offset: self.model.objective_offset(),
            exact: exact_for_exit,
        };
        let out = self.publish_deferred_if_native_did_not_decide(outcome, &solved);
        // EXTEND, do not assign. Every early return inside the body has already
        // drained the ledger into `replay_claims`; resolving the deferred claim
        // then files ITS claims, and overwriting here would silently delete the
        // evidence the body had collected. Appending is the only correct join.
        self.replay_claims.extend(crate::cert_io::ledger::take());
        Ok(out)
    }

    fn check_with_shared_binary_prefix_in_frame_inner(
        &mut self,
        shared_binary_prefix: &[Col],
        proof_first_workers: Option<NonZeroUsize>,
        margin_mode: MarginMode<'_>,
        target_fsb_prefix: Option<crate::bab::TargetFsbPrefixRequest<'_>>,
    ) -> Result<Outcome, MilpError> {
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
        // Any claim left on this thread by an earlier solve is not this solve's
        // evidence. Drop it before starting rather than risk attributing it.
        let _ = crate::cert_io::ledger::take();
        self.invalidate_last_evidence();
        self.opts.deadline = self.opts.effective_deadline(started);
        self.opts.time_limit = None;
        let expired = |o: &SolveOpts| o.deadline.is_some_and(|d| Instant::now() >= d);

        let objective: Vec<(u32, f64)> = (0..self.model.num_cols())
            .map(|i| (i as u32, self.model.obj_coeff(Col(i as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let has_objective = self.model.has_objective();
        // TRUE rational objective for the re-derivation gate / exact rim,
        // materialized whenever the model has an authoritative side store.
        let exact_objective = authoritative_exact_objective(&self.model);

        // Some zero-objective verification MILPs are a mechanically compiled
        // SAT instance: clause ReLUs, one identity and one booleanization ReLU
        // per input, and two output rows that require every clause to hold and
        // every input to round to {0,1}.  Recovering that representation avoids
        // asking generic branch-and-bound to rediscover CDCL through millions
        // of LP boxes.  The recognizer is exact and fail-closed, and a SAT point
        // still leaves through `finish`, which independently checks every
        // original MILP row and bound.
        //
        // Refutations leave only through the model-bound `sat-relu-rup`
        // channel: the exact projection is rebuilt and its bounded RUP proof
        // independently replayed before the session can publish it.
        let ordinary_native_check = matches!(&self.lane, MilpLane::Native)
            && shared_binary_prefix.is_empty()
            && proof_first_workers.is_none()
            && target_fsb_prefix.is_none()
            && matches!(&margin_mode, MarginMode::Auto)
            // A MARKED MARGIN ROW IS AN OPT-IN PROOF STRATEGY, NOT A SHAPE.
            //
            // `MarginMode::Auto` is the default for every model, so gating on
            // it alone let the structure routes claim margin models too. That
            // returned before the margin dispatch, so `margin::reframe` was
            // never called, no nested session was created, and — the part that
            // matters — the margin lane's own evidence gate (it REFUSES to
            // report infeasible without a verified margin tree) was skipped
            // along with it. The lane was silently deleted on every model the
            // routes could settle.
            //
            // A caller that calls `Model::mark_margin_row` has named the proof
            // it wants, and that proof lands on `Outcome::Infeasible.tree_cert`
            // where `validate_witnesses` re-checks it — a better carrier than a
            // session side channel. Yield to it.
            && self.model.margin_row().is_none()
            && self.opts.structure_routing;

        // A NOTE ON THE PRELUDE TAX, AND ON A FIX THAT WAS TRIED AND REJECTED.
        //
        // The lattice device belongs to the ANCHOR — `SolveOpts::with_structure_routing(false)`
        // runs it at the top of `bab::structural_prologue` — and on the
        // market-split family it is the whole answer. Reaching it only through
        // branch-and-bound means the speculative prelude runs first, and on
        // `markshare_5_0` that costs a measured 7.5x:
        //
        // ```text
        //   default                        OPTIMAL 1 @ 1.13 s   3/3
        //   `SolveOpts::with_structure_routing(false)`   OPTIMAL 1 @ 0.15 s   3/3
        // ```
        //
        // (`pb_route::try_solve_production_portfolio` alone held 398 of 730
        // profile samples.) Same verdict, same evidence — pure prelude tax.
        //
        // TWO FIXES WERE TRIED HERE AND BOTH WERE WITHDRAWN, and recording why
        // is more useful than the code would have been:
        //
        // 1. Running `lattice::try_prove` at session level and returning its
        //    optimum directly. It restored the 0.15 s and SILENTLY DROPPED the
        //    postsolve certificate lift `bab::solve_milp_in` performs on the way
        //    out — `Optimal` with caller-frame evidence became
        //    `Unknown{CertificateUnavailable}` under `--require full`. A new exit
        //    path is a new place to lose evidence.
        //
        // 2. Skipping the speculative prelude whenever `lattice::recognises`
        //    matched. Its shape scan also matches small weighted-Boolean
        //    feasibility rows, so `6x + 10y + 14z = 18` over binaries — which
        //    the single-row DP route refutes with a SUCCINCT typed artifact —
        //    came back `evidence infeasible REPLAY feasibility-face-empty`
        //    instead. Narrowing the predicate to objective-bearing models did
        //    not save it.
        //
        // Both were the routing defect this file is being repaired FOR, wearing
        // a different hat: a recogniser deciding, on its own authority, that
        // another lane does not get to run. The tax is a BUDGET problem — the
        // prelude's lanes are handed slices sized from the caller's deadline
        // rather than from the model — and it should be fixed there, where the
        // repair cannot remove anyone's ability to publish a proof.
        // Both postures give the exact SAT/ReLU plan one proof-enabled CDCL
        // pass: SAT lifts through the private checked-point boundary, while
        // UNSAT binds the already replayed DAG to this model. If that bounded
        // path declines, either posture continues to established proof lanes.
        // Either posture may run ordinary CDCL once only when the caller has
        // explicitly disabled its memory envelope; that legacy engine has no
        // enforceable retained-memory limit of its own.
        let mut pending_sat_relu_fallback = None;
        if ordinary_native_check {
            if let Some(plan) = crate::sat_relu::prepare_with_memory_budget(
                &self.model,
                self.opts.deadline,
                self.opts.memory_budget,
            ) {
                let ordinary_fallback_allowed = self.opts.memory_budget.is_none();
                let proof_deadline =
                    sat_relu_proof_trial_deadline(self.opts.deadline, Instant::now());
                let sat_relu_frame = crate::claim::LaneFrame::enter();
                let proof_decision = proof_deadline.and_then(|deadline| {
                    plan.try_solve_with_proof(&self.model, Some(deadline), self.opts.memory_budget)
                });
                let proof_conclusive = match proof_decision {
                    Some(crate::sat_relu::SatReluProofDecision::Sat(checked)) => {
                        #[cfg(test)]
                        crate::sat_relu::test_wait_before_session_finish();
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective.clone(),
                        };
                        let outcome = finish_checked_sat_point(
                            checked,
                            has_objective,
                            &self.model,
                            &solved,
                            &self.opts,
                        );
                        let lane_claims = sat_relu_frame.take_lane_claims();
                        if let Some(out) = self.admit_or_defer(
                            &crate::claim::SAT_RELU_PROOF,
                            outcome,
                            &solved,
                            lane_claims,
                            Finisher::AlreadyFinished,
                        ) {
                            self.replay_claims = crate::cert_io::ledger::take();
                            return Ok(out);
                        }
                        true
                    }
                    Some(crate::sat_relu::SatReluProofDecision::Unsat(certificate)) => {
                        self.sat_relu_infeasibility_certificate = Some(certificate);
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective.clone(),
                        };
                        let outcome = Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        };
                        let outcome = finish_exact_reduction_with_supplemental_proof(
                            outcome,
                            &self.model,
                            &solved,
                            &self.opts,
                            SupplementalProof::VerifiedSatReluInfeasibility,
                        );
                        let lane_claims = sat_relu_frame.take_lane_claims();
                        if let Some(out) = self.admit_or_defer(
                            &crate::claim::SAT_RELU_PROOF,
                            outcome,
                            &solved,
                            lane_claims,
                            Finisher::AlreadyFinished,
                        ) {
                            self.replay_claims = crate::cert_io::ledger::take();
                            return Ok(out);
                        }
                        true
                    }
                    None if ordinary_fallback_allowed => {
                        // The bounded proof path can decline on its local
                        // deadline/codec envelope. Retain the recognized plan,
                        // but do not solve it yet: certified routes get first
                        // refusal and the ordinary fallback runs at most once
                        // at its claim-lattice position below.
                        drop(sat_relu_frame);
                        false
                    }
                    None => {
                        drop(sat_relu_frame);
                        false
                    }
                };

                if !proof_conclusive && ordinary_fallback_allowed {
                    pending_sat_relu_fallback = Some(plan);
                }
            }
        }

        // The GF(2) route historically lived only inside `bab::solve_milp`.
        // That is too late for a session: one of the proof-exporting exact
        // routes below may return before branch-and-bound is entered, leaving
        // a valid parity contradiction with no parity artifact attached to the
        // session. Give the narrowly recognized family first refusal here,
        // then independently replay its source-row contradiction before it is
        // allowed to satisfy the full-evidence policy.
        //
        // A parity optimum is intentionally different. GF(2) enumeration is
        // an exact internal proof, but it does not yet export a typed
        // optimality artifact. In `require full` posture retain its exact point
        // only as an incumbent seed and continue to a proof-producing route;
        // never let the infeasibility side artifact certify an optimum.
        if ordinary_native_check {
            if let Some(parity_outcome) = crate::parity::try_solve(&self.model, self.opts.deadline)
            {
                let parity_certificate = crate::parity::take_pending_infeasibility_certificate();
                match parity_outcome {
                    outcome @ Outcome::Infeasible { .. } => {
                        if let Some(certificate) = parity_certificate.filter(|certificate| {
                            crate::verify_parity_infeasibility_certificate(&self.model, certificate)
                                .is_ok()
                        }) {
                            self.parity_infeasibility_certificate = Some(certificate);
                            let solved = SolvedObjective {
                                coeffs: &objective,
                                sense: self.model.sense(),
                                offset: self.model.objective_offset(),
                                exact: exact_objective,
                            };
                            let out = finish_exact_reduction_with_supplemental_proof(
                                outcome,
                                &self.model,
                                &solved,
                                &self.opts,
                                SupplementalProof::VerifiedParityInfeasibility,
                            );
                            self.replay_claims = crate::cert_io::ledger::take();
                            return Ok(out);
                        }
                        // Missing or malformed side evidence cannot authorize
                        // an early infeasibility verdict. Fall through to the
                        // ordinary independently certified routes.
                    }
                    Outcome::Optimal { model_values, .. } if self.opts.require_certificates => {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                    }
                    Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        ..
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                    }
                    outcome => {
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let out = finish_exact_reduction(outcome, &self.model, &solved, &self.opts);
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
            }
        }

        // Complete disjunctive single-machine scheduling formulations are
        // solved by an exact subset/Pareto DP. Recognition consumes every
        // source row and column, reconstruction is checked against the source
        // model, and this posture independently replays the typed model-bound
        // artifact before it may certify optimality. A structural, resource,
        // deadline, or source-witness miss falls through unchanged.
        if ordinary_native_check {
            if let Some(scheduling) =
                crate::scheduling_route::try_solve_certified(&self.model, self.opts.deadline)
            {
                let crate::scheduling_route::SingleMachineSchedulingDecision::Optimal {
                    value,
                    model_values,
                    certificate,
                } = scheduling;
                self.single_machine_scheduling_optimality_certificate = Some(certificate);
                let solved = SolvedObjective {
                    coeffs: &objective,
                    sense: self.model.sense(),
                    offset: self.model.objective_offset(),
                    exact: exact_objective,
                };
                let outcome = Outcome::Optimal {
                    value,
                    model_values,
                    cert: None,
                };
                let out = finish_exact_reduction_with_supplemental_proof(
                    outcome,
                    &self.model,
                    &solved,
                    &self.opts,
                    SupplementalProof::VerifiedSingleMachineSchedulingOptimality,
                );
                self.replay_claims = crate::cert_io::ledger::take();
                return Ok(out);
            }
        }

        // PROOF-EXPORTING ROUTES RUN IN BOTH POSTURES AFTER THE BOUNDED
        // SAT/RELU PROOF ROUTE HAS DECLINED.
        //
        // Every lane below exports a typed artifact that is independently
        // replayed against a freshly rebuilt projection of THIS source model
        // before the verdict is returned, and is published on the session's
        // typed accessors.  Gating that on `require_certificates` was a
        // measured evidence DOWNGRADE: the CLI ships `--require witness`, so
        // the default posture fell through to the REPLAY-only lanes below
        // (`sat-relu-cnf-unsat`, `direct-cnf-unsat`, `pb-projection-*`) and a
        // model that could be refuted by a succinct, third-party-checkable
        // proof emitted an unbacked replay claim instead —
        // `ay-milp verify` exit 10 under the default and exit 0 under
        // `--require full` on the SAME model.
        //
        // The exact SAT/ReLU route above participates in both postures and
        // returns its checked SAT point or model-bound UNSAT artifact directly.
        // Only a bounded proof miss reaches this point. A recognized plan from
        // a caller without an explicit memory envelope is retained, but its
        // ordinary-CDCL fallback waits until every typed route below has had
        // first refusal; budgeted postures never enter that unmetered engine.
        // Every other REPLAY-only route remains behind the sealed lanes, so a
        // generic model that can export a succinct proof still does so.
        // Feasible/optimal answers and bare exhaustion otherwise stay on the
        // native proof-producing path.
        if ordinary_native_check {
            // The network route has its own model-bound artifact boundary: it
            // rebuilds the eager Hoffman projection and independently replays
            // either the empty master or the strict-better objective face.
            // A proof-export miss carries a one-shot continuation: a checked
            // conclusive raw result, or exactly the distinct lazy Benders arm.
            // It never authorizes the eager/symmetry/PB work to run twice.
            let network_attempt_started = Instant::now();
            let network_attempt = crate::network_design_route::try_solve_certified_attempt(
                &self.model,
                self.opts.deadline,
            );
            if structure_trace_enabled() {
                eprintln!(
                    "--trace network-design-attempt t={:.6}s applicable={}",
                    network_attempt_started.elapsed().as_secs_f64(),
                    !matches!(
                        network_attempt,
                        crate::network_design_route::CertifiedNetworkDesignAttempt::NotApplicable
                    ),
                );
            }
            let certified_network = match network_attempt {
                crate::network_design_route::CertifiedNetworkDesignAttempt::NotApplicable => None,
                crate::network_design_route::CertifiedNetworkDesignAttempt::Decided(decision) => {
                    Some(decision)
                }
                crate::network_design_route::CertifiedNetworkDesignAttempt::ReadyReplay(
                    decision,
                ) => {
                    self.install_network_design_replay_handoff(
                        NetworkDesignReplayHandoff::ReadyReplay(decision),
                    );
                    None
                }
                crate::network_design_route::CertifiedNetworkDesignAttempt::LazyOnly(incumbent) => {
                    self.install_network_design_replay_handoff(
                        NetworkDesignReplayHandoff::LazyOnly(incumbent),
                    );
                    None
                }
            };
            if let Some(network) = certified_network {
                match network {
                    crate::network_design_route::CertifiedNetworkDesignDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        self.install_network_design_replay_handoff(
                            NetworkDesignReplayHandoff::LazyOnly(Some(
                                crate::pb_route::PbRouteDecision::Feasible {
                                    model_values,
                                    incumbent_only,
                                },
                            )),
                        );
                    }
                    crate::network_design_route::CertifiedNetworkDesignDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } => {
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let outcome = Outcome::Feasible {
                            model_values,
                            incumbent_only,
                            dual_bound: None,
                        };
                        let out = finish_exact_reduction(outcome, &self.model, &solved, &self.opts);
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                    crate::network_design_route::CertifiedNetworkDesignDecision::Infeasible(
                        certificate,
                    ) => {
                        self.network_design_infeasibility_certificate = Some(certificate);
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let outcome = Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        };
                        let out = finish_exact_reduction_with_supplemental_proof(
                            outcome,
                            &self.model,
                            &solved,
                            &self.opts,
                            SupplementalProof::VerifiedNetworkDesignInfeasibility,
                        );
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                    crate::network_design_route::CertifiedNetworkDesignDecision::Optimal {
                        value,
                        model_values,
                        certificate,
                    } => {
                        self.network_design_optimality_certificate = Some(certificate);
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let outcome = Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        };
                        let out = finish_exact_reduction_with_supplemental_proof(
                            outcome,
                            &self.model,
                            &solved,
                            &self.opts,
                            SupplementalProof::VerifiedNetworkDesignOptimality,
                        );
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
            }

            // Integral conservation chains coupled only by covering rows
            // admit an exact Dantzig--Wolfe decomposition. Give that typed
            // route first refusal after network design, but only behind its
            // advice-only matrix scout. This avoids repeatedly radix-lifting
            // matching general-integer models through the generic PB lanes;
            // an exact recognition or proof miss still falls through under
            // the same caller deadline. Network design remains ahead of this
            // broader recognizer, preserving rout's specialized path.
            if self.may_offer_block_angular_before_network_replay()
                && crate::block_angular_route::is_coarse_block_angular_candidate(&self.model)
            {
                let block_angular_frame = crate::claim::LaneFrame::enter();
                let block_angular = crate::block_angular_route::try_solve_certified(
                    &self.model,
                    self.opts.deadline,
                    self.opts.memory_budget,
                );
                if let Some(block_angular) = block_angular {
                    let crate::block_angular_route::BlockAngularDecision {
                        value,
                        model_values,
                        certificate,
                    } = block_angular;
                    self.block_angular_optimality_certificate = Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective.clone(),
                    };
                    let outcome = Outcome::Optimal {
                        value,
                        model_values,
                        cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedBlockAngularOptimality,
                    );
                    let lane_claims = block_angular_frame.take_lane_claims();
                    if let Some(out) = self.admit_or_defer(
                        &crate::claim::BLOCK_ANGULAR,
                        out,
                        &solved,
                        lane_claims,
                        Finisher::AlreadyFinished,
                    ) {
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                } else {
                    drop(block_angular_frame);
                }
            }

            let proof_deadline = pb_portfolio_trial_deadline(self.opts.deadline, Instant::now());
            let infeasibility_probe_started = Instant::now();
            let single_row = proof_deadline.and_then(|trial_deadline| {
                crate::pb_route::try_prove_single_row_infeasibility(&self.model, trial_deadline)
            });
            if structure_trace_enabled() {
                eprintln!(
                    "--trace infeasibility-probe single_row={:.6}s hit={}",
                    infeasibility_probe_started.elapsed().as_secs_f64(),
                    single_row.is_some(),
                );
            }
            if let Some(crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible {
                certificate,
            }) = single_row
            {
                self.single_row_dp_infeasibility_certificate = Some(certificate);
                let solved = SolvedObjective {
                    coeffs: &objective,
                    sense: self.model.sense(),
                    offset: self.model.objective_offset(),
                    exact: exact_objective,
                };
                let outcome = Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                };
                let out = finish_exact_reduction_with_supplemental_proof(
                    outcome,
                    &self.model,
                    &solved,
                    &self.opts,
                    SupplementalProof::VerifiedSingleRowDpInfeasibility,
                );
                self.replay_claims = crate::cert_io::ledger::take();
                return Ok(out);
            }

            // The single-row probe just declined this model; its cost is the
            // model-derived unit that bounds the heavier BDD arm. See
            // `probe_scaled_deadline`.
            let single_row_cost = infeasibility_probe_started.elapsed();
            let multi_row_started = Instant::now();
            let multi_row = probe_scaled_deadline(
                single_row_cost,
                proof_deadline,
                multi_row_started,
            )
            .and_then(|trial_deadline| {
                crate::pb_route::try_prove_multi_row_infeasibility(&self.model, trial_deadline)
            });
            if structure_trace_enabled() {
                eprintln!(
                    "--trace infeasibility-probe multi_row={:.6}s hit={}",
                    multi_row_started.elapsed().as_secs_f64(),
                    multi_row.is_some(),
                );
            }
            if let Some(crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible {
                certificate,
            }) = multi_row
            {
                self.multi_row_bdd_infeasibility_certificate = Some(certificate);
                let solved = SolvedObjective {
                    coeffs: &objective,
                    sense: self.model.sense(),
                    offset: self.model.objective_offset(),
                    exact: exact_objective,
                };
                let outcome = Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                };
                let out = finish_exact_reduction_with_supplemental_proof(
                    outcome,
                    &self.model,
                    &solved,
                    &self.opts,
                    SupplementalProof::VerifiedMultiRowBddInfeasibility,
                );
                self.replay_claims = crate::cert_io::ledger::take();
                return Ok(out);
            }

            let open_domain_started = Instant::now();
            let open_domain = proof_deadline.and_then(|trial_deadline| {
                crate::open_domain_route::try_prove_infeasibility(&self.model, trial_deadline)
            });
            if structure_trace_enabled() {
                eprintln!(
                    "--trace infeasibility-probe open_domain={:.6}s hit={}",
                    open_domain_started.elapsed().as_secs_f64(),
                    open_domain.is_some(),
                );
            }
            match open_domain {
                Some(
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedSingleRowInfeasible {
                        certificate,
                    },
                ) => {
                    self.open_domain_single_row_dp_infeasibility_certificate = Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedOpenDomainSingleRowDpInfeasibility,
                    );
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
                Some(
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedMultiRowInfeasible {
                        certificate,
                    },
                ) => {
                    self.open_domain_multi_row_bdd_infeasibility_certificate = Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedOpenDomainMultiRowBddInfeasibility,
                    );
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
                Some(
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridPbLpInfeasible {
                        certificate,
                    },
                ) => {
                    self.open_domain_hybrid_pb_lp_infeasibility_certificate = Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedOpenDomainHybridPbLpInfeasibility,
                    );
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
                Some(
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridIntegerLiftInfeasible {
                        certificate,
                    },
                ) => {
                    self.open_domain_hybrid_integer_lift_infeasibility_certificate =
                        Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedOpenDomainHybridIntegerLiftInfeasibility,
                    );
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
                _ => {}
            }

            // Same unit as the BDD arm above: the cheap single-row structural
            // pass already declined this model. See `probe_scaled_deadline`.
            let direct_hybrid_started = Instant::now();
            let direct_hybrid =
                probe_scaled_deadline(single_row_cost, proof_deadline, direct_hybrid_started)
                    .and_then(|trial_deadline| {
                        crate::hybrid_pb_lp::try_solve_certified(&self.model, Some(trial_deadline))
                    });
            if structure_trace_enabled() {
                eprintln!(
                    "--trace infeasibility-probe hybrid_pb_lp={:.6}s hit={}",
                    direct_hybrid_started.elapsed().as_secs_f64(),
                    direct_hybrid.is_some(),
                );
            }
            match direct_hybrid {
                Some(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(certificate)) => {
                    self.hybrid_pb_lp_infeasibility_certificate = Some(certificate);
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    let out = finish_exact_reduction_with_supplemental_proof(
                        outcome,
                        &self.model,
                        &solved,
                        &self.opts,
                        SupplementalProof::VerifiedHybridPbLpInfeasibility,
                    );
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
                Some(_) => {}
                None => {
                    let lifted_hybrid_started = Instant::now();
                    let lifted_hybrid = probe_scaled_deadline(
                        single_row_cost,
                        proof_deadline,
                        lifted_hybrid_started,
                    )
                    .and_then(|trial_deadline| {
                        crate::hybrid_integer_lift::try_solve_certified(
                            &self.model,
                            Some(trial_deadline),
                        )
                    });
                    if let Some(
                        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(
                            certificate,
                        ),
                    ) = lifted_hybrid
                    {
                        self.hybrid_integer_lift_infeasibility_certificate = Some(certificate);
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let outcome = Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        };
                        let out = finish_exact_reduction_with_supplemental_proof(
                            outcome,
                            &self.model,
                            &solved,
                            &self.opts,
                            SupplementalProof::VerifiedHybridIntegerLiftInfeasibility,
                        );
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
            }
        }
        // POSTURE IS A FILTER ON EVIDENCE, NOT A SWITCH ON WORK.
        //
        // This block used to read `&& !self.opts.require_certificates`, and
        // that one conjunct WAS the posture inversion. `--require full` skipped
        // the whole block and fell through to the proof-producing tree, while
        // the shipped default (`--require witness`) ran it and took the REPLAY.
        // The strict mode therefore got the succinct proof and the DEFAULT got
        // the weak one. MEASURED on `W1_unsat_v9_c14_000008` before this change:
        //
        // ```text
        //   --require none      INFEASIBLE     758 bytes   verify exit 10
        //   --require witness   INFEASIBLE     758 bytes   verify exit 10   <- the default
        //   --require full      INFEASIBLE  19,664 bytes   verify exit  0
        // ```
        //
        // The CLI's own documentation already called `--require` a "post-hoc
        // verdict FILTER, not a work switch"; the code disagreed. With the
        // conjunct gone every posture sees the same candidate set and
        // `apply_cert_policy` filters the winner, so a weaker posture can never
        // produce a weaker result — non-inversion by construction rather than
        // by policy. `posture_never_inverts_the_evidence_it_admits` pins it.
        //
        // What replaces the conjunct is the EVIDENCE FLOOR: a lane may end the
        // solve only when `claim::may_close` finds its evidence for the claim it
        // is making at least as strong as anything the anchor could still have
        // attached. That test is posture-independent, so deleting the conjunct
        // does not hand the REPLAY lanes the models they were wrongly taking —
        // it moves the decision from "which posture is this?" to "is this
        // evidence good enough?", which is the question that was never asked.
        if let Some(plan) = pending_sat_relu_fallback.take() {
            // The proof-producing pass declined, and every earlier exact proof
            // route got first refusal. Ordinary CDCL now runs once from the
            // retained plan. Both its checked SAT point and replay-only UNSAT
            // still pass through the claim lattice before they may publish.
            crate::sat_relu::trace_ordinary_fallback();
            let sat_relu_frame = crate::claim::LaneFrame::enter();
            match plan.solve(&self.model, self.opts.deadline) {
                Some(crate::sat_relu::SatReluDecision::Sat(checked)) => {
                    #[cfg(test)]
                    crate::sat_relu::test_wait_before_session_finish();
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective.clone(),
                    };
                    let outcome = finish_checked_sat_point(
                        checked,
                        has_objective,
                        &self.model,
                        &solved,
                        &self.opts,
                    );
                    let lane_claims = sat_relu_frame.take_lane_claims();
                    if let Some(out) = self.admit_or_defer(
                        &crate::claim::SAT_RELU_FALLBACK,
                        outcome,
                        &solved,
                        lane_claims,
                        Finisher::AlreadyFinished,
                    ) {
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
                Some(crate::sat_relu::SatReluDecision::Unsat) => {
                    crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                        claim: "sat-relu-cnf-unsat".to_owned(),
                        device: "sat-relu-reduction".to_owned(),
                        method: "exact-structural-recovery+cdcl".to_owned(),
                        arithmetic: "exact-dyadic+rational-rounding".to_owned(),
                        nodes_visited: None,
                        node_budget: 0,
                        outcome: "exhausted".to_owned(),
                        nondeterminism: Vec::new(),
                        reproduce: "ay-milp solve <model> --require none".to_owned(),
                        tcb: "ay-milp/src/sat_relu.rs+ay-milp/src/sat_route.rs+ay-sat".to_owned(),
                    });
                    let lane_claims = sat_relu_frame.take_lane_claims();
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        // A deferred fallback continues through every later
                        // route and into the native anchor, so its exact
                        // objective must survive.
                        exact: exact_objective.clone(),
                    };
                    let outcome = Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    };
                    if let Some(out) = self.admit_or_defer(
                        &crate::claim::SAT_RELU_FALLBACK,
                        outcome,
                        &solved,
                        lane_claims,
                        Finisher::ExactReduction,
                    ) {
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
                None => drop(sat_relu_frame),
            }
        }
        if ordinary_native_check {
            // General semantic clause-MILP route. Unlike `sat_relu`, this is
            // independent of a compiler layout: every exact finite row side is
            // admitted only when it is a scaled Boolean clause (or a Boolean
            // tautology/contradiction), and fixed 0/1 domains become units.
            let direct_cnf_frame = crate::claim::LaneFrame::enter();
            let direct_cnf_decision = crate::direct_cnf::try_solve(&self.model, self.opts.deadline);
            if let Some(decision) = direct_cnf_decision {
                let outcome = match decision {
                    crate::sat_route::SatDecision::Sat(checked) => {
                        let solved = SolvedObjective {
                            coeffs: &objective,
                            sense: self.model.sense(),
                            offset: self.model.objective_offset(),
                            exact: exact_objective,
                        };
                        let out = finish_checked_sat_point(
                            checked,
                            has_objective,
                            &self.model,
                            &solved,
                            &self.opts,
                        );
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                    crate::sat_route::SatDecision::Unsat => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "direct-cnf-unsat".to_owned(),
                            device: "direct-cnf-reduction".to_owned(),
                            method: "exact-boolean-row-recovery+cdcl".to_owned(),
                            arithmetic: "exact-rational".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/direct_cnf.rs+ay-milp/src/sat_route.rs+ay-sat"
                                .to_owned(),
                        });
                        Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        }
                    }
                };
                let lane_claims = direct_cnf_frame.take_lane_claims();
                let solved = SolvedObjective {
                    coeffs: &objective,
                    sense: self.model.sense(),
                    offset: self.model.objective_offset(),
                    // Cloned for the same reason as the `sat_relu` arm above.
                    exact: exact_objective.clone(),
                };
                if let Some(out) = self.admit_or_defer(
                    &crate::claim::DIRECT_CNF,
                    outcome,
                    &solved,
                    lane_claims,
                    Finisher::ExactReduction,
                ) {
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
            } else {
                drop(direct_cnf_frame);
            }

            // Small capacitated network blocks can be eliminated exactly from
            // fixed-charge formulations.  The recognizer emits the complete
            // Hoffman projection onto a bounded-integral master; a bounded PB
            // trial proves that master, and every surviving master point is
            // completed by exact rational max-flow and checked against this
            // original model.  Non-network models take only the cheap
            // column-shape decline.  A PB/resource/deadline decline preserves
            // most of the outer budget for native MILP search.
            let network_decision = match self.take_pending_network_design_replay() {
                Some(NetworkDesignReplayHandoff::ReadyReplay(decision)) => Some(decision),
                Some(NetworkDesignReplayHandoff::LazyOnly(incumbent)) => {
                    crate::network_design_route::try_solve_lazy_only(
                        &self.model,
                        self.opts.deadline,
                        incumbent,
                    )
                }
                None => crate::network_design_route::try_solve(&self.model, self.opts.deadline),
            };
            if let Some(decision) = network_decision {
                let outcome = match decision {
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        None
                    }
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } => Some(Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        dual_bound: None,
                    }),
                    // DELIBERATELY NOT PUBLISHED as a typed artifact. This PB
                    // residual is a refutation of the network-design MASTER,
                    // not of a projection of this model, so
                    // `verify_*_infeasibility_certificate_with_deadline(&self.model, ..)`
                    // would refute it. Publishing it would turn an honest
                    // REPLAY claim into a SUCCINCT claim our own `.ayc` checker
                    // rejects. The network lane's own model-bound artifact is
                    // the `network_design_*_certificate` pair, produced by
                    // `network_design_route::try_solve_certified` above.
                    crate::pb_route::PbRouteDecision::Infeasible
                    | crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                    | crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible { .. } => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "network-design-projection-infeasible".to_owned(),
                            device: "hoffman-network-pb-projection".to_owned(),
                            method: "exact-hoffman-projection+bounded-pb-exhaustion".to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/presolve.rs+\
                                  ay-milp/src/network_design_pb.rs+\
                                  ay-milp/src/network_design_route.rs+\
                                  ay-milp/src/pb_translate.rs+ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::Optimal {
                        value,
                        model_values,
                    } => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "network-design-projection-optimal".to_owned(),
                            device: "hoffman-network-pb-projection".to_owned(),
                            method: "exact-hoffman-projection+bounded-pb-exhaustion+\
                                     rational-transshipment"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/presolve.rs+\
                                  ay-milp/src/network_design_pb.rs+\
                                  ay-milp/src/network_design_route.rs+\
                                  ay-milp/src/pb_translate.rs+ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        })
                    }
                };
                if let Some(outcome) = outcome {
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let out = finish_exact_reduction(outcome, &self.model, &solved, &self.opts);
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
            }

            // Bounded exact single-row pseudo-Boolean specialization. Unlike
            // Direct-CNF, this accepts arbitrary exact rational weights and
            // objectives over integral domains contained in {0,1}. The
            // translator proves the PB projection exactly (including both
            // sides of a range row and max/objective-offset mapping), the DP
            // independently repeats negative/optimal passes, and the adapter
            // re-checks every returned point and objective against this model.
            // A structural/resource decline returns here immediately: generic
            // raw PB-CDCL is trial-only and cannot consume the production
            // solve's remaining deadline. As above, certificate-required
            // solves stay on the case-split tree until this exhaustion proof
            // has an exportable model-bound certificate format.
            if let Some(decision) =
                crate::pb_route::try_solve_specialized(&self.model, self.opts.deadline)
            {
                let outcome = match decision {
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        // An anytime PB incumbent is useful advice, but it is not
                        // authority to stop an optimization solve.  Preserve a
                        // caller-supplied seed; otherwise hand the independently
                        // checked PB point to native branch-and-bound and keep
                        // proving under the same absolute deadline.  The native
                        // seeded entry point rechecks the floating representation
                        // before using it, so an inexact/unrepresentable lift can
                        // only be ignored.
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        None
                    }
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } => Some(Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        dual_bound: None,
                    }),
                    crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible {
                        certificate,
                    } => {
                        self.single_row_dp_infeasibility_certificate = Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible {
                        certificate,
                    } => {
                        self.multi_row_bdd_infeasibility_certificate = Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::Infeasible => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "pb-projection-infeasible".to_owned(),
                            device: "milp-to-pb-reduction".to_owned(),
                            method: "exact-rational-boolean-projection+redundant-single-row-dp"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/pb_translate.rs+ay-milp/src/pb_route.rs+\
                                  ay-pb-core/src/single_row_dp.rs"
                                .to_owned(),
                        });
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::Optimal {
                        value,
                        model_values,
                    } => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "pb-projection-optimal".to_owned(),
                            device: "milp-to-pb-reduction".to_owned(),
                            method: "exact-rational-boolean-projection+redundant-single-row-dp"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/pb_translate.rs+ay-milp/src/pb_route.rs+\
                                  ay-pb-core/src/single_row_dp.rs"
                                .to_owned(),
                        });
                        Some(Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        })
                    }
                };
                if let Some(outcome) = outcome {
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let out = finish_exact_reduction(outcome, &self.model, &solved, &self.opts);
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
            }

            // Compact multi-row bounded-integer models (and exact continuous
            // objective singletons eliminated by `pb_translate`) get a bounded
            // trial in AY's complete PB portfolio.  Exact translation owns the
            // structural budget decision: the small dense Boolean optimization
            // class receives a proof-sized slice, while every other translation
            // keeps the historical short generic trial.  A decline or timeout
            // always returns to native branch-and-bound under the same outer
            // deadline.
            let pb_portfolio_workers = (!self.opts.determinism)
                .then(|| NonZeroUsize::new(self.opts.threads as usize))
                .flatten()
                .filter(|workers| workers.get() > 1);
            let pb_portfolio_decision = crate::pb_route::try_solve_production_portfolio(
                &self.model,
                self.opts.deadline,
                pb_portfolio_workers,
            );
            if let Some(decision) = pb_portfolio_decision {
                let outcome = match decision {
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        None
                    }
                    crate::pb_route::PbRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } => Some(Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        dual_bound: None,
                    }),
                    crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible {
                        certificate,
                    } => {
                        self.multi_row_bdd_infeasibility_certificate = Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    // A typed single-row refutation is evidence; folding it into
                    // the bare arm below traded a succinct, replayable artifact
                    // for an unbacked replay string. Publish it exactly as the
                    // specialized route does.
                    crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible {
                        certificate,
                    } => {
                        self.single_row_dp_infeasibility_certificate = Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::Infeasible => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "pb-portfolio-projection-infeasible".to_owned(),
                            device: "bounded-milp-to-pb-portfolio".to_owned(),
                            method: "exact-rational-bounded-integer-projection+pb-exhaustion"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/pb_translate.rs+ay-milp/src/pb_route.rs+\
                                  ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::pb_route::PbRouteDecision::Optimal {
                        value,
                        model_values,
                    } => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "pb-portfolio-projection-optimal".to_owned(),
                            device: "bounded-milp-to-pb-portfolio".to_owned(),
                            method: "exact-rational-bounded-integer-projection+pb-exhaustion"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/pb_translate.rs+ay-milp/src/pb_route.rs+\
                                  ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        })
                    }
                };
                if let Some(outcome) = outcome {
                    // THROUGH THE EVIDENCE FLOOR, like every other verdict-ending
                    // lane. The portfolio's OPTIMALITY is an exhaustion argument
                    // over its own projection, not an exported object — and on a
                    // model with a real objective the anchor can lift a checkable
                    // `OptimalityCertificate`, so the portfolio must not preempt
                    // it. See `claim::PB_PORTFOLIO`.
                    let lane_claims = crate::cert_io::ledger::take();
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective.clone(),
                    };
                    if let Some(out) = self.admit_or_defer(
                        &crate::claim::PB_PORTFOLIO,
                        outcome,
                        &solved,
                        lane_claims,
                        Finisher::ExactReduction,
                    ) {
                        self.replay_claims = crate::cert_io::ledger::take();
                        return Ok(out);
                    }
                }
            }

            // Structurally open integer domains cannot enter the bounded PB
            // routes above directly.  The open-domain adapter first removes
            // only monotone existential columns, then (for optimization) uses
            // the independently checked lifted point to build an inclusive,
            // finite objective cap.  Both transformations are rebuilt against
            // this exact source model before a verdict is promoted.  A typed
            // residual refutation remains succinct because its checker rebuilds
            // this projection; only a backend that cannot export one falls back
            // to replay evidence.
            if let Some(decision) =
                crate::open_domain_route::try_solve(&self.model, self.opts.deadline)
            {
                let outcome = match decision {
                    crate::open_domain_route::OpenDomainRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        None
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::Feasible {
                        model_values,
                        incumbent_only,
                    } => Some(Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        dual_bound: None,
                    }),
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedSingleRowInfeasible {
                        certificate,
                    } => {
                        self.open_domain_single_row_dp_infeasibility_certificate =
                            Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedMultiRowInfeasible {
                        certificate,
                    } => {
                        self.open_domain_multi_row_bdd_infeasibility_certificate =
                            Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridPbLpInfeasible {
                        certificate,
                    } => {
                        self.open_domain_hybrid_pb_lp_infeasibility_certificate =
                            Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridIntegerLiftInfeasible {
                        certificate,
                    } => {
                        self.open_domain_hybrid_integer_lift_infeasibility_certificate =
                            Some(certificate);
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::Infeasible => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "open-domain-projection-infeasible".to_owned(),
                            device: "monotone-open-domain-projection".to_owned(),
                            method: "exact-monotone-projection+bounded-exact-exhaustion".to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/open_domain.rs+\
                                  ay-milp/src/open_domain_route.rs+\
                                  ay-milp/src/pb_translate.rs+ay-milp/src/hybrid_pb_lp.rs+\
                                  ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    crate::open_domain_route::OpenDomainRouteDecision::Optimal {
                        value,
                        model_values,
                    } => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "open-domain-cap-optimal".to_owned(),
                            device: "bounded-open-domain-objective-cap".to_owned(),
                            method: "exact-monotone-projection+inclusive-objective-cap+\
                                     bounded-exact-optimization"
                                .to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/open_domain.rs+\
                                  ay-milp/src/open_domain_route.rs+\
                                  ay-milp/src/pb_translate.rs+ay-milp/src/hybrid_pb_lp.rs+\
                                  ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        })
                    }
                };
                if let Some(outcome) = outcome {
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let out = finish_exact_reduction(outcome, &self.model, &solved, &self.opts);
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
            }

            // Experimental mixed bounded-integer/continuous route, explicitly
            // armed for controlled A/Bs only. General-integer master columns
            // first receive an exact finite radix lift; the resulting compact
            // PB master is coupled to continuous LP subproblems. Exact Farkas
            // combinations project valid Benders rows (or license one-assignment
            // no-goods) back to the master. The trial deadline above reserves the
            // native path after a decline. Infeasibility is adopted only with the
            // typed cut-ledger/refutation artifact; an optimality result remains
            // replay evidence because this route does not export a matching dual
            // optimum proof.
            let hybrid_enabled =
                crate::tune::caller_flag(crate::tune::Knob::HybridPbLp) == Some(true);
            enum HybridCertifiedDecision {
                Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision),
                IntegerLift(crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision),
            }
            let hybrid_decision =
                hybrid_pb_lp_trial_deadline(hybrid_enabled, self.opts.deadline, Instant::now())
                    .and_then(|trial_deadline| {
                        crate::hybrid_pb_lp::try_solve_certified(&self.model, Some(trial_deadline))
                            .map(HybridCertifiedDecision::Direct)
                            .or_else(|| {
                                crate::hybrid_integer_lift::try_solve_certified(
                                    &self.model,
                                    Some(trial_deadline),
                                )
                                .map(HybridCertifiedDecision::IntegerLift)
                            })
                    });
            if let Some(decision) = hybrid_decision {
                let mut supplemental_proof = SupplementalProof::None;
                let outcome = match decision {
                    HybridCertifiedDecision::Direct(
                        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible {
                            model_values,
                            incumbent_only,
                        },
                    )
                    | HybridCertifiedDecision::IntegerLift(
                        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
                            model_values,
                            incumbent_only,
                        },
                    ) if exact_reduction_feasible_must_continue_native(
                        has_objective,
                        incumbent_only,
                    ) =>
                    {
                        if self.incumbent_seed.is_none() {
                            self.incumbent_seed = exact_point_to_f64_seed(&model_values);
                        }
                        None
                    }
                    HybridCertifiedDecision::Direct(
                        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible {
                            model_values,
                            incumbent_only,
                        },
                    )
                    | HybridCertifiedDecision::IntegerLift(
                        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
                            model_values,
                            incumbent_only,
                        },
                    ) => Some(Outcome::Feasible {
                        model_values,
                        incumbent_only,
                        dual_bound: None,
                    }),
                    HybridCertifiedDecision::Direct(
                        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(certificate),
                    ) => {
                        self.hybrid_pb_lp_infeasibility_certificate = Some(certificate);
                        supplemental_proof = SupplementalProof::VerifiedHybridPbLpInfeasibility;
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    HybridCertifiedDecision::IntegerLift(
                        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(
                            certificate,
                        ),
                    ) => {
                        self.hybrid_integer_lift_infeasibility_certificate = Some(certificate);
                        supplemental_proof =
                            SupplementalProof::VerifiedHybridIntegerLiftInfeasibility;
                        Some(Outcome::Infeasible {
                            cert: None,
                            tree_cert: None,
                        })
                    }
                    HybridCertifiedDecision::Direct(
                        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Optimal {
                            value,
                            model_values,
                        },
                    )
                    | HybridCertifiedDecision::IntegerLift(
                        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Optimal {
                            value,
                            model_values,
                        },
                    ) => {
                        crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
                            claim: "hybrid-pb-lp-optimal".to_owned(),
                            device: "binary-master-continuous-lp".to_owned(),
                            method: "exact-pb-master+farkas-benders".to_owned(),
                            arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
                            nodes_visited: None,
                            node_budget: 0,
                            outcome: "exhausted".to_owned(),
                            nondeterminism: Vec::new(),
                            reproduce: "ay-milp solve <model> --require none".to_owned(),
                            tcb: "ay-milp/src/hybrid_integer_lift.rs+\
                                  ay-milp/src/hybrid_pb_lp.rs+ay-milp/src/cert.rs+\
                                  ay-milp/src/exact.rs+ay-pb-core"
                                .to_owned(),
                        });
                        Some(Outcome::Optimal {
                            value,
                            model_values,
                            cert: None,
                        })
                    }
                };
                if let Some(outcome) = outcome {
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    let out = if supplemental_proof.certifies_infeasibility() {
                        finish_exact_reduction_with_supplemental_proof(
                            outcome,
                            &self.model,
                            &solved,
                            &self.opts,
                            supplemental_proof,
                        )
                    } else {
                        finish_exact_reduction(outcome, &self.model, &solved, &self.opts)
                    };
                    self.replay_claims = crate::cert_io::ledger::take();
                    return Ok(out);
                }
            }
        }
        // `Auto` is the historical empty-prefix margin behavior. `Required`
        // creates one nested optimization session under this already-pinned
        // deadline. `ReframedProof` reaches the native call below; its exact
        // bound can trigger proof replay but cannot authorize a verdict.
        let margin_proof_target = match margin_mode {
            MarginMode::Auto => {
                if let Some(reframed) = crate::margin::reframe(&self.model, &self.opts) {
                    let solved = SolvedObjective {
                        coeffs: &objective,
                        sense: self.model.sense(),
                        offset: self.model.objective_offset(),
                        exact: exact_objective,
                    };
                    return Ok(finish(reframed.verdict, &self.model, &solved, &self.opts));
                }
                None
            }
            MarginMode::Disabled => None,
            MarginMode::Required => {
                let crate::margin::PreparedMargin {
                    reframed_model,
                    mapping,
                } = crate::margin::prepare(&self.model).ok_or_else(|| MilpError::Session {
                    message: "marked-margin shared prefix requires an enabled, objective-zero, \
                              nonempty one-sided margin row"
                        .to_owned(),
                })?;
                let target = mapping.proof_target(&self.model);
                // Certificate policy belongs to the ORIGINAL verdict. A
                // reframed MILP optimum may carry no optimality artifact even
                // though its point is a complete original-feasibility witness;
                // rejecting it here would discard authority the outer
                // `finish` can independently check. The outer policy still
                // requires evidence for any mapped Infeasible claim.
                let sub_opts = self.opts.clone().with_require_certificates(false);
                let mut sub = BabSession::new(reframed_model, &sub_opts)?;
                sub.hint_branch_order(&self.branch_hints);
                sub.shortlist_root_strong_branch_candidates(&self.root_strong_branch_shortlist);
                let reframed_outcome = sub.check_with_shared_binary_prefix(
                    shared_binary_prefix,
                    None,
                    MarginMode::ReframedProof(target),
                    target_fsb_prefix,
                )?;
                let mut reframed = mapping.map(&self.model, reframed_outcome);
                // This explicit proof API has a stronger contract than the
                // generic `require_certificates` policy: an UNSAT mapping is
                // authoritative only with a complete caller-frame MILP tree.
                // In particular, a fully solved reframed MILP may report an
                // uncertified `Optimal` result; mapping its value past the
                // threshold must not manufacture a bare original-model
                // `Infeasible` when the caller left the generic policy off.
                //
                // `MarginMapping::map` has already filtered tree artifacts
                // against the original model. Presence here therefore means
                // verified; the outer `finish` gate independently verifies the
                // retained tree again without adding another full tree walk at
                // this boundary.
                let has_verified_margin_tree = matches!(
                    &reframed.verdict,
                    Outcome::Infeasible {
                        tree_cert: Some(_),
                        ..
                    }
                );
                if reframed.verdict.is_infeasible() && !has_verified_margin_tree {
                    reframed.verdict = Outcome::Unknown {
                        reason: UnknownReason::CertificateUnavailable,
                    };
                }
                let solved = SolvedObjective {
                    coeffs: &objective,
                    sense: self.model.sense(),
                    offset: self.model.objective_offset(),
                    exact: exact_objective,
                };
                return Ok(finish(reframed.verdict, &self.model, &solved, &self.opts));
            }
            MarginMode::ReframedProof(target) => Some(target),
        };
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
                //
                // THE ANCHOR'S BOUNDED FIRST REFUSAL. When a lane's verdict was
                // deferred for being below the anchor's evidence reach, native
                // search runs on a TIGHTENED deadline: long enough to produce
                // the stronger proof if it can, short enough that failing to
                // costs bounded latency rather than the caller's whole budget.
                // The slice is derived from the model, never from how patient
                // the caller happened to be — see `claim::ANCHOR_FIRST_REFUSAL_CAP`
                // for why deadline-derived speculation is the specific shape
                // that made `markshare_5_0` slower the more time it was given.
                //
                // With no deferred claim this is `self.opts` unchanged, so the
                // ordinary path is byte-identical.
                let anchor_opts = match (&self.deferred_claim, &self.opts.deadline) {
                    (Some(_), _) => {
                        match crate::claim::AnchorFirstRefusal::plan(
                            Instant::now(),
                            self.opts.deadline,
                        ) {
                            Some(refusal) => {
                                let mut tightened = self.opts.clone();
                                tightened.deadline = Some(refusal.until);
                                std::borrow::Cow::Owned(tightened)
                            }
                            None => std::borrow::Cow::Borrowed(&self.opts),
                        }
                    }
                    _ => std::borrow::Cow::Borrowed(&self.opts),
                };
                let anchor_opts: &SolveOpts = &anchor_opts;
                let mut raw = match self.incumbent_seed.as_deref() {
                    Some(seed) => crate::bab::solve_milp_seeded(
                        &self.model,
                        anchor_opts,
                        seed,
                        &self.branch_hints,
                        &self.root_strong_branch_shortlist,
                    ),
                    None if !shared_binary_prefix.is_empty() => {
                        match (proof_first_workers, margin_proof_target.as_ref()) {
                            (Some(workers), None) => {
                                crate::bab::solve_milp_shared_binary_prefix_proof_first(
                                    &self.model,
                                    &self.opts,
                                    shared_binary_prefix,
                                    workers,
                                    &self.branch_hints,
                                    &self.root_strong_branch_shortlist,
                                )
                            }
                            (None, Some(target)) => {
                                crate::bab::solve_milp_shared_binary_prefix_with_margin_proof(
                                    &self.model,
                                    &self.opts,
                                    shared_binary_prefix,
                                    target,
                                    &self.branch_hints,
                                    &self.root_strong_branch_shortlist,
                                    target_fsb_prefix,
                                )
                            }
                            (None, None) => crate::bab::solve_milp_shared_binary_prefix(
                                &self.model,
                                &self.opts,
                                shared_binary_prefix,
                                &self.branch_hints,
                                &self.root_strong_branch_shortlist,
                            ),
                            (Some(_), Some(_)) => {
                                return Err(MilpError::Session {
                                    message: "marked-margin proof target does not compose with \
                                              proof-first prefix workers"
                                        .to_owned(),
                                });
                            }
                        }
                    }
                    None if self.branch_hints.is_empty()
                        && self.root_strong_branch_shortlist.is_empty() =>
                    {
                        crate::bab::solve_milp(&self.model, anchor_opts)
                    }
                    None => crate::bab::solve_milp_advised(
                        &self.model,
                        anchor_opts,
                        &self.branch_hints,
                        &self.root_strong_branch_shortlist,
                    ),
                };
                // The parity device lives below branch-and-bound's public
                // `Outcome`, so drain its typed side artifact immediately after
                // that call.  Rebuild the contradiction from this session's
                // source model before retaining it; a stale, malformed, or
                // non-infeasible pairing is discarded and can authorize
                // neither the full-evidence policy nor certificate emission.
                if let Some(certificate) = crate::parity::take_pending_infeasibility_certificate() {
                    if raw.is_infeasible()
                        && crate::verify_parity_infeasibility_certificate(&self.model, &certificate)
                            .is_ok()
                    {
                        self.parity_infeasibility_certificate = Some(certificate);
                    }
                }
                // An interrupted tree that holds nothing but a rigorous dual bound
                // now reports `Bound` rather than `Unknown` (see the no-incumbent
                // arms of `solve_milp_in`). That is still "no primal verdict", so
                // it must keep reaching the smt fallback exactly as `Unknown` did —
                // otherwise the bound fix would silently COST the verdicts smt was
                // rescuing. And if smt in turn settles nothing, the bound we set
                // aside is strictly better than the `Unknown` smt hands back, so it
                // is restored rather than discarded.
                #[cfg(feature = "smt")]
                if shared_binary_prefix.is_empty()
                    && (raw.is_unknown() || matches!(raw, Outcome::Bound { .. }))
                    && !expired(&self.opts)
                    && self.smt_fallback_within_reach()
                {
                    let held = match &raw {
                        Outcome::Bound {
                            dual_bound,
                            rigorous,
                        } => Some((dual_bound.clone(), *rigorous)),
                        _ => None,
                    };
                    let mut smt = crate::smt::SmtMilp::new(&self.model, &self.opts)?;
                    raw = if has_objective {
                        smt.optimize(&self.model, &self.opts, &objective, self.model.sense())?
                    } else {
                        smt.check_feasible(&self.opts)?
                    };
                    if let (true, Some((dual_bound, rigorous))) = (raw.is_unknown(), held) {
                        raw = Outcome::Bound {
                            dual_bound,
                            rigorous,
                        };
                    }
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
                    } if self.parity_infeasibility_certificate.is_none() => {
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
                        // FLOAT-FIRST, RIM-AUTHORITY (see
                        // `tree_cert::root_float_farkas`). The exact rim alone
                        // could not AFFORD this witness at real scale: measured
                        // on the downstream optimization consumer's captured W1 corpus, two presolve-decided
                        // infeasible models (1980x1567 and 1600x1290, zero
                        // branch-and-bound nodes) shipped `evidence infeasible
                        // NONE` because the grace expired — and the witness was
                        // there the whole time, reachable in 5.6 ms / 3.2 ms
                        // once the float lane proposes the ray and the rationals
                        // only have to CHECK it (29.0 s / 16.4 s for the exact
                        // rim to derive the same thing from cold, measured with
                        // `--cert-grace-secs`).
                        //
                        // Strictly additive: the returned certificate is already
                        // exact-verified against this model, a declining float
                        // lane falls through to the identical exact pass below,
                        // and `finish` re-verifies either one.
                        match crate::tree_cert::root_float_farkas(&self.model, budget.deadline) {
                            Some(cert) => Outcome::Infeasible {
                                cert: Some(cert),
                                tree_cert: None,
                            },
                            None => {
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
                        // Bounded post-verdict certificate pass, float-first for
                        // the same reason the native lane above is: the exact
                        // rim derives the SAME object from cold in seconds that
                        // checking a proposed ray takes in milliseconds. See
                        // `tree_cert::root_float_farkas`.
                        let budget = cert_budget_for(&self.model, &self.opts);
                        match crate::tree_cert::root_float_farkas(&self.model, budget.deadline) {
                            Some(cert) => Outcome::Infeasible {
                                cert: Some(cert),
                                tree_cert: None,
                            },
                            None => {
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
        // A threshold-crossing margin tree is finalized in the ORIGINAL
        // feasibility frame, not this nested reframed model. Let it leave the
        // nested session only after direct original-frame verification; the
        // outer margin map and outer `finish` verify it again.
        let original_margin_tree_verified = match (&margin_proof_target, &outcome) {
            (
                Some(target),
                Outcome::Infeasible {
                    tree_cert: Some(tree),
                    ..
                },
            ) => tree.verify(target.proof_model()).is_ok(),
            _ => false,
        };
        let parity_infeasibility_verified = outcome.is_infeasible()
            && self
                .parity_infeasibility_certificate
                .as_ref()
                .is_some_and(|certificate| {
                    crate::verify_parity_infeasibility_certificate(&self.model, certificate).is_ok()
                });
        if !parity_infeasibility_verified && outcome.is_infeasible() {
            self.parity_infeasibility_certificate = None;
        }
        let out = if original_margin_tree_verified {
            outcome
        } else if parity_infeasibility_verified {
            finish_exact_reduction_with_supplemental_proof(
                outcome,
                &self.model,
                &solved,
                &self.opts,
                SupplementalProof::VerifiedParityInfeasibility,
            )
        } else {
            finish(outcome, &self.model, &solved, &self.opts)
        };
        // THE DEFERRED CLAIM COMES BACK. This is the half of the invariant that
        // makes deferral safe: a claim held for being below the anchor's
        // evidence reach is published verbatim whenever the anchor did not in
        // fact do better. There is no path on which it is dropped.
        let out = self.publish_deferred_if_native_did_not_decide(out, &solved);
        // Drain the ledger into the session that produced it. A verdict the
        // `finish` gate withheld keeps its claims too: `--emit-cert` on an
        // `Unknown` still reports what the device tried.
        self.replay_claims = crate::cert_io::ledger::take();
        Ok(out)
    }

    /// Resolve a deferred lane verdict against what native search came back
    /// with. Three cases, and only three:
    ///
    /// 1. **Native decided, and agrees.** Native's verdict is published. Its
    ///    evidence is by construction at least as strong as the deferred claim's
    ///    (that is precisely why the claim was deferred), so this is the case the
    ///    deferral was FOR — on `W1_unsat_v9_c14_000008` it turns 758
    ///    unverifiable bytes into a 19,664-byte tree certificate `verify`
    ///    accepts at exit 0. The lane's replay claim rides along as
    ///    corroboration rather than being discarded.
    /// 2. **Native did not decide** (timeout, `Bound`, `Unknown`). The deferred
    ///    verdict is published unchanged. The comparison here is `verdict`
    ///    against `Unknown` and `Replay` against nothing — dominance on both
    ///    axes, with nothing predicted and nothing to tune.
    /// 3. **Native decided and CONTRADICTS the deferred claim.** Two independent
    ///    exact engines disagree about the same model. Neither answer may be
    ///    published: the greedy router resolved this silently by letting
    ///    whichever lane ran first win, and that is the one failure mode a
    ///    portfolio is uniquely able to SEE. Fail closed to `WitnessRejected`
    ///    naming both sides. Across ~3,300 adversarial models, 542 corpus solves
    ///    and 393 certificate splices this has never fired; if it ever does,
    ///    saying so is worth more than either answer.
    fn publish_deferred_if_native_did_not_decide(
        &mut self,
        native: Outcome,
        solved: &SolvedObjective<'_>,
    ) -> Outcome {
        let Some(deferred) = self.deferred_claim.take() else {
            return native;
        };
        // CASE 3 IS CHECKED FIRST, AND IT IS CHECKED AGAINST *ANY* NATIVE
        // ANSWER, NOT ONLY A DECIDED ONE. A native `Feasible` is not a decided
        // verdict — it is an interrupted search holding a point — but a POINT
        // still flatly contradicts a refutation, and resolving that by the
        // ordinary "native did not decide, publish the deferred claim" rule
        // would publish INFEASIBLE for a model native had just exhibited a
        // feasible point of. That is the greedy router's silent-resolution
        // failure re-created inside the fix, so it is ruled out here rather
        // than downstream.
        let native_exhibits_a_point =
            matches!(native, Outcome::Feasible { .. } | Outcome::Optimal { .. });
        let deferred_refutes = matches!(deferred.outcome, Outcome::Infeasible { .. });
        let deferred_exhibits_a_point = matches!(
            deferred.outcome,
            Outcome::Feasible { .. } | Outcome::Optimal { .. }
        );
        let native_refutes = matches!(native, Outcome::Infeasible { .. });
        let trap = |native: &Outcome, deferred: &crate::claim::Deferred| Outcome::Unknown {
            reason: UnknownReason::WitnessRejected {
                detail: format!(
                    "portfolio disagreement: native search returned {} while lane `{}` \
                     returned {} for the same model; neither verdict is published",
                    verdict_word(native),
                    deferred.lane,
                    verdict_word(&deferred.outcome),
                ),
            },
        };
        if (native_exhibits_a_point && deferred_refutes)
            || (native_refutes && deferred_exhibits_a_point)
        {
            return trap(&native, &deferred);
        }
        let native_decided = !matches!(
            native,
            Outcome::Unknown { .. } | Outcome::Bound { .. } | Outcome::Feasible { .. }
        );
        if native_decided {
            // Remaining cross-class disagreements (an unbounded objective
            // against a refutation, say).
            let contradiction = match (&native, &deferred.outcome) {
                (Outcome::Infeasible { .. }, Outcome::Infeasible { .. }) => false,
                (Outcome::Unbounded, Outcome::Unbounded) => false,
                (Outcome::Optimal { .. }, Outcome::Optimal { .. }) => false,
                (Outcome::Infeasible { .. }, _) | (_, Outcome::Infeasible { .. }) => true,
                _ => false,
            };
            if contradiction {
                return trap(&native, &deferred);
            }
            // Case 1. Publish native's verdict WITH native's artifacts AND the
            // lane's replay claim. The union, not a choice: native decided, but
            // native's own evidence is not guaranteed to be the stronger one —
            // measured on a PHP(8,7) refutation, native returns
            // `Infeasible{cert:None,tree_cert:None}` (census NONE) while the
            // deferred lane held a REPLAY claim. Filing the lane's claim rather
            // than dropping it is what makes this a least-upper-bound over the
            // two answers instead of a preference for one.
            if structure_trace_enabled() {
                eprintln!(
                    "--trace portfolio: native decided inside its first-refusal slice; \
                     publishing native's verdict, lane `{}` claim filed as corroboration",
                    deferred.lane,
                );
            }
            for claim in deferred.replay_claims {
                crate::cert_io::ledger::record(claim);
            }
            return native;
        }
        // Case 2.
        if structure_trace_enabled() {
            eprintln!(
                "--trace portfolio: native did not decide inside its first-refusal \
                 slice; publishing deferred verdict from lane `{}`",
                deferred.lane,
            );
        }
        for claim in deferred.replay_claims {
            crate::cert_io::ledger::record(claim);
        }
        finish_exact_reduction(deferred.outcome, &self.model, solved, &self.opts)
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
        // B6: the AY_MILP_SMT_MIN_BUDGET env override is deleted.
        let floor = SMT_FALLBACK_MIN_BUDGET_SECS;
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
mod ft_adoption_frame_tests {
    use super::*;

    fn tiny_integral_session() -> BabSession {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(0.0, 1.0, &[(x, 1.0)]);
        BabSession::new(model, &SolveOpts::new()).expect("valid tiny integral session")
    }

    #[test]
    fn completed_check_clears_carriers_from_post_check_standalone_lp() {
        let _guard = crate::sepstat::adoption_test_guard();
        let mut session = tiny_integral_session();
        let _ = session.check().expect("tiny check succeeds");

        assert!(session.model.ft_adoption_solve_latch().is_none());
        assert!(session.opts.ft_adoption_solve_latch().is_none());
        let standalone =
            FloatLp::from_model(session.model(), &[], Sense::Minimize).expect("standalone LP");
        let before = crate::sepstat::adoption_forgone();
        assert!(
            !standalone.charge_ft_adoption_exclusion(),
            "post-check public model leaked a stale census frame"
        );
        assert_eq!(crate::sepstat::adoption_forgone(), before);
    }

    #[test]
    fn check_unwind_clears_both_local_frame_carriers() {
        let mut session = tiny_integral_session();
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _frame = FtAdoptionFrame::enter(&mut session);
            panic!("exercise census-frame unwind cleanup");
        }));

        assert!(unwound.is_err());
        assert!(session.model.ft_adoption_solve_latch().is_none());
        assert!(session.opts.ft_adoption_solve_latch().is_none());
    }

    #[test]
    fn repeated_public_checks_clear_and_allocate_distinct_top_level_frames() {
        let _guard = crate::sepstat::adoption_test_guard();
        let mut session = tiny_integral_session();
        for _ in 0..2 {
            let _ = session.check().expect("repeated tiny check succeeds");
            assert!(session.model.ft_adoption_solve_latch().is_none());
            assert!(session.opts.ft_adoption_solve_latch().is_none());
        }

        let before = crate::sepstat::adoption_forgone();
        let first = {
            let frame = FtAdoptionFrame::enter(&mut session);
            assert_eq!(frame.ownership(), FtAdoptionFrameOwnership::TopLevelOwner);
            let latch = frame
                .session
                .model
                .ft_adoption_solve_latch()
                .expect("owner installed model carrier");
            assert!(latch.charge(7));
            latch
        };
        assert!(session.model.ft_adoption_solve_latch().is_none());
        assert!(session.opts.ft_adoption_solve_latch().is_none());
        let second = {
            let frame = FtAdoptionFrame::enter(&mut session);
            assert_eq!(frame.ownership(), FtAdoptionFrameOwnership::TopLevelOwner);
            let latch = frame
                .session
                .opts
                .ft_adoption_solve_latch()
                .expect("owner installed options carrier");
            assert!(!first.same_frame(&latch));
            assert!(latch.charge(13));
            latch
        };
        assert!(!first.same_frame(&second));
        assert!(session.model.ft_adoption_solve_latch().is_none());
        assert!(session.opts.ft_adoption_solve_latch().is_none());

        let after = crate::sepstat::adoption_forgone();
        assert_eq!(after.0 - before.0, 2);
        assert_eq!(after.1 - before.1, 20);
    }

    #[test]
    fn margin_style_nested_check_borrows_outer_frame_without_double_count() {
        let _guard = crate::sepstat::adoption_test_guard();
        let mut outer = tiny_integral_session();
        let before = crate::sepstat::adoption_forgone();

        {
            let outer_frame = FtAdoptionFrame::enter(&mut outer);
            assert_eq!(
                outer_frame.ownership(),
                FtAdoptionFrameOwnership::TopLevelOwner
            );
            let outer_latch = outer_frame
                .session
                .model
                .ft_adoption_solve_latch()
                .expect("outer model carrier");

            // `margin::reframe` clones the outer model, clones these options
            // through `BabSession::new`, then invokes the nested check.
            let reframed_model = outer_frame.session.model.clone();
            let nested_opts = outer_frame.session.opts.clone();
            let mut nested =
                BabSession::new(reframed_model, &nested_opts).expect("valid nested session");
            {
                let nested_frame = FtAdoptionFrame::enter(&mut nested);
                assert_eq!(
                    nested_frame.ownership(),
                    FtAdoptionFrameOwnership::NestedBorrower
                );
                let nested_latch = nested_frame
                    .session
                    .opts
                    .ft_adoption_solve_latch()
                    .expect("nested options carrier");
                assert!(outer_latch.same_frame(&nested_latch));
                assert!(nested_latch.charge(29));
            }
            assert!(nested.model.ft_adoption_solve_latch().is_none());
            assert!(nested.opts.ft_adoption_solve_latch().is_none());
            assert!(
                !outer_latch.charge(101),
                "outer and margin-nested paths charged separate frames"
            );
            assert!(outer_frame
                .session
                .model
                .ft_adoption_solve_latch()
                .is_some_and(|latch| latch.same_frame(&outer_latch)));
        }
        assert!(outer.model.ft_adoption_solve_latch().is_none());
        assert!(outer.opts.ft_adoption_solve_latch().is_none());

        let after = crate::sepstat::adoption_forgone();
        assert_eq!(after.0 - before.0, 1);
        assert_eq!(after.1 - before.1, 29);
    }

    #[test]
    fn actual_margin_reframe_enters_one_owner_and_one_borrower() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(2.0, 2.0, &[(x, 1.0), (y, 1.0)]);
        let margin = model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
        model
            .mark_margin_row(margin)
            .expect("fixture has a one-sided margin");
        let mut session = BabSession::new(model, &SolveOpts::new()).expect("valid margin session");
        let before = ft_adoption_frame_entry_counts();

        let outcome = session.check().expect("margin reframe check succeeds");
        assert!(outcome.is_infeasible());
        let after = ft_adoption_frame_entry_counts();
        assert_eq!(after.0 - before.0, 1, "outer check owns exactly one frame");
        assert_eq!(
            after.1 - before.1,
            1,
            "production margin reframe must borrow the outer frame"
        );
        assert!(session.model.ft_adoption_solve_latch().is_none());
        assert!(session.opts.ft_adoption_solve_latch().is_none());
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
    fn rigorous_bound_expr_survives_mixed_sign_duals_on_one_sided_rows() {
        use num_traits::ToPrimitive as _;
        // REGRESSION: a multi-column objective over one-sided rows (lb = -inf) yields a dual
        // with mixed signs. The NS slack term is then -inf for the wrong-signed rows and
        // NEITHER global flip rescues it, so the bound was declined even though the column
        // form succeeded on the very same model. Zeroing the offending components restores a
        // finite bound. Coefficients come from a real star-set reachability query, where
        // this showed up as a 100% decline rate.
        let mut m = Model::new();
        let cols: Vec<_> = (0..5).map(|_| m.add_col(-1.0, 1.0)).collect();
        let a = [
            [
                0.316_227_766_016_837_94,
                -0.707_106_781_186_547_6,
                0.141_421_356_237_309_5,
                0.0,
                0.948_683_298_050_513_8,
            ],
            [
                -0.057_735_026_918_962_58,
                0.288_675_134_594_812_9,
                -0.866_025_403_784_438_6,
                0.115_470_053_837_925_15,
                0.0,
            ],
            [
                0.001_224_744_871_391_589_2,
                0.0,
                0.0,
                -0.048_989_794_855_663_56,
                0.244_948_974_278_317_83,
            ],
        ];
        let b = [
            -0.123_091_490_979_332_72,
            0.447_213_595_499_957_9,
            -0.001_897_366_596_101_027_5,
        ];
        for (row, rhs) in a.iter().zip(b.iter()) {
            let coeffs: Vec<_> = row
                .iter()
                .enumerate()
                .filter(|(_, w)| **w != 0.0)
                .map(|(j, &w)| (cols[j], w))
                .collect();
            m.add_row(f64::NEG_INFINITY, *rhs, &coeffs);
        }
        let g = [
            0.774_596_669_241_483_4,
            -0.258_198_889_747_161_1,
            0.516_397_779_494_322_2,
            0.0,
            -0.129_099_444_873_580_55,
        ];
        let expr: Vec<_> = cols
            .iter()
            .zip(g.iter())
            .filter(|(_, w)| **w != 0.0)
            .map(|(&c, &w)| (c, w))
            .collect();
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");
        for sense in [Sense::Minimize, Sense::Maximize] {
            match s.rigorous_bound_expr(&expr, sense).expect("expr bound") {
                Outcome::Bound { dual_bound, .. } => {
                    assert!(
                        dual_bound.to_f64().expect("f64").is_finite(),
                        "{sense:?} produced a non-finite bound"
                    );
                }
                other => panic!("{sense:?} declined on a solvable model: {other:?}"),
            }
        }
    }

    #[test]
    fn rigorous_bound_expr_is_as_tight_as_the_column_form() {
        use num_traits::ToPrimitive as _;
        // The expression form must not merely be CHEAPER than the column form, it must be as
        // TIGHT. Before the exact-rim tier existed, a weak NS answer was final and the
        // expression form lost on exactly the queries where tightness decides an outcome.
        // Bound x + y two ways: directly as an expression, and via a materialised column
        // z = x + y. The answers must agree.
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let y = m.add_col(-1.0, 1.0);
        let z = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0), (y, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 0.25, &[(x, 1.0), (y, -1.0)]);
        // z - x - y = 0
        m.add_row(0.0, 0.0, &[(z, 1.0), (x, -1.0), (y, -1.0)]);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");

        for sense in [Sense::Minimize, Sense::Maximize] {
            let via_col = match s.rigorous_bound(z, sense).expect("col") {
                Outcome::Bound { dual_bound, .. } => dual_bound.to_f64().expect("f64"),
                other => panic!("column form gave {other:?}"),
            };
            let via_expr = match s
                .rigorous_bound_expr(&[(x, 1.0), (y, 1.0)], sense)
                .expect("expr")
            {
                Outcome::Bound { dual_bound, .. } => dual_bound.to_f64().expect("f64"),
                other => panic!("expression form gave {other:?}"),
            };
            assert!(
                (via_col - via_expr).abs() < 1e-9,
                "{sense:?}: expression {via_expr} is not as tight as column {via_col}"
            );
        }
    }

    #[test]
    fn float_dual_for_expr_returns_a_usable_multiplier_vector() {
        // The contract is only that the vector has one entry per row and is finite — it is
        // explicitly UNTRUSTED, so there is nothing else to assert about its values. What
        // matters is that a caller can turn it into a sound bound by weak duality, which is
        // what the star-set caller does.
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let y = m.add_col(-1.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0), (y, 1.0)]);
        m.add_row(f64::NEG_INFINITY, 0.25, &[(x, 1.0), (y, -1.0)]);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");

        for sense in [Sense::Minimize, Sense::Maximize] {
            let duals = s
                .float_dual_for_expr(&[(x, 1.0), (y, 1.0)], sense)
                .expect("no error")
                .expect("float lane settles on a 2x2");
            assert_eq!(duals.len(), 2, "one dual per row");
            assert!(duals.iter().all(|v| v.is_finite()), "duals must be finite");
        }
    }

    #[test]
    fn float_dual_for_expr_validates_input_and_declines_the_empty_form() {
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");
        assert!(s
            .float_dual_for_expr(&[(Col(99), 1.0)], Sense::Minimize)
            .is_err());
        assert!(s
            .float_dual_for_expr(&[(x, f64::NAN)], Sense::Minimize)
            .is_err());
        assert!(s
            .float_dual_for_expr(&[], Sense::Minimize)
            .expect("no error")
            .is_none());
    }

    #[test]
    fn rigorous_bound_expr_matches_the_single_column_form() {
        // The expression API must agree with the column API on a one-column objective,
        // otherwise callers cannot migrate to it.
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let y = m.add_col(-1.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0), (y, 1.0)]);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");

        for sense in [Sense::Minimize, Sense::Maximize] {
            let col_form = s.rigorous_bound(x, sense).expect("col bound");
            let expr_form = s
                .rigorous_bound_expr(&[(x, 1.0)], sense)
                .expect("expr bound");
            match (&col_form, &expr_form) {
                (Outcome::Bound { dual_bound: a, .. }, Outcome::Bound { dual_bound: b, .. }) => {
                    assert_eq!(a, b, "column and expression forms disagree for {sense:?}")
                }
                other => panic!("expected two bounds, got {other:?}"),
            }
        }
    }

    #[test]
    fn rigorous_bound_expr_bounds_a_true_linear_form() {
        use num_traits::ToPrimitive as _;
        // x + y over {x,y in [-1,1], x + y <= 0.5}: min -2, max 0.5. The bound must
        // enclose that, and must NOT be tighter than it.
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let y = m.add_col(-1.0, 1.0);
        m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0), (y, 1.0)]);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");

        let lo = match s
            .rigorous_bound_expr(&[(x, 1.0), (y, 1.0)], Sense::Minimize)
            .expect("min")
        {
            Outcome::Bound { dual_bound, .. } => dual_bound.to_f64().expect("f64"),
            other => panic!("expected a bound, got {other:?}"),
        };
        let hi = match s
            .rigorous_bound_expr(&[(x, 1.0), (y, 1.0)], Sense::Maximize)
            .expect("max")
        {
            Outcome::Bound { dual_bound, .. } => dual_bound.to_f64().expect("f64"),
            other => panic!("expected a bound, got {other:?}"),
        };
        assert!(lo <= -2.0 + 1e-9, "lower {lo} must not exceed the true -2");
        assert!(
            hi >= 0.5 - 1e-9,
            "upper {hi} must not undercut the true 0.5"
        );
        assert!(
            lo > -10.0 && hi < 10.0,
            "bounds should still be useful: [{lo}, {hi}]"
        );
    }

    #[test]
    fn rigorous_bound_expr_accumulates_a_repeated_column() {
        use num_traits::ToPrimitive as _;
        // (x, 1.0) twice must mean 2x, not x.
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");
        let doubled = match s
            .rigorous_bound_expr(&[(x, 1.0), (x, 1.0)], Sense::Maximize)
            .expect("max")
        {
            Outcome::Bound { dual_bound, .. } => dual_bound.to_f64().expect("f64"),
            other => panic!("expected a bound, got {other:?}"),
        };
        assert!(
            doubled >= 2.0 - 1e-9,
            "2x over [-1,1] maxes at 2, got {doubled}"
        );
    }

    #[test]
    fn rigorous_bound_expr_rejects_bad_input_and_handles_the_empty_form() {
        let mut m = Model::new();
        let x = m.add_col(-1.0, 1.0);
        let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");

        assert!(s
            .rigorous_bound_expr(&[(Col(99), 1.0)], Sense::Minimize)
            .is_err());
        assert!(s
            .rigorous_bound_expr(&[(x, f64::NAN)], Sense::Minimize)
            .is_err());

        // The empty expression is the constant 0.
        match s.rigorous_bound_expr(&[], Sense::Minimize).expect("empty") {
            Outcome::Bound { dual_bound, .. } => {
                assert_eq!(dual_bound, BigRational::from_integer(0.into()));
            }
            other => panic!("expected an exact 0, got {other:?}"),
        }
    }

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

    /// THE ONE PLACE THE WITHHOLDING IS DELIBERATE, pinned on all three shapes
    /// the dual bound can now leave the engine in.
    ///
    /// A Neumaier–Shcherbina or safe-dual number is a valid bound for the LP the
    /// ROUNDED `f64` matrix denotes. On a model carrying a coefficient with no
    /// exact `f64` that is the wrong LP, so the number bounds a different problem
    /// and must be dropped rather than presented — the asymmetric rule this whole
    /// area runs on: an invalid "rigorous" bound is far worse than no bound.
    ///
    /// Pinned here because the bound now travels paths it did not before: a bare
    /// `Outcome::Bound` from an interrupted no-incumbent tree is a NEW shape at
    /// this boundary, and it degrades whole (there is no primal to keep) rather
    /// than losing a field. The `Feasible` arm is included so the pair reads as
    /// one rule, and an exact-coefficient control is included so the test cannot
    /// pass by the guard simply firing on everything.
    #[test]
    fn an_inexact_model_reports_no_dual_bound_on_any_arm() {
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 10.0);
        let row = m.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        // The stored `f64` says `x >= 1`; the TRUE row is `2x >= 1`, minimum 1/2.
        m.record_inexact_row_coeff(row, x.0, BigRational::from_integer(2.into()));

        let bound = BigRational::new(1.into(), 2.into());
        assert!(
            matches!(
                fail_closed_for_inexact(
                    Outcome::Bound {
                        dual_bound: bound.clone(),
                        rigorous: true
                    },
                    &m
                ),
                Outcome::Unknown {
                    reason: UnknownReason::CertificateUnavailable
                }
            ),
            "a bare rigorous Bound must degrade WHOLE on an inexact model"
        );
        match fail_closed_for_inexact(
            Outcome::Feasible {
                model_values: vec![BigRational::from_integer(1.into())],
                incumbent_only: true,
                dual_bound: Some(bound.clone()),
            },
            &m,
        ) {
            Outcome::Feasible { dual_bound, .. } => assert!(
                dual_bound.is_none(),
                "the incumbent survives (it is re-checked exactly); the bound riding \
                 along on it does not"
            ),
            other => panic!("the incumbent itself must be kept, got {other:?}"),
        }

        // CONTROL: the identical outcomes on an EXACT model pass through
        // untouched. Without this the two assertions above would also hold if
        // the guard had been widened to fire on every model.
        let mut exact_m = Model::new();
        let y = exact_m.add_int_col(0.0, 10.0);
        exact_m.add_row(1.0, f64::INFINITY, &[(y, 1.0)]);
        assert!(
            matches!(
                fail_closed_for_inexact(
                    Outcome::Bound {
                        dual_bound: bound.clone(),
                        rigorous: true
                    },
                    &exact_m
                ),
                Outcome::Bound { rigorous: true, .. }
            ),
            "an exact model must keep its bound"
        );
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

/// Force every lazily-cached environment read in this module to happen NOW.
///
/// # The race this closes
///
/// `tune.rs` states the property the crate is supposed to have: *"The environment
/// layer is read **once**, into `EnvSnapshot`, and never again — so no accessor on
/// the solve path touches `std::env`."* That is true of the `tune` layer and FALSE
/// of the crate: 2 accessors here cache their value in a `OnceLock` and call
/// `env::var` **lazily**, inside `get_or_init`, the first time the solve path
/// happens to reach them — at an arbitrary point, on an arbitrary thread.
///
/// That is the exact hazard `EngineEconomics` was built to remove.
/// the development design notes records the consumer's mitigation:
/// it *"rewrites the same constant values before every window solve"*, so a
/// `set_var` on one thread can land while another thread is mid-solve taking its
/// first `getenv` here. `std::env::set_var` racing a concurrent `getenv` is why it
/// is `unsafe` in edition 2024.
///
/// Priming collapses those windows into ONE, at solve entry, before any worker is
/// spawned. It changes no value: the same `OnceLock`s resolve to the same bytes.
/// It only moves *when* they are read, from "scattered across the solve" to "once,
/// at a point the caller controls".
pub(crate) fn prime_env() {
    let _ = float_lane_enabled();
    let _ = smt_lane_forced();
}
