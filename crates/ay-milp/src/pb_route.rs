// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact pure-Boolean MILP routes through AY's native PB engines.
//!
//! [`crate::pb_translate`] owns admission and the equivalence proof.  This
//! module is deliberately a thin adapter to the public `ay-pb-core` API and a
//! second fail-closed result boundary: every returned Boolean assignment is
//! checked against both the normalized PB plan and the original rational
//! [`Model`], and every claimed PB objective is mapped back and compared with
//! [`Model::objective_value_at`].
//!
//! Production ownership is intentionally structural: the bounded exact one-row
//! subset-sum/knapsack DP gets first refusal after exact translation, and a
//! compact portfolio gets a deadline-bounded trial.  A small dense Boolean
//! optimization plan receives a proof-sized slice; every other plan keeps the
//! short generic slice.  Structural/resource declines return immediately to
//! native MILP, and no PB trial silently inherits the whole remaining deadline.
//!
//! `ay-pb-core` has no `ay-milp` dependency.  The separate `ay-pb` facade owns
//! the reverse PB-to-MILP portfolio arm; using the core here therefore cannot
//! recurse back into this route.

use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_pb_core::portfolio::{
    solve_decision_portfolio, solve_optimization_portfolio,
    solve_optimization_portfolio_parallel_with_workers, solve_optimization_portfolio_with_timings,
};
use ay_pb_core::{
    encode_multi_row_bdd_infeasibility_certificate_json,
    encode_single_row_dp_infeasibility_certificate_json,
    generate_multi_row_bdd_infeasibility_certificate_interruptible,
    generate_single_row_dp_infeasibility_certificate_interruptible,
    solve_single_row_binary_interruptible,
    verify_multi_row_bdd_infeasibility_certificate_interruptible,
    verify_single_row_dp_infeasibility_certificate_interruptible, MultiRowBddDecline,
    MultiRowBddInfeasibilityCertificate, PbCdclResult, PbCdclSolver, PbConstraint, PbInstance,
    PbLit, PbObjective, PbRel, PbStatus, PbTerm, SingleRowDpDecline,
    SingleRowDpInfeasibilityCertificate, SingleRowDpOutcome,
};
use num_rational::BigRational;

use crate::pb_translate::{translate, PbInequality, PbObjectivePlan, PbRoutePlan};
use crate::Model;

/// General PB search retains several representations.  Keep every embedded
/// route inside one shared compact admission envelope before constructing the
/// core instance or its proof state graph.
const MAX_PORTFOLIO_TRIAL_VARS: u32 = 8_192;
const MAX_PORTFOLIO_TRIAL_CONSTRAINTS: usize = 8_192;
const MAX_PORTFOLIO_TRIAL_TERMS: usize = 250_000;

/// The general exact-PB arm remains a short piece of optional search: at most
/// half a second, and — see [`generic_trial_slice`] — no more than a small
/// multiple of what representing this model already cost.
const GENERIC_PORTFOLIO_TRIAL_CAP: Duration = Duration::from_millis(500);

/// How many translation passes of speculative PB search an UNRECOGNISED model
/// is worth.
///
/// THE PRELUDE TAX, AND WHY THE UNIT IS THE MODEL AND NOT THE DEADLINE.
///
/// `Generic` is the class a model lands in when [`portfolio_trial_ownership`]
/// declined it — the structural gate looked and found nothing it owns. Such a
/// model used to be handed `min(500ms, caller_deadline/10)`, which mentions the
/// caller's patience and never mentions the model. Every `--time-limit 60`
/// invocation therefore bought the same 500 ms speculative trial whether the
/// native lane needed 60 ms or 60 s, and on the general MIPLIB corpus that was
/// a measured flat tax on eight of ten instances at IDENTICAL node counts:
///
/// ```text
///   p0201     1.331s -> 0.334s    4.0x     khb05250  0.778s -> 0.278s   2.8x
///   dcmulti   1.124s -> 0.606s    1.9x     gt2       2.787s -> 1.781s   1.6x
/// ```
///
/// (measured as `AY_MILP_NO_STRUCTURE_ROUTE=1`, which removes the whole
/// prelude; the PB arm is the largest single share — a prior profile put
/// `try_solve_production_portfolio` at 398 of 730 samples on `markshare_5_0`.)
///
/// Translation is one linear pass over the nonzeros and has already been paid
/// by the time ownership is known, so it is a free, exact, model-derived unit
/// of "how big is this thing". A speculative search that cannot beat a tuned
/// branch-and-bound within a couple of dozen passes over the model was not
/// going to. The cap and the caller deadline still bound it from above, and
/// `DenseBooleanOptimization` — the class that owns its slice on structural
/// grounds — is deliberately untouched.
///
/// This is the repair `session.rs` prescribes in its own prelude-tax note:
/// budget it at the budget layer, so no recogniser has to decide on its own
/// authority that another lane may not run. Nothing here can refuse a lane; it
/// only declines to spend the user's wall on a model it already failed to
/// recognise.
const GENERIC_PORTFOLIO_TRANSLATION_MULTIPLE: u32 = 24;

/// Never round the generic slice below what the arm costs to START.
///
/// MEASURED: the exact-PB portfolio needs 32.3 ms to settle a three-variable,
/// two-constraint model — that is fixed set-up (translation is 7 us on the same
/// model), not search. A slice under it therefore buys nothing at all: the arm
/// is entered, does its set-up, and is cut off before it can conclude. That is
/// strictly worse than declining, because the time is spent either way.
///
/// So the floor is the arm's own start-up cost plus headroom, and it is a
/// MEASUREMENT rather than a taste: at 2 ms and at 10 ms the compact multi-row
/// PB model in `session_routes_compact_multirow_pb_through_bounded_portfolio`
/// still reached the right optimum, but by native branch-and-bound, silently
/// losing its `pb-portfolio-projection-optimal` evidence. Cutting a lane's
/// budget below its start-up cost is an EVIDENCE regression wearing a
/// performance hat, and only the claim assertion in that test caught it.
const GENERIC_PORTFOLIO_TRIAL_FLOOR: Duration = Duration::from_millis(48);

/// The speculative slice an unrecognised model earns, in its own units.
///
/// `translation` is the wall already spent representing the model exactly. See
/// [`GENERIC_PORTFOLIO_TRANSLATION_MULTIPLE`] for why that is the unit.
fn generic_trial_slice(translation: Duration) -> Duration {
    translation
        .checked_mul(GENERIC_PORTFOLIO_TRANSLATION_MULTIPLE)
        .unwrap_or(GENERIC_PORTFOLIO_TRIAL_CAP)
        .max(GENERIC_PORTFOLIO_TRIAL_FLOOR)
        .min(GENERIC_PORTFOLIO_TRIAL_CAP)
}

/// Compact block formulations can hide row-permutation symmetry from the
/// legacy row-pair detector when a row repeats coefficients.  The scalable
/// detector exactly verifies every candidate automorphism, but remains a
/// speculative front-end pass, so give it only a small part of a caller-owned
/// trial before the ordinary portfolio/fallback keeps control.
const BLOCK_SYMMETRY_DETECTION_CAP: Duration = Duration::from_millis(150);

/// Direct candidates avoid graph discovery and should verify quickly. Bound
/// them independently so a malformed-but-large supplied map cannot consume the
/// complete structural slice and starve the established generic fallback.
const BLOCK_SYMMETRY_CANDIDATE_VERIFICATION_CAP: Duration = Duration::from_millis(75);

/// A small dense Boolean optimization model is a PB problem in its native
/// representation, not merely a speculative MILP reduction.  Give that exact
/// engine enough wall to prove a nontrivial optimum while retaining at least a
/// third of every finite caller deadline for native branch-and-bound.
const DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP: Duration = Duration::from_secs(120);
const DENSE_BOOLEAN_MIN_VARS: u32 = 48;
const DENSE_BOOLEAN_MAX_VARS: u32 = 128;
const DENSE_BOOLEAN_MIN_ROWS: usize = 24;
const DENSE_BOOLEAN_MAX_ROWS: usize = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PortfolioTrialOwnership {
    Generic,
    DenseBooleanOptimization,
}

impl PortfolioTrialOwnership {
    fn trace_name(self) -> &'static str {
        match self {
            Self::Generic => "generic",
            Self::DenseBooleanOptimization => "dense-boolean-optimization",
        }
    }
}

/// A conclusive, independently checked result from the exact PB projection.
pub(crate) enum PbRouteDecision {
    /// Feasible point; `incumbent_only` distinguishes interrupted optimization
    /// from a completed decision solve.
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    /// The PB engine proved the exact projection infeasible.
    Infeasible,
    /// The bounded single-row engine proved infeasibility and exported a
    /// separately replayable exact reachability artifact.
    CertifiedSingleRowInfeasible {
        certificate: SingleRowDpInfeasibilityCertificate,
    },
    /// The bounded general linear-PB engine proved infeasibility and exported
    /// an independently replayable exact residual-state decision DAG.
    CertifiedMultiRowInfeasible {
        certificate: MultiRowBddInfeasibilityCertificate,
    },
    /// The PB engine proved a minimum of its transformed objective, mapped back
    /// to the caller's original min/max objective and exact offset.
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

/// What the verified block-symmetry trial actually consumed.
///
/// Callers use this distinction to budget a fallback phase. A structural
/// decline did not run the augmented optimizer and therefore must not earn a
/// second slice merely because a cheap shape precheck matched. Only a changed,
/// exactly validated, compact admitted augmentation owns the fallback, even if
/// its clock expires before the optimizer can enter search.
pub(crate) enum VerifiedBlockSymmetryAttempt {
    Declined,
    Admitted(Option<PbRouteDecision>),
}

impl VerifiedBlockSymmetryAttempt {
    pub(crate) fn decision(&self) -> Option<&PbRouteDecision> {
        match self {
            Self::Admitted(decision) => decision.as_ref(),
            Self::Declined => None,
        }
    }

    pub(crate) fn into_decision(self) -> Option<PbRouteDecision> {
        match self {
            Self::Admitted(decision) => decision,
            Self::Declined => None,
        }
    }

    pub(crate) fn earns_fresh_fallback(&self) -> bool {
        matches!(self, Self::Admitted(_))
    }
}

/// Keep the serial PB trial's ownership/allocation posture unchanged while
/// allowing a typed parallel trial to share one immutable instance across its
/// workers.  An unconditional `Arc` here would make even the one-thread default
/// pay synchronization-oriented allocation for a route that did not request it.
enum PortfolioTrialInstance {
    Serial(PbInstance),
    Parallel(Arc<PbInstance>),
}

impl PortfolioTrialInstance {
    fn as_instance(&self) -> &PbInstance {
        match self {
            Self::Serial(instance) => instance,
            Self::Parallel(instance) => instance.as_ref(),
        }
    }

    fn as_parallel(&self) -> Option<&Arc<PbInstance>> {
        match self {
            Self::Serial(_) => None,
            Self::Parallel(instance) => Some(instance),
        }
    }
}

/// Try only the bounded exact single-row specialization.
///
/// `None` means typed translation/structure/resource decline, interruption,
/// deadline, or a rejected result.  In particular, this production entry point
/// never invokes generic PB-CDCL after the specialization declines.
pub(crate) fn try_solve_specialized(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<PbRouteDecision> {
    try_solve_specialized_interruptible(model, deadline, || false)
}

/// Interruptible form of [`try_solve_specialized`].
pub(crate) fn try_solve_specialized_interruptible<F>(
    model: &Model,
    deadline: Option<Instant>,
    mut should_stop: F,
) -> Option<PbRouteDecision>
where
    F: FnMut() -> bool,
{
    let started = Instant::now();
    if should_stop() {
        return None;
    }
    let plan = match translate(model, deadline) {
        Ok(plan) => plan,
        Err(reason) => {
            if trace_enabled() {
                eprintln!("AY_MILP_TRACE pb-specialized: translation-declined={reason:?}");
            }
            return None;
        }
    };
    if deadline_reached(deadline) || should_stop() {
        return None;
    }
    let (instance, core_objective) = build_core_instance(&plan)?;

    let mut stopped = || deadline_reached(deadline) || should_stop();
    match solve_single_row_binary_interruptible(&instance, &mut stopped) {
        Ok(SingleRowDpOutcome::Feasible(assignment)) => {
            if core_objective.is_some() {
                return None;
            }
            let point = checked_point(model, &plan, &assignment, deadline)?;
            if trace_enabled() {
                eprintln!(
                    "AY_MILP_TRACE pb-specialized: engine=single-row-dp vars={} constraints={} \
                     objective=false verdict=FEASIBLE wall={:.6}s",
                    plan.num_vars,
                    plan.num_constraints,
                    started.elapsed().as_secs_f64(),
                );
            }
            return Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: false,
            });
        }
        Ok(SingleRowDpOutcome::Infeasible) => {
            if trace_enabled() {
                eprintln!(
                    "AY_MILP_TRACE pb-specialized: engine=single-row-dp vars={} constraints={} \
                     objective={} verdict=INFEASIBLE wall={:.6}s",
                    plan.num_vars,
                    plan.num_constraints,
                    plan.objective.is_some(),
                    started.elapsed().as_secs_f64(),
                );
            }
            let certificate_result =
                generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || {
                    stopped()
                });
            return map_single_row_infeasibility_certificate_result(certificate_result);
        }
        Ok(SingleRowDpOutcome::Optimal { assignment, value }) => {
            let (point, mapped) = checked_objective(
                model,
                &plan,
                plan.objective.as_ref()?,
                &assignment,
                value,
                deadline,
            )?;
            if trace_enabled() {
                eprintln!(
                    "AY_MILP_TRACE pb-specialized: engine=single-row-dp vars={} constraints={} \
                     objective=true verdict=OPTIMAL wall={:.6}s",
                    plan.num_vars,
                    plan.num_constraints,
                    started.elapsed().as_secs_f64(),
                );
            }
            return Some(PbRouteDecision::Optimal {
                value: mapped,
                model_values: point,
            });
        }
        Err(reason) => {
            if trace_enabled() {
                eprintln!("AY_MILP_TRACE pb-specialized: single-row-dp-declined={reason:?}");
            }
        }
    }

    // Deliberately no generic fallback here.  A bounded specialized decline
    // leaves the original native MILP solve its remaining deadline.
    None
}

/// Keep proof-export exhaustion distinct from a disagreement between the
/// decision pass and the independent certificate pass.  Only an explicit
/// export envelope miss may retain the already-established replay verdict;
/// structural, arithmetic, or verification disagreement invalidates the
/// specialized result altogether.
fn map_single_row_infeasibility_certificate_result(
    result: Result<Option<SingleRowDpInfeasibilityCertificate>, SingleRowDpDecline>,
) -> Option<PbRouteDecision> {
    match result {
        Ok(Some(certificate)) => {
            Some(PbRouteDecision::CertifiedSingleRowInfeasible { certificate })
        }
        Err(
            SingleRowDpDecline::ResourceLimit
            | SingleRowDpDecline::MemoryLimit
            | SingleRowDpDecline::Interrupted,
        ) => Some(PbRouteDecision::Infeasible),
        Ok(None) | Err(_) => None,
    }
}

/// Directly search for a bounded, typed single-row PB infeasibility proof.
///
/// Unlike [`try_solve_specialized`], this proof-only entry point never spends a
/// certificate-required solve optimizing a feasible model whose bare optimum
/// would then be discarded.  The same absolute deadline covers translation,
/// artifact generation, and model-bound replay.
pub(crate) fn try_prove_single_row_infeasibility(
    model: &Model,
    trial_deadline: Instant,
) -> Option<PbRouteDecision> {
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    let plan = translate(model, Some(trial_deadline)).ok()?;
    let (instance, _) = build_core_instance(&plan)?;
    let certificate =
        generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || {
            deadline_reached(Some(trial_deadline))
        })
        .ok()??;
    verify_single_row_infeasibility_certificate_with_deadline(
        model,
        &certificate,
        Some(trial_deadline),
    )
    .ok()?;
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    encode_single_row_dp_infeasibility_certificate_json(&certificate).ok()?;
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    Some(PbRouteDecision::CertifiedSingleRowInfeasible { certificate })
}

/// Map a second-pass general-PB proof export without laundering a disagreement
/// into replay evidence.  A preceding complete PB solve may retain its bare
/// infeasibility verdict only when proof construction explicitly exhausted its
/// resource envelope or was interrupted; `Ok(None)` and all structural,
/// arithmetic, or replay failures invalidate that verdict at this boundary.
fn map_multi_row_infeasibility_certificate_result(
    result: Result<Option<MultiRowBddInfeasibilityCertificate>, MultiRowBddDecline>,
) -> Option<PbRouteDecision> {
    match result {
        Ok(Some(certificate)) => Some(PbRouteDecision::CertifiedMultiRowInfeasible { certificate }),
        Err(
            MultiRowBddDecline::ResourceLimit
            | MultiRowBddDecline::MemoryLimit
            | MultiRowBddDecline::Interrupted,
        ) => Some(PbRouteDecision::Infeasible),
        Ok(None) | Err(_) => None,
    }
}

/// Directly search for a bounded, typed multi-row PB infeasibility proof.
///
/// This is the certificate-required counterpart of the complete PB portfolio:
/// it returns authority only when the decision DAG was generated, independently
/// replayed by `ay-pb-core`, then rebuilt and replayed once more from the
/// original MILP below.  A feasible system or any decline yields `None` because
/// this proof-only entry point does not export a primal witness.
pub(crate) fn try_prove_multi_row_infeasibility(
    model: &Model,
    trial_deadline: Instant,
) -> Option<PbRouteDecision> {
    let certificate = generate_multi_row_infeasibility_certificate(
        model,
        trial_deadline,
        MULTI_ROW_BDD_PRELUDE_MAX_VARS,
    )?;
    verify_multi_row_infeasibility_certificate_with_deadline(
        model,
        &certificate,
        Some(trial_deadline),
    )
    .ok()?;
    Some(PbRouteDecision::CertifiedMultiRowInfeasible { certificate })
}

/// Generate and serialize a multi-row proof for the network route without
/// replaying it against the producing master. This carries no authority by
/// itself: `network_design_route` must rebuild the source-bound projection and
/// replay the artifact before publishing its typed decision.
pub(crate) fn try_generate_network_multi_row_infeasibility_certificate(
    model: &Model,
    trial_deadline: Instant,
) -> Option<MultiRowBddInfeasibilityCertificate> {
    // The NETWORK route keeps the batch-engine admission: it asks for this proof
    // deliberately, having already decided the model is worth it. Only the
    // speculative prelude gets the small cap.
    generate_multi_row_infeasibility_certificate(model, trial_deadline, u32::MAX)
}

/// Variable cap for the SPECULATIVE prelude arm.
///
/// The multi-row BDD has NO early feasibility exit: `build_rejecting_dag` leaves
/// only by emptying the frontier (a proof) or by reaching the last variable with a
/// state alive (feasible). On a FEASIBLE model it must therefore descend every
/// layer, so it is guaranteed to consume its entire budget and return nothing —
/// and that budget is `24 x` the single-row cost (`session::probe_scaled_deadline`),
/// itself dominated by a PB translation this arm then REDOES.
///
/// Measured cost of that guarantee, trace-self-reported, zero hits:
///
/// ```text
///   gt2 43.8ms (20.8% of a 211ms solve)   qnet1 165ms   misc07 152ms
///   mod010 70ms   p0201 11.5ms            -- 442.5ms over five instances
/// ```
///
/// Declining cannot change a verdict: this arm's ONLY success value is
/// `CertifiedMultiRowInfeasible`, it never yields a feasible point or an optimum,
/// and `None` falls through to open-domain, hybrid PB-LP, integer lift, the
/// portfolio and finally complete native branch-and-bound. On a feasible model it
/// is provably incapable of hitting at all.
///
/// 128 sits above every multi-row capability the repo actually tests (2-3 Boolean
/// vars) and below the smallest corpus model that pays the tax (p0201, 201 PB
/// vars). It matches [`DENSE_BOOLEAN_MAX_VARS`], which already marks where small
/// dense Boolean reasoning stops in this file.
const MULTI_ROW_BDD_PRELUDE_MAX_VARS: u32 = 128;

fn generate_multi_row_infeasibility_certificate(
    model: &Model,
    trial_deadline: Instant,
    max_plan_vars: u32,
) -> Option<MultiRowBddInfeasibilityCertificate> {
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    let plan = translate(model, Some(trial_deadline)).ok()?;
    if !compact_plan_admitted(&plan)
        || plan.num_vars > max_plan_vars
        || deadline_reached(Some(trial_deadline))
    {
        return None;
    }
    let (instance, _) = build_core_instance(&plan)?;
    let certificate =
        generate_multi_row_bdd_infeasibility_certificate_interruptible(&instance, || {
            deadline_reached(Some(trial_deadline))
        })
        .ok()??;
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    encode_multi_row_bdd_infeasibility_certificate_json(&certificate).ok()?;
    if deadline_reached(Some(trial_deadline)) {
        return None;
    }
    Some(certificate)
}

/// Try generic PB-CDCL under a caller-provided absolute trial deadline.
///
/// This entry point exists for controlled A/B work.  Requiring an `Instant`
/// (rather than accepting `None`) prevents a caller from accidentally granting
/// raw PB search unbounded or whole-production-deadline ownership.  It does
/// not run the single-row specialization: callers that want a portfolio must
/// invoke [`try_solve_specialized`] first and budget this trial separately.
#[allow(dead_code)]
pub(crate) fn try_solve_generic_trial(
    model: &Model,
    trial_deadline: Instant,
) -> Option<PbRouteDecision> {
    try_solve_generic_trial_interruptible(model, trial_deadline, || false)
}

/// Interruptible form of [`try_solve_generic_trial`].
#[allow(dead_code)]
pub(crate) fn try_solve_generic_trial_interruptible<F>(
    model: &Model,
    trial_deadline: Instant,
    mut should_stop: F,
) -> Option<PbRouteDecision>
where
    F: FnMut() -> bool,
{
    let started = Instant::now();
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }
    let plan = match translate(model, Some(trial_deadline)) {
        Ok(plan) => plan,
        Err(reason) => {
            if trace_enabled() {
                eprintln!("AY_MILP_TRACE pb-generic-trial: translation-declined={reason:?}");
            }
            return None;
        }
    };
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }
    let (instance, core_objective) = build_core_instance(&plan)?;
    let mut stopped = || deadline_reached(Some(trial_deadline)) || should_stop();
    let mut solver = PbCdclSolver::new_interruptible(&instance, &mut stopped);
    solver.set_solve_deadline(Some(trial_deadline));
    if stopped() {
        return None;
    }

    let result = match core_objective.as_ref() {
        Some(objective) => solver.solve_optimize_interruptible(objective, None, &mut stopped),
        None => solver.solve_interruptible(&mut stopped),
    };
    if stopped() {
        return None;
    }

    let decision = match result {
        PbCdclResult::Unsatisfiable => Some(PbRouteDecision::Infeasible),
        PbCdclResult::Satisfiable(assignment) => {
            let point = checked_point(model, &plan, &assignment, Some(trial_deadline))?;
            // `Satisfiable` is the complete result for a decision problem.  It
            // would be only an incumbent if a future core optimizer returned it
            // directly despite an objective.
            Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: core_objective.is_some(),
            })
        }
        PbCdclResult::Feasible(assignment, claimed) => {
            let (point, _) = checked_objective(
                model,
                &plan,
                plan.objective.as_ref()?,
                &assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: true,
            })
        }
        PbCdclResult::Optimal(assignment, claimed) => {
            let (point, value) = checked_objective(
                model,
                &plan,
                plan.objective.as_ref()?,
                &assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Optimal {
                value,
                model_values: point,
            })
        }
        PbCdclResult::Unknown => None,
        // The result enum is non-exhaustive.  A future result kind receives no
        // accidental authority at this boundary.
        _ => None,
    };
    if let Some(ref decision) = decision {
        if trace_enabled() {
            let verdict = match decision {
                PbRouteDecision::Feasible { .. } => "FEASIBLE",
                PbRouteDecision::Infeasible
                | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => "INFEASIBLE",
                PbRouteDecision::Optimal { .. } => "OPTIMAL",
            };
            eprintln!(
                "AY_MILP_TRACE pb-generic-trial: engine=pb-cdcl vars={} constraints={} objective={} \
                 verdict={verdict} wall={:.6}s",
                plan.num_vars,
                plan.num_constraints,
                plan.objective.is_some(),
                started.elapsed().as_secs_f64(),
            );
        }
    }
    decision
}

/// Select the wall slice for one production PB-portfolio trial.
///
/// The dense class uses integer duration arithmetic (`remaining / 3 * 2`), so
/// its deadline can never consume more than two thirds of a finite caller
/// budget.  Overflow in `Instant` arithmetic declines the optional route.
fn portfolio_trial_deadline(
    ownership: PortfolioTrialOwnership,
    outer_deadline: Option<Instant>,
    now: Instant,
    translation: Option<Duration>,
) -> Option<Instant> {
    // `translation` is `None` at the ADMISSION call, which runs before there is
    // a plan to measure; there the historical deadline slice still applies,
    // bounded by the same cap. Once translation has been paid its cost becomes
    // the unit for an unrecognised model. See `generic_trial_slice`.
    let (cap, slice) = match (ownership, outer_deadline) {
        (PortfolioTrialOwnership::Generic, Some(outer)) => (
            GENERIC_PORTFOLIO_TRIAL_CAP,
            translation.map_or_else(
                || outer.saturating_duration_since(now) / 10,
                |paid| generic_trial_slice(paid).min(outer.saturating_duration_since(now)),
            ),
        ),
        (PortfolioTrialOwnership::DenseBooleanOptimization, Some(outer)) => (
            DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP,
            (outer.saturating_duration_since(now) / 3) * 2,
        ),
        (PortfolioTrialOwnership::Generic, None) => (
            GENERIC_PORTFOLIO_TRIAL_CAP,
            translation.map_or(GENERIC_PORTFOLIO_TRIAL_CAP, generic_trial_slice),
        ),
        (PortfolioTrialOwnership::DenseBooleanOptimization, None) => (
            DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP,
            DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP,
        ),
    };
    let deadline = now.checked_add(slice.min(cap))?;
    let deadline = outer_deadline.map_or(deadline, |outer| deadline.min(outer));
    (deadline > now).then_some(deadline)
}

/// Classify only a translated, identity-lifted Boolean optimization problem.
///
/// This intentionally runs *after* exact PB translation.  Consequently a
/// non-Boolean domain, arithmetic overflow, unsupported continuous lift, or
/// translation deadline can never buy the expanded slice.  The range and
/// density gates cover the dense 48--128 variable PB band without granting
/// ownership to the sparse set-covering/packing models that dominate MIPLIB.
fn portfolio_trial_ownership(plan: &PbRoutePlan) -> PortfolioTrialOwnership {
    let Some(objective) = plan.objective.as_ref() else {
        return PortfolioTrialOwnership::Generic;
    };
    if plan.eliminated_continuous != 0
        || plan.encoded_general_integers != 0
        || !(DENSE_BOOLEAN_MIN_VARS..=DENSE_BOOLEAN_MAX_VARS).contains(&plan.num_vars)
        || plan.constraints.len() != plan.num_constraints as usize
        || !(DENSE_BOOLEAN_MIN_ROWS..=DENSE_BOOLEAN_MAX_ROWS).contains(&plan.constraints.len())
        || plan.constraints.iter().any(|row| row.terms.is_empty())
    {
        return PortfolioTrialOwnership::Generic;
    }

    // `translate_objective` emits at most one term per source column.  Requiring
    // half the variables to participate rejects constant/tiny objectives.
    let Some(objective_support_twice) = objective.terms.len().checked_mul(2) else {
        return PortfolioTrialOwnership::Generic;
    };
    if objective_support_twice < plan.num_vars as usize {
        return PortfolioTrialOwnership::Generic;
    }

    let Some(term_occurrences) = plan
        .constraints
        .iter()
        .try_fold(0usize, |count, row| count.checked_add(row.terms.len()))
    else {
        return PortfolioTrialOwnership::Generic;
    };
    let Some(dense_cells) = (plan.num_vars as usize).checked_mul(plan.constraints.len()) else {
        return PortfolioTrialOwnership::Generic;
    };
    let Some(term_occurrences_twice) = term_occurrences.checked_mul(2) else {
        return PortfolioTrialOwnership::Generic;
    };
    if term_occurrences_twice < dense_cells {
        return PortfolioTrialOwnership::Generic;
    }

    PortfolioTrialOwnership::DenseBooleanOptimization
}

/// Production ownership wrapper for AY's exact PB portfolio.
///
/// Translation first receives the existing generic admission slice.  A plan
/// that translates exactly and matches [`portfolio_trial_ownership`] may then
/// extend search to its structural budget, reusing that same plan rather than
/// translating a second time.  Every other model gets the historical 500 ms /
/// one-tenth trial, after which the caller continues native MILP under the same
/// outer deadline.
pub(crate) fn try_solve_production_portfolio(
    model: &Model,
    outer_deadline: Option<Instant>,
    workers: Option<NonZeroUsize>,
) -> Option<PbRouteDecision> {
    let started = Instant::now();
    let admission_deadline = portfolio_trial_deadline(
        PortfolioTrialOwnership::Generic,
        outer_deadline,
        started,
        None,
    )?;
    let plan = translate(model, Some(admission_deadline));
    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE pb-portfolio-admission: translate={:.6}s outcome={}",
            started.elapsed().as_secs_f64(),
            match &plan {
                Ok(_) => "plan",
                Err(_) => "declined",
            },
        );
    }
    let plan = plan.ok()?;
    if deadline_reached(Some(admission_deadline)) || !compact_plan_admitted(&plan) {
        return None;
    }
    // The exact wall this model cost to represent — the unit an unrecognised
    // model's speculative slice is denominated in.
    let translation = started.elapsed();
    let ownership = portfolio_trial_ownership(&plan);
    let trial_deadline =
        portfolio_trial_deadline(ownership, outer_deadline, started, Some(translation))?;
    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE pb-portfolio-policy: class={} workers={} budget={:.6}s",
            ownership.trace_name(),
            workers.map_or(1, NonZeroUsize::get),
            trial_deadline
                .saturating_duration_since(started)
                .as_secs_f64(),
        );
    }
    try_solve_translated_portfolio_trial(model, plan, trial_deadline, workers, || false, started)
}

/// Try AY's complete PB portfolio under a caller-owned absolute trial deadline.
///
/// This is deliberately separate from [`try_solve_specialized`].  The latter is
/// a cheap production specialization; this entry point may enter general PB
/// search and therefore requires an explicit bounded slice.  It uses
/// `ay-pb-core`, not the `ay-pb` facade, so an embedded MILP solve can never
/// recurse through the facade's PB-to-MILP optimum-upgrade arm.
#[allow(dead_code)]
pub(crate) fn try_solve_portfolio_trial(
    model: &Model,
    trial_deadline: Instant,
) -> Option<PbRouteDecision> {
    try_solve_portfolio_trial_interruptible_with_schedule(model, trial_deadline, None, || false)
}

/// Try directly-derived structural block swaps before falling back to the
/// generic verified block detector, reporting whether the augmented optimizer
/// actually consumed the caller-owned slice.
///
/// This entry point is reserved for a caller that has already exposed a compact
/// structural formulation (currently the eager Hoffman network master). Every
/// emitted lex row comes from a permutation checked exactly against the
/// complete PB row multiset and objective. The optimizer's assignment is then
/// rechecked against both the unaugmented PB plan and the source rational
/// model, so the symmetry device can reduce search only; it cannot define a
/// verdict or witness.
///
/// `model_column_candidates` use zero-based source-model column ids. Exact PB
/// translation expands bounded-integer swaps through their radix bits, and the
/// core independently verifies every resulting permutation against the full PB
/// constraint multiset and objective. A failed translation or verification
/// retains the established generic detector as a bounded fallback.
pub(crate) fn try_solve_verified_block_symmetry_candidates_attempt(
    model: &Model,
    model_column_candidates: &[BTreeMap<u32, u32>],
    trial_deadline: Instant,
) -> VerifiedBlockSymmetryAttempt {
    try_solve_verified_block_symmetry_trial_with_candidates(
        model,
        model_column_candidates,
        trial_deadline,
    )
}

fn try_solve_verified_block_symmetry_trial_with_candidates(
    model: &Model,
    model_column_candidates: &[BTreeMap<u32, u32>],
    trial_deadline: Instant,
) -> VerifiedBlockSymmetryAttempt {
    let started = Instant::now();
    if deadline_reached(Some(trial_deadline)) {
        return VerifiedBlockSymmetryAttempt::Declined;
    }
    let plan = match translate(model, Some(trial_deadline)) {
        Ok(plan) => plan,
        Err(_) => return VerifiedBlockSymmetryAttempt::Declined,
    };
    if !compact_plan_admitted(&plan) {
        return VerifiedBlockSymmetryAttempt::Declined;
    }
    if deadline_reached(Some(trial_deadline)) {
        return VerifiedBlockSymmetryAttempt::Declined;
    }
    let Some((instance, objective)) = build_core_instance(&plan) else {
        return VerifiedBlockSymmetryAttempt::Declined;
    };
    let Some(objective) = objective.as_ref() else {
        return VerifiedBlockSymmetryAttempt::Declined;
    };

    let detect_started = Instant::now();
    let pb_candidates = model_column_candidates
        .iter()
        .filter_map(|candidate| plan.lift_model_column_permutation_to_pb(candidate))
        .collect::<Vec<_>>();
    let structural = if pb_candidates.is_empty() {
        None
    } else {
        let Some(verification_ceiling) =
            Instant::now().checked_add(BLOCK_SYMMETRY_CANDIDATE_VERIFICATION_CAP)
        else {
            return VerifiedBlockSymmetryAttempt::Declined;
        };
        let verification_deadline = trial_deadline.min(verification_ceiling);
        Some(
            ay_pb_core::break_verified_candidate_symmetries_with_deadline(
                &instance,
                &pb_candidates,
                Some(verification_deadline),
            ),
        )
    };
    let structural_changed = structural
        .as_ref()
        .is_some_and(|(_, result)| result.changed_instance());
    let (augmented, symmetry) = if let Some(result) =
        structural.filter(|(_, result)| result.changed_instance())
    {
        result
    } else {
        let Some(detect_ceiling) = Instant::now().checked_add(BLOCK_SYMMETRY_DETECTION_CAP) else {
            return VerifiedBlockSymmetryAttempt::Declined;
        };
        let detect_deadline = trial_deadline.min(detect_ceiling);
        ay_pb_core::break_verified_block_symmetries_with_deadline(&instance, Some(detect_deadline))
    };
    let detect_wall = detect_started.elapsed();
    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE pb-block-symmetry-source: model-candidates={} pb-candidates={} path={}",
            model_column_candidates.len(),
            pb_candidates.len(),
            if structural_changed {
                "structural-exact"
            } else {
                "generic-fallback"
            },
        );
    }
    let Some(auxiliary_variables) = u32::try_from(symmetry.lex_auxiliary_variables_added).ok()
    else {
        return VerifiedBlockSymmetryAttempt::Declined;
    };
    let Some(expected_augmented_vars) = instance.num_vars.checked_add(auxiliary_variables) else {
        return VerifiedBlockSymmetryAttempt::Declined;
    };
    let Some(expected_augmented_constraints) = instance
        .constraints
        .len()
        .checked_add(symmetry.lex_constraints_added)
    else {
        return VerifiedBlockSymmetryAttempt::Declined;
    };
    if instance.num_vars != plan.num_vars
        || augmented.num_vars != expected_augmented_vars
        || augmented.constraints.len() != expected_augmented_constraints
        || usize::try_from(augmented.num_constraints).ok() != Some(augmented.constraints.len())
    {
        if trace_enabled() {
            eprintln!(
                "AY_MILP_TRACE pb-block-symmetry: generators={} sequential-generators={} \
                 lex-rows={} lex-aux-vars={} source-vars={} augmented-vars={} \
                 verdict=INVALID-AUGMENTATION detect={:.6}s wall={:.6}s",
                symmetry.vector_transposition_generators,
                symmetry.sequential_lex_generators,
                symmetry.lex_constraints_added,
                symmetry.lex_auxiliary_variables_added,
                instance.num_vars,
                augmented.num_vars,
                detect_wall.as_secs_f64(),
                started.elapsed().as_secs_f64(),
            );
        }
        return VerifiedBlockSymmetryAttempt::Declined;
    }
    if !compact_core_instance_admitted(&augmented) {
        if trace_enabled() {
            eprintln!(
                "AY_MILP_TRACE pb-block-symmetry: generators={} sequential-generators={} \
                 lex-rows={} lex-aux-vars={} source-vars={} augmented-vars={} \
                 constraints={} verdict=DECLINED-AUGMENTED-ENVELOPE detect={:.6}s wall={:.6}s",
                symmetry.vector_transposition_generators,
                symmetry.sequential_lex_generators,
                symmetry.lex_constraints_added,
                symmetry.lex_auxiliary_variables_added,
                instance.num_vars,
                augmented.num_vars,
                augmented.constraints.len(),
                detect_wall.as_secs_f64(),
                started.elapsed().as_secs_f64(),
            );
        }
        return VerifiedBlockSymmetryAttempt::Declined;
    }
    let augmentation_admitted = symmetry.changed_instance();
    let admission_deadline_reached = deadline_reached(Some(trial_deadline));
    if !augmentation_admitted || admission_deadline_reached {
        if trace_enabled() {
            eprintln!(
                "AY_MILP_TRACE pb-block-symmetry: generators={} sequential-generators={} \
                 lex-rows={} lex-aux-vars={} source-vars={} augmented-vars={} \
                 verdict={} detect={:.6}s wall={:.6}s",
                symmetry.vector_transposition_generators,
                symmetry.sequential_lex_generators,
                symmetry.lex_constraints_added,
                symmetry.lex_auxiliary_variables_added,
                instance.num_vars,
                augmented.num_vars,
                if augmentation_admitted {
                    "ADMITTED-DEADLINE"
                } else {
                    "DECLINED"
                },
                detect_wall.as_secs_f64(),
                started.elapsed().as_secs_f64(),
            );
        }
        return if augmentation_admitted {
            VerifiedBlockSymmetryAttempt::Admitted(None)
        } else {
            VerifiedBlockSymmetryAttempt::Declined
        };
    }

    let (lex_width, lex_coefficient_bits, source_coefficient_bits, augmented_coefficient_bits) =
        if trace_enabled() {
            let coefficient_bits = |constraints: &[PbConstraint], objective: &PbObjective| {
                constraints
                    .iter()
                    .flat_map(|constraint| &constraint.terms)
                    .chain(&objective.terms)
                    .map(|term| term.coeff.unsigned_abs())
                    .max()
                    .map_or(0, |coefficient| {
                        usize::try_from(u128::BITS - coefficient.leading_zeros())
                            .unwrap_or(usize::MAX)
                    })
            };
            let added = &augmented.constraints[instance.constraints.len()..];
            let bits = added
                .iter()
                .flat_map(|constraint| &constraint.terms)
                .map(|term| term.coeff.unsigned_abs())
                .max()
                .map_or(0, |coefficient| {
                    usize::try_from(u128::BITS - coefficient.leading_zeros()).unwrap_or(usize::MAX)
                });
            (
                symmetry.max_lex_coordinates,
                bits,
                coefficient_bits(&instance.constraints, objective),
                coefficient_bits(&augmented.constraints, objective),
            )
        } else {
            (0, 0, 0, 0)
        };

    let timeout = trial_deadline.saturating_duration_since(Instant::now());
    if timeout.is_zero() {
        return VerifiedBlockSymmetryAttempt::Admitted(None);
    }
    let term = AtomicBool::new(false);
    let solve_started = Instant::now();
    let mut ignore_improvement = |_: i128, _: &[bool]| {};
    let portfolio = solve_optimization_portfolio_with_timings(
        &augmented,
        objective,
        Some(timeout),
        solve_started,
        &term,
        &mut ignore_improvement,
    );
    let solution = portfolio.solution;
    let solve_wall = solve_started.elapsed();
    if deadline_reached(Some(trial_deadline)) {
        if trace_enabled() {
            eprintln!(
                "AY_MILP_TRACE pb-block-symmetry: generators={} sequential-generators={} \
                 lex-rows={} lex-aux-vars={} lex-width={} lex-coeff-bits={} \
                 source-coeff-bits={} augmented-coeff-bits={} \
                 source-vars={} augmented-vars={} solver-status={:?} verdict=DEADLINE \
                 portfolio-pre-native-ms={} portfolio-native-ms={} portfolio-sat-ms={} \
                 portfolio-lns-ms={} detect={:.6}s solve={:.6}s wall={:.6}s",
                symmetry.vector_transposition_generators,
                symmetry.sequential_lex_generators,
                symmetry.lex_constraints_added,
                symmetry.lex_auxiliary_variables_added,
                lex_width,
                lex_coefficient_bits,
                source_coefficient_bits,
                augmented_coefficient_bits,
                instance.num_vars,
                augmented.num_vars,
                solution.status,
                portfolio.timings.pre_native_sat_ms,
                portfolio.timings.native_ms,
                portfolio.timings.sat_ms,
                portfolio.timings.lns_ms,
                detect_wall.as_secs_f64(),
                solve_wall.as_secs_f64(),
                started.elapsed().as_secs_f64(),
            );
        }
        return VerifiedBlockSymmetryAttempt::Admitted(None);
    }
    if !solution.assignment.is_empty()
        && (solution.assignment.len() < augmented.num_vars as usize
            || !ay_pb_core::verify_all_constraints(&augmented.constraints, &solution.assignment)
            || !ay_pb_core::verify_all_constraints(&instance.constraints, &solution.assignment)
            || !plan.satisfies(&solution.assignment))
    {
        return VerifiedBlockSymmetryAttempt::Admitted(None);
    }

    let decision = (|| match solution.status {
        // The exact automorphism check plus lex-leader theorem makes the
        // augmented model equisatisfiable with the source PB model.
        PbStatus::Unsatisfiable => Some(PbRouteDecision::Infeasible),
        PbStatus::Satisfiable => {
            let objective_plan = plan.objective.as_ref()?;
            let claimed = objective_plan.value_at(&solution.assignment)?;
            let (point, _) = checked_objective(
                model,
                &plan,
                objective_plan,
                &solution.assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: true,
            })
        }
        PbStatus::OptimumFound => {
            let objective_plan = plan.objective.as_ref()?;
            let claimed = solution.objective?;
            let (point, value) = checked_objective(
                model,
                &plan,
                objective_plan,
                &solution.assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Optimal {
                value,
                model_values: point,
            })
        }
        PbStatus::Unknown | PbStatus::Unsupported => None,
    })();
    if trace_enabled() {
        let verdict = match &decision {
            Some(PbRouteDecision::Feasible { .. }) => "FEASIBLE",
            Some(
                PbRouteDecision::Infeasible
                | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                | PbRouteDecision::CertifiedMultiRowInfeasible { .. },
            ) => "INFEASIBLE",
            Some(PbRouteDecision::Optimal { .. }) => "OPTIMAL",
            None => "DECLINED",
        };
        eprintln!(
            "AY_MILP_TRACE pb-block-symmetry: generators={} sequential-generators={} \
             lex-rows={} lex-aux-vars={} lex-width={} lex-coeff-bits={} \
             source-coeff-bits={} augmented-coeff-bits={} source-vars={} augmented-vars={} \
             constraints={} verdict={} portfolio-pre-native-ms={} portfolio-native-ms={} \
             portfolio-sat-ms={} portfolio-lns-ms={} detect={:.6}s solve={:.6}s wall={:.6}s",
            symmetry.vector_transposition_generators,
            symmetry.sequential_lex_generators,
            symmetry.lex_constraints_added,
            symmetry.lex_auxiliary_variables_added,
            lex_width,
            lex_coefficient_bits,
            source_coefficient_bits,
            augmented_coefficient_bits,
            instance.num_vars,
            augmented.num_vars,
            augmented.constraints.len(),
            verdict,
            portfolio.timings.pre_native_sat_ms,
            portfolio.timings.native_ms,
            portfolio.timings.sat_ms,
            portfolio.timings.lns_ms,
            detect_wall.as_secs_f64(),
            solve_wall.as_secs_f64(),
            started.elapsed().as_secs_f64(),
        );
    }
    VerifiedBlockSymmetryAttempt::Admitted(decision)
}

/// Try the complete PB optimization portfolio with an explicit worker budget.
///
/// This is the production-safe foundation for an embedding solver's typed
/// `threads` policy.  Unlike the standalone PB binary's automatic parallel
/// route, it consults no process environment at all — neither ay-pb-core's own
/// parallel switch (see `ay-pb-core/src/portfolio.rs`) nor `NBCORE`; the caller
/// has already resolved the worker envelope.  The switch is named there rather
/// than here so `tests/env_ledger.rs` does not read a cross-crate name out of
/// ay-milp prose and demand `ay-milp knobs --list` advertise a switch this
/// crate never reads.  Decision models retain the serial
/// path because this seam is intended for optimization and because a feasible
/// decision assignment needs no portfolio race.  All exact translation,
/// result sanitization, lifted-point checking, and model-objective checking are
/// shared with [`try_solve_portfolio_trial`].
pub(crate) fn try_solve_portfolio_trial_with_workers(
    model: &Model,
    trial_deadline: Instant,
    workers: NonZeroUsize,
) -> Option<PbRouteDecision> {
    try_solve_portfolio_trial_interruptible_with_schedule(
        model,
        trial_deadline,
        Some(workers),
        || false,
    )
}

/// Interruptible form of [`try_solve_portfolio_trial`].
#[allow(dead_code)]
pub(crate) fn try_solve_portfolio_trial_interruptible<F>(
    model: &Model,
    trial_deadline: Instant,
    should_stop: F,
) -> Option<PbRouteDecision>
where
    F: FnMut() -> bool,
{
    try_solve_portfolio_trial_interruptible_with_schedule(model, trial_deadline, None, should_stop)
}

fn try_solve_portfolio_trial_interruptible_with_schedule<F>(
    model: &Model,
    trial_deadline: Instant,
    workers: Option<NonZeroUsize>,
    mut should_stop: F,
) -> Option<PbRouteDecision>
where
    F: FnMut() -> bool,
{
    let started = Instant::now();
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }
    let plan = translate(model, Some(trial_deadline)).ok()?;
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }
    try_solve_translated_portfolio_trial(model, plan, trial_deadline, workers, should_stop, started)
}

fn try_solve_translated_portfolio_trial<F>(
    model: &Model,
    plan: PbRoutePlan,
    trial_deadline: Instant,
    workers: Option<NonZeroUsize>,
    mut should_stop: F,
    started: Instant,
) -> Option<PbRouteDecision>
where
    F: FnMut() -> bool,
{
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }
    // General PB search retains multiple solver representations.  Keep this
    // embedded trial on the compact class for which a bounded prefix is useful;
    // larger translations remain entirely with native MILP rather than paying
    // an avoidable in-process memory spike before the external RSS guard can
    // intervene.
    if !compact_plan_admitted(&plan) {
        return None;
    }
    let (instance, objective) = build_core_instance(&plan)?;
    let instance = if workers.is_some() {
        PortfolioTrialInstance::Parallel(Arc::new(instance))
    } else {
        PortfolioTrialInstance::Serial(instance)
    };
    let timeout = trial_deadline.saturating_duration_since(Instant::now());
    if timeout.is_zero() {
        return None;
    }

    // The portfolio owns its wall deadline.  An arbitrary caller callback need
    // not be Send, so it is polled immediately around the synchronous call; a
    // completed answer is discarded if cancellation arrived meanwhile.
    let term = AtomicBool::new(false);
    let start = Instant::now();
    let solution = match (objective.as_ref(), workers) {
        (Some(objective), Some(workers)) => {
            let Some(shared) = instance.as_parallel() else {
                return None;
            };
            let mut ignore_improvement = |_: i128, _: &[bool]| {};
            solve_optimization_portfolio_parallel_with_workers(
                shared,
                objective,
                Some(timeout),
                start,
                &term,
                &mut ignore_improvement,
                workers,
            )
        }
        (Some(objective), None) => {
            let mut ignore_improvement = |_: i128, _: &[bool]| {};
            solve_optimization_portfolio(
                instance.as_instance(),
                objective,
                Some(timeout),
                start,
                &term,
                &mut ignore_improvement,
            )
        }
        (None, _) => solve_decision_portfolio(instance.as_instance(), Some(timeout), start, &term),
    };
    if deadline_reached(Some(trial_deadline)) || should_stop() {
        return None;
    }

    let assignment = &solution.assignment;
    if !assignment.is_empty()
        && (assignment.len() < plan.num_vars as usize
            || !ay_pb_core::verify_all_constraints(&instance.as_instance().constraints, assignment)
            || !plan.satisfies(assignment))
    {
        return None;
    }
    let decision = match solution.status {
        PbStatus::Unsatisfiable => {
            let certificate_result = generate_multi_row_bdd_infeasibility_certificate_interruptible(
                instance.as_instance(),
                || deadline_reached(Some(trial_deadline)) || should_stop(),
            );
            map_multi_row_infeasibility_certificate_result(certificate_result)
        }
        PbStatus::Satisfiable if objective.is_none() => {
            let point = checked_point(model, &plan, assignment, Some(trial_deadline))?;
            Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: false,
            })
        }
        PbStatus::Satisfiable => {
            let objective_plan = plan.objective.as_ref()?;
            let claimed = objective_plan.value_at(assignment)?;
            let (point, _) = checked_objective(
                model,
                &plan,
                objective_plan,
                assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Feasible {
                model_values: point,
                incumbent_only: true,
            })
        }
        PbStatus::OptimumFound => {
            let objective_plan = plan.objective.as_ref()?;
            let claimed = solution.objective?;
            let (point, value) = checked_objective(
                model,
                &plan,
                objective_plan,
                assignment,
                claimed,
                Some(trial_deadline),
            )?;
            Some(PbRouteDecision::Optimal {
                value,
                model_values: point,
            })
        }
        PbStatus::Unknown | PbStatus::Unsupported => None,
    };
    if let Some(PbRouteDecision::CertifiedMultiRowInfeasible { certificate }) = &decision {
        if verify_multi_row_infeasibility_certificate_with_deadline(
            model,
            certificate,
            Some(trial_deadline),
        )
        .is_err()
        {
            return None;
        }
    }
    if trace_enabled() {
        let verdict = match &decision {
            Some(PbRouteDecision::Feasible { .. }) => "FEASIBLE",
            Some(
                PbRouteDecision::Infeasible
                | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                | PbRouteDecision::CertifiedMultiRowInfeasible { .. },
            ) => "INFEASIBLE",
            Some(PbRouteDecision::Optimal { .. }) => "OPTIMAL",
            None => "DECLINED",
        };
        eprintln!(
            "AY_MILP_TRACE pb-portfolio-trial: vars={} constraints={} verdict={} wall={:.6}s",
            plan.num_vars,
            plan.num_constraints,
            verdict,
            started.elapsed().as_secs_f64(),
        );
    }
    decision
}

fn compact_plan_admitted(plan: &PbRoutePlan) -> bool {
    let Some(terms) = plan
        .constraints
        .iter()
        .try_fold(0usize, |count, row| count.checked_add(row.terms.len()))
    else {
        return false;
    };
    portfolio_trial_counts_admitted(plan.num_vars, plan.constraints.len(), terms)
}

/// Re-apply the compact portfolio envelope after an optional transformation.
/// A source plan at the admission boundary cannot acquire unbudgeted variables,
/// rows, or term occurrences through symmetry auxiliaries.
fn compact_core_instance_admitted(instance: &PbInstance) -> bool {
    let Some(terms) = instance
        .constraints
        .iter()
        .try_fold(0usize, |count, row| count.checked_add(row.terms.len()))
    else {
        return false;
    };
    portfolio_trial_counts_admitted(instance.num_vars, instance.constraints.len(), terms)
}

fn portfolio_trial_counts_admitted(num_vars: u32, constraints: usize, terms: usize) -> bool {
    num_vars <= MAX_PORTFOLIO_TRIAL_VARS
        && constraints <= MAX_PORTFOLIO_TRIAL_CONSTRAINTS
        && terms <= MAX_PORTFOLIO_TRIAL_TERMS
}

fn build_core_instance(plan: &PbRoutePlan) -> Option<(PbInstance, Option<PbObjective>)> {
    let constraints = plan
        .constraints
        .iter()
        .map(|row| {
            let terms = row
                .terms
                .iter()
                .map(|&(column, coeff)| {
                    Some(PbTerm {
                        coeff,
                        lits: vec![PbLit {
                            var: column.checked_add(1)?,
                            negated: false,
                        }],
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: row.rhs,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    if constraints.len() != plan.num_constraints as usize {
        return None;
    }

    let objective = match plan.objective.as_ref() {
        Some(objective) => {
            let terms = objective
                .terms
                .iter()
                .map(|&(column, coeff)| {
                    Some(PbTerm {
                        coeff,
                        lits: vec![PbLit {
                            var: column.checked_add(1)?,
                            negated: false,
                        }],
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some(PbObjective { terms })
        }
        None => None,
    };

    let instance = PbInstance {
        num_vars: plan.num_vars,
        num_constraints: plan.num_constraints,
        constraints,
        objective: objective.clone(),
    };
    Some((instance, objective))
}

/// Independently rebuild the exact PB projection of `model` and replay an
/// exported single-row infeasibility artifact against that rebuilt instance.
/// The artifact's embedded canonical row/objective is never trusted to define
/// what is being proved.
pub fn verify_single_row_infeasibility_certificate(
    model: &Model,
    certificate: &SingleRowDpInfeasibilityCertificate,
) -> Result<(), String> {
    verify_single_row_infeasibility_certificate_with_deadline(model, certificate, None)
}

/// Deadline-aware model-bound replay for a single-row proof artifact.
pub(crate) fn verify_single_row_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &SingleRowDpInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    if deadline_reached(deadline) {
        return Err("single-row DP proof replay deadline expired".to_owned());
    }
    let plan = translate(model, deadline)
        .map_err(|reason| format!("exact MILP-to-PB translation declined: {reason:?}"))?;
    let (instance, _) = build_core_instance(&plan)
        .ok_or_else(|| "exact PB instance reconstruction failed".to_owned())?;
    verify_single_row_dp_infeasibility_certificate_interruptible(&instance, certificate, || {
        deadline_reached(deadline)
    })
    .map_err(|reason| format!("single-row DP proof replay failed: {reason:?}"))
}

/// Independently rebuild the exact PB projection of `model` and replay a
/// general multi-row residual-state decision DAG against that rebuilt instance.
/// Neither the route's earlier translation nor any implicit generator state is
/// trusted by this certificate boundary.
pub fn verify_multi_row_infeasibility_certificate(
    model: &Model,
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Result<(), String> {
    verify_multi_row_infeasibility_certificate_with_deadline(model, certificate, None)
}

/// Deadline-aware model-bound replay for a multi-row decision-DAG artifact.
pub(crate) fn verify_multi_row_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &MultiRowBddInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    if deadline_reached(deadline) {
        return Err("multi-row BDD proof replay deadline expired".to_owned());
    }
    let plan = translate(model, deadline)
        .map_err(|reason| format!("exact MILP-to-PB translation declined: {reason:?}"))?;
    let (instance, _) = build_core_instance(&plan)
        .ok_or_else(|| "exact PB instance reconstruction failed".to_owned())?;
    verify_multi_row_bdd_infeasibility_certificate_interruptible(&instance, certificate, || {
        deadline_reached(deadline)
    })
    .map_err(|reason| format!("multi-row BDD proof replay failed: {reason:?}"))
}

/// Generate an independently replayable refutation of every assignment whose
/// transformed PB objective is strictly better than `claimed_model_value`.
///
/// The exact objective translator always maps the caller's min/max problem to
/// minimization of an integer PB expression.  Consequently strict improvement
/// is exactly `pb <= p - 1`, with no epsilon or coefficient-gcd assumption.
/// The returned decision DAG proves that face empty; the primal point attaining
/// the claimed value remains a separate witness obligation.
pub(crate) fn try_prove_objective_bound(
    model: &Model,
    claimed_model_value: &BigRational,
    deadline: Instant,
) -> Option<MultiRowBddInfeasibilityCertificate> {
    let (certificate, instance) =
        generate_objective_bound_certificate(model, claimed_model_value, deadline)?;
    verify_multi_row_bdd_infeasibility_certificate_interruptible(&instance, &certificate, || {
        deadline_reached(Some(deadline))
    })
    .ok()?;
    Some(certificate)
}

/// Generate and serialize a strict-objective-face refutation for the network
/// route. The caller must perform the independently rebuilt source-bound replay;
/// this helper deliberately does not trust or re-verify the producing master.
pub(crate) fn try_generate_network_objective_bound_certificate(
    model: &Model,
    claimed_model_value: &BigRational,
    deadline: Instant,
) -> Option<MultiRowBddInfeasibilityCertificate> {
    generate_objective_bound_certificate(model, claimed_model_value, deadline)
        .map(|(certificate, _)| certificate)
}

fn generate_objective_bound_certificate(
    model: &Model,
    claimed_model_value: &BigRational,
    deadline: Instant,
) -> Option<(MultiRowBddInfeasibilityCertificate, PbInstance)> {
    let instance = build_strict_improvement_instance(model, claimed_model_value, Some(deadline))?;
    let certificate =
        generate_multi_row_bdd_infeasibility_certificate_interruptible(&instance, || {
            deadline_reached(Some(deadline))
        })
        .ok()??;
    if deadline_reached(Some(deadline)) {
        return None;
    }
    encode_multi_row_bdd_infeasibility_certificate_json(&certificate).ok()?;
    if deadline_reached(Some(deadline)) {
        return None;
    }
    Some((certificate, instance))
}

/// Rebuild the exact objective projection and replay a strict-better-face
/// refutation.  Neither the artifact's embedded PB rows nor solver state define
/// the optimization claim.
pub(crate) fn verify_objective_bound(
    model: &Model,
    claimed_model_value: &BigRational,
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Result<(), String> {
    verify_objective_bound_with_deadline(model, claimed_model_value, certificate, None)
}

pub(crate) fn verify_objective_bound_with_deadline(
    model: &Model,
    claimed_model_value: &BigRational,
    certificate: &MultiRowBddInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    let instance = build_strict_improvement_instance(model, claimed_model_value, deadline)
        .ok_or_else(|| "exact strict-improvement PB reconstruction failed".to_owned())?;
    verify_multi_row_bdd_infeasibility_certificate_interruptible(&instance, certificate, || {
        deadline_reached(deadline)
    })
    .map_err(|reason| format!("objective-bound BDD proof replay failed: {reason:?}"))
}

fn build_strict_improvement_instance(
    model: &Model,
    claimed_model_value: &BigRational,
    deadline: Option<Instant>,
) -> Option<PbInstance> {
    if deadline_reached(deadline) {
        return None;
    }
    let plan = translate(model, deadline).ok()?;
    if !compact_plan_admitted(&plan) {
        return None;
    }
    let objective = plan.objective.as_ref()?;
    let claimed_pb_value = objective.map.pb_value(claimed_model_value)?;
    let (cutoff, terms) = if claimed_pb_value == i128::MIN {
        // Translation preflights the complete objective range in `i128`, so a
        // value below MIN is impossible independently of the model rows.
        (
            PbInequality {
                terms: Vec::new(),
                rhs: 1,
            },
            Vec::new(),
        )
    } else {
        let terms = objective
            .terms
            .iter()
            .map(|&(column, coefficient)| {
                Some(PbTerm {
                    coeff: coefficient.checked_neg()?,
                    lits: vec![PbLit {
                        var: column.checked_add(1)?,
                        negated: false,
                    }],
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let rhs = 1i128.checked_sub(claimed_pb_value)?;
        let cutoff = PbInequality {
            terms: objective
                .terms
                .iter()
                .map(|&(column, coefficient)| Some((column, coefficient.checked_neg()?)))
                .collect::<Option<Vec<_>>>()?,
            rhs,
        };
        (cutoff, terms)
    };
    if !crate::pb_translate::pb_core_row_range_fits_for_certificate(&cutoff) {
        return None;
    }
    let (mut instance, _) = build_core_instance(&plan)?;
    instance.constraints.push(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: cutoff.rhs,
    });
    instance.num_constraints = instance.num_constraints.checked_add(1)?;
    if deadline_reached(deadline) {
        return None;
    }
    Some(instance)
}

fn checked_point(
    model: &Model,
    plan: &PbRoutePlan,
    assignment: &[bool],
    deadline: Option<Instant>,
) -> Option<Vec<BigRational>> {
    if deadline_reached(deadline) || !plan.satisfies(assignment) {
        return None;
    }
    let point = plan.lift(assignment)?;
    if model.check_point(&point).is_err() || deadline_reached(deadline) {
        return None;
    }
    Some(point)
}

fn checked_objective(
    model: &Model,
    plan: &PbRoutePlan,
    objective: &PbObjectivePlan,
    assignment: &[bool],
    claimed: i128,
    deadline: Option<Instant>,
) -> Option<(Vec<BigRational>, BigRational)> {
    if objective.value_at(assignment)? != claimed {
        return None;
    }
    let point = checked_point(model, plan, assignment, deadline)?;
    let value = objective.map.model_value(claimed);
    if model.objective_value_at(&point) != value || deadline_reached(deadline) {
        return None;
    }
    Some((point, value))
}

fn deadline_reached(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

fn trace_enabled() -> bool {
    // Cached: the ratchet in `tests/env_ledger.rs` counts a bare `env::var_os`
    // on the solve path as a LIVE read — a fresh `getenv` a concurrent
    // `set_var` can race, which priming cannot help. `OnceLock` is the shape
    // that ratchet asks for and `simplex.rs` already uses.
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_MILP_TRACE").is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BabSession, Model, Outcome, Sense, SolveOpts};
    use num_bigint::BigInt;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    #[test]
    fn augmented_core_rechecks_the_complete_portfolio_envelope() {
        let row = PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let admitted = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![row],
            objective: None,
        };
        assert!(compact_core_instance_admitted(&admitted));

        let mut too_many_vars = admitted.clone();
        too_many_vars.num_vars = MAX_PORTFOLIO_TRIAL_VARS + 1;
        assert!(!compact_core_instance_admitted(&too_many_vars));
        assert!(portfolio_trial_counts_admitted(
            MAX_PORTFOLIO_TRIAL_VARS,
            MAX_PORTFOLIO_TRIAL_CONSTRAINTS,
            MAX_PORTFOLIO_TRIAL_TERMS,
        ));
        assert!(!portfolio_trial_counts_admitted(
            MAX_PORTFOLIO_TRIAL_VARS,
            MAX_PORTFOLIO_TRIAL_CONSTRAINTS + 1,
            MAX_PORTFOLIO_TRIAL_TERMS,
        ));
        assert!(!portfolio_trial_counts_admitted(
            MAX_PORTFOLIO_TRIAL_VARS,
            MAX_PORTFOLIO_TRIAL_CONSTRAINTS,
            MAX_PORTFOLIO_TRIAL_TERMS + 1,
        ));
    }

    fn translated_boolean_optimization(
        vars: usize,
        rows: usize,
        row_support: usize,
        objective_support: Option<usize>,
    ) -> PbRoutePlan {
        let mut model = Model::new();
        let columns: Vec<_> = (0..vars).map(|_| model.add_binary_col()).collect();
        let row_terms: Vec<_> = columns
            .iter()
            .take(row_support)
            .copied()
            .map(|column| (column, 1.0))
            .collect();
        for _ in 0..rows {
            model.add_row(f64::NEG_INFINITY, row_support as f64 / 2.0, &row_terms);
        }
        if let Some(support) = objective_support {
            let objective: Vec<_> = columns
                .iter()
                .take(support)
                .copied()
                .map(|column| (column, 1.0))
                .collect();
            model.set_objective(&objective, Sense::Maximize);
        }
        translate(&model, None).expect("synthetic Boolean model translates exactly")
    }

    #[test]
    fn dense_boolean_ownership_accepts_exact_boundary_shapes() {
        let lower = translated_boolean_optimization(48, 24, 24, Some(24));
        assert_eq!(
            portfolio_trial_ownership(&lower),
            PortfolioTrialOwnership::DenseBooleanOptimization
        );

        let upper = translated_boolean_optimization(128, 128, 64, Some(64));
        assert_eq!(
            portfolio_trial_ownership(&upper),
            PortfolioTrialOwnership::DenseBooleanOptimization
        );
    }

    #[test]
    fn dense_boolean_ownership_declines_nonmatching_shapes() {
        for plan in [
            translated_boolean_optimization(47, 24, 24, Some(24)),
            translated_boolean_optimization(129, 24, 65, Some(65)),
            translated_boolean_optimization(48, 23, 24, Some(24)),
            translated_boolean_optimization(48, 129, 24, Some(24)),
            translated_boolean_optimization(48, 24, 23, Some(24)),
            translated_boolean_optimization(48, 24, 24, Some(23)),
            translated_boolean_optimization(48, 24, 24, None),
        ] {
            assert_eq!(
                portfolio_trial_ownership(&plan),
                PortfolioTrialOwnership::Generic
            );
        }
    }

    #[test]
    fn dense_boolean_deadline_leaves_native_third_and_honours_cap() {
        let now = Instant::now();
        let sixty = now + Duration::from_secs(60);
        let deadline = portfolio_trial_deadline(
            PortfolioTrialOwnership::DenseBooleanOptimization,
            Some(sixty),
            now,
            None,
        )
        .expect("finite dense trial");
        assert_eq!(deadline, now + Duration::from_secs(40));
        assert!(sixty.duration_since(deadline) >= Duration::from_secs(20));

        let short_remaining = Duration::from_millis(100);
        let short_outer = now + short_remaining;
        let short = portfolio_trial_deadline(
            PortfolioTrialOwnership::DenseBooleanOptimization,
            Some(short_outer),
            now,
            None,
        )
        .expect("short dense trial");
        assert!(short_outer.duration_since(short) >= short_remaining / 3);

        let two_hundred = now + Duration::from_secs(200);
        let capped = portfolio_trial_deadline(
            PortfolioTrialOwnership::DenseBooleanOptimization,
            Some(two_hundred),
            now,
            None,
        )
        .expect("capped dense trial");
        assert_eq!(capped, now + DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP);
        assert!(two_hundred.duration_since(capped) >= Duration::from_secs(80));
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::DenseBooleanOptimization,
                None,
                now,
                None
            ),
            Some(now + DENSE_BOOLEAN_PORTFOLIO_TRIAL_CAP)
        );
    }

    #[test]
    fn strict_objective_face_artifact_proves_exact_bound_and_rejects_weaker_claim() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Minimize);

        let deadline = Instant::now() + Duration::from_secs(2);
        let certificate = try_prove_objective_bound(&model, &integer(1), deadline)
            .expect("nothing has objective below one");
        verify_objective_bound(&model, &integer(1), &certificate)
            .expect("strict-better proof replays");

        assert!(try_prove_objective_bound(
            &model,
            &integer(2),
            Instant::now() + Duration::from_secs(2)
        )
        .is_none());

        let mut corrupted = certificate;
        corrupted.format.push_str("-tampered");
        assert!(verify_objective_bound(&model, &integer(1), &corrupted).is_err());
    }

    /// An UNRECOGNISED model's speculative slice is denominated in what the
    /// model itself cost to represent, not in the caller's remaining patience.
    ///
    /// The regression this pins: every `Generic` model used to receive
    /// `min(500ms, deadline/10)` regardless of size, a flat prelude tax on
    /// models the native lane settles in tens of milliseconds.
    #[test]
    fn generic_slice_is_denominated_in_translation_not_in_the_caller_deadline() {
        let now = Instant::now();
        let hour = now + Duration::from_secs(3600);

        // Same enormous caller deadline, two models a factor apart in
        // representation cost => two different slices, both well under the old
        // flat 500 ms. Under the old rule both were the cap.
        let cheap = portfolio_trial_deadline(
            PortfolioTrialOwnership::Generic,
            Some(hour),
            now,
            Some(Duration::from_millis(3)),
        )
        .expect("a cheap model still gets a look");
        let dear = portfolio_trial_deadline(
            PortfolioTrialOwnership::Generic,
            Some(hour),
            now,
            Some(Duration::from_millis(12)),
        )
        .expect("a dearer model gets proportionally more");
        assert_eq!(cheap, now + Duration::from_millis(72));
        assert_eq!(dear, now + Duration::from_millis(288));
        assert!(dear > cheap, "the unit is the model, not the deadline");
        assert!(
            dear < now + GENERIC_PORTFOLIO_TRIAL_CAP,
            "both stay under the flat budget they replace"
        );

        // The historical cap still bounds it from above ...
        let huge = portfolio_trial_deadline(
            PortfolioTrialOwnership::Generic,
            Some(hour),
            now,
            Some(Duration::from_secs(1)),
        )
        .expect("a very large model is capped, not unbounded");
        assert_eq!(huge, now + GENERIC_PORTFOLIO_TRIAL_CAP);

        // ... a floor keeps a translation too fast to time from rounding the
        // trial below what the arm costs to START (measured 32.3 ms; see
        // `GENERIC_PORTFOLIO_TRIAL_FLOOR`) ...
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::Generic,
                Some(hour),
                now,
                Some(Duration::ZERO)
            ),
            Some(now + GENERIC_PORTFOLIO_TRIAL_FLOOR)
        );
        assert!(
            GENERIC_PORTFOLIO_TRIAL_FLOOR >= Duration::from_millis(33),
            "the floor must clear the arm's measured 32.3 ms start-up, or the \
             slice is spent on set-up and cut off before it can conclude"
        );

        // ... and the caller's deadline still wins when it is the tighter of
        // the two, so this can never extend a solve.
        let soon = now + Duration::from_millis(3);
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::Generic,
                Some(soon),
                now,
                Some(Duration::from_millis(5))
            ),
            Some(soon)
        );

        // The structurally-owned class is deliberately untouched.
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::DenseBooleanOptimization,
                Some(now + Duration::from_secs(60)),
                now,
                Some(Duration::from_micros(500))
            ),
            Some(now + Duration::from_secs(40))
        );
    }

    #[test]
    fn generic_deadline_retains_historical_short_fallback_posture() {
        let now = Instant::now();
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::Generic,
                Some(now + Duration::from_secs(60)),
                now,
                None
            ),
            Some(now + GENERIC_PORTFOLIO_TRIAL_CAP)
        );
        assert_eq!(
            portfolio_trial_deadline(
                PortfolioTrialOwnership::Generic,
                Some(now + Duration::from_millis(100)),
                now,
                None
            ),
            Some(now + Duration::from_millis(10))
        );
        assert_eq!(
            portfolio_trial_deadline(PortfolioTrialOwnership::Generic, Some(now), now, None),
            None
        );
        assert_eq!(
            portfolio_trial_deadline(PortfolioTrialOwnership::Generic, None, now, None),
            Some(now + GENERIC_PORTFOLIO_TRIAL_CAP)
        );
    }

    #[test]
    fn specialized_one_row_route_lifts_feasibility_exactly() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
        let decision = try_solve_specialized(&model, None).expect("single-row PB route");
        let PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } = decision
        else {
            panic!("expected feasible decision")
        };
        assert!(!incumbent_only);
        model
            .check_point(&model_values)
            .expect("route witness rechecks");
    }

    #[test]
    fn specialized_one_row_route_proves_infeasibility() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        assert!(matches!(
            try_solve_specialized(&model, None),
            Some(PbRouteDecision::CertifiedSingleRowInfeasible { .. })
        ));
    }

    #[test]
    fn specialized_decline_does_not_invoke_generic_pb_search() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        // These are two independent semantic rows, so the one-row DP must
        // decline.  Raw PB-CDCL can solve the same exact projection, making a
        // conclusive result here evidence that it was *not* called implicitly.
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(y, 1.0)]);

        assert!(try_solve_specialized(&model, None).is_none());

        let trial_deadline = Instant::now() + std::time::Duration::from_secs(5);
        let generic = try_solve_generic_trial(&model, trial_deadline)
            .expect("explicit generic PB trial should decide this tiny instance");
        let PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } = generic
        else {
            panic!("expected generic PB feasibility decision")
        };
        assert!(!incumbent_only);
        assert_eq!(model_values, vec![integer(1), integer(1)]);
        model
            .check_point(&model_values)
            .expect("generic trial witness rechecks");
    }

    #[test]
    fn direct_multi_row_route_exports_replayable_infeasibility_dag() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(y, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);

        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        let decision = try_prove_multi_row_infeasibility(&model, deadline)
            .expect("bounded multi-row proof route");
        let PbRouteDecision::CertifiedMultiRowInfeasible { certificate } = decision else {
            panic!("expected typed multi-row infeasibility proof")
        };
        verify_multi_row_infeasibility_certificate(&model, &certificate)
            .expect("proof rebuilds and replays against original MILP");

        let mut corrupted = certificate;
        corrupted.format.push_str(".corrupt");
        assert!(verify_multi_row_infeasibility_certificate(&model, &corrupted).is_err());
    }

    #[test]
    fn multi_row_export_disagreement_never_becomes_replay_authority() {
        assert!(map_multi_row_infeasibility_certificate_result(Ok(None)).is_none());
        assert!(map_multi_row_infeasibility_certificate_result(Err(
            MultiRowBddDecline::VerificationFailed
        ))
        .is_none());
        assert!(matches!(
            map_multi_row_infeasibility_certificate_result(Err(MultiRowBddDecline::ResourceLimit)),
            Some(PbRouteDecision::Infeasible)
        ));
        assert!(matches!(
            map_multi_row_infeasibility_certificate_result(Err(MultiRowBddDecline::Interrupted)),
            Some(PbRouteDecision::Infeasible)
        ));
    }

    #[test]
    fn bounded_portfolio_trial_proves_a_multirow_optimum() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        // Deliberately outside the one-row specialization.  The exact optimum
        // is y=1, x=0 with value 1.
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 2.0), (y, 1.0)]);
        model.set_objective(&[(x, 3.0), (y, 1.0)], Sense::Minimize);

        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        let decision =
            try_solve_portfolio_trial(&model, deadline).expect("bounded PB portfolio result");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact portfolio optimum")
        };
        assert_eq!(value, integer(1));
        assert_eq!(model_values, vec![integer(0), integer(1)]);
        model
            .check_point(&model_values)
            .expect("portfolio witness rechecks");
    }

    #[test]
    fn typed_parallel_portfolio_proves_and_rechecks_a_multirow_optimum() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        model.add_row(2.0, f64::INFINITY, &[(x, 2.0), (y, 1.0), (z, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
        model.set_objective(&[(x, 5.0), (y, 2.0), (z, 1.0)], Sense::Minimize);

        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        let workers = NonZeroUsize::new(2).expect("nonzero worker budget");
        let decision = try_solve_portfolio_trial_with_workers(&model, deadline, workers)
            .expect("typed parallel PB portfolio result");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact parallel portfolio optimum")
        };
        // `2x + y + z >= 2`, `x + y <= 1`, min `5x + 2y + z`. The feasible set
        // is {(0,1,1)->3, (1,0,0)->5, (1,0,1)->6}; (0,0,1) is NOT in it —
        // 2*0 + 0 + 1 = 1, and 1 >= 2 is false. The optimum is 3 at (0,1,1).
        assert_eq!(value, integer(3));
        assert_eq!(model_values, vec![integer(0), integer(1), integer(1)]);
        assert_eq!(model.objective_value_at(&model_values), value);
        model
            .check_point(&model_values)
            .expect("parallel portfolio witness rechecks");

        // `check_point` proves FEASIBILITY, not optimality — it would have
        // accepted the solver's real answer while the hardcoded expectation
        // above named an infeasible point. Brute-force the 2^3 assignments so
        // the optimality half is derived, not asserted from a constant.
        let mut best: Option<BigRational> = None;
        for mask in 0u32..8 {
            let point: Vec<BigRational> = (0..3)
                .map(|bit| integer(i64::from((mask >> bit) & 1)))
                .collect();
            if model.check_point(&point).is_err() {
                continue;
            }
            let candidate = model.objective_value_at(&point);
            if best.as_ref().is_none_or(|b| candidate < *b) {
                best = Some(candidate);
            }
        }
        assert_eq!(
            best.expect("the enumerated feasible set is nonempty"),
            value,
            "the route's optimum must equal the enumerated optimum"
        );
    }

    #[test]
    fn verified_symmetry_preadmission_expiry_remains_a_decline() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(0.0, 1.0, &[(x, 1.0)]);

        let declined = try_solve_verified_block_symmetry_candidates_attempt(
            &model,
            &[],
            Instant::now() + Duration::from_secs(1),
        );
        assert!(matches!(&declined, VerifiedBlockSymmetryAttempt::Declined));
        assert!(!declined.earns_fresh_fallback());

        let expired =
            try_solve_verified_block_symmetry_candidates_attempt(&model, &[], Instant::now());
        assert!(matches!(&expired, VerifiedBlockSymmetryAttempt::Declined));
        assert!(!expired.earns_fresh_fallback());
    }

    #[test]
    fn verified_block_symmetry_trial_preserves_and_checks_matrix_optimum() {
        // Three interchangeable row/column blocks.  Repeated unit
        // coefficients deliberately make the legacy row-pair bijection
        // ambiguous; the scalable detector must verify a whole-block
        // automorphism before the route may add a lex leader.
        let mut model = Model::new();
        let columns: Vec<_> = (0..9).map(|_| model.add_binary_col()).collect();
        for row in 0..3 {
            let terms: Vec<_> = (0..3)
                .map(|column| (columns[row * 3 + column], 1.0))
                .collect();
            model.add_row(1.0, f64::INFINITY, &terms);
        }
        for column in 0..3 {
            let terms: Vec<_> = (0..3).map(|row| (columns[row * 3 + column], 1.0)).collect();
            model.add_row(1.0, f64::INFINITY, &terms);
        }
        let objective: Vec<_> = columns
            .iter()
            .copied()
            .map(|column| (column, 1.0))
            .collect();
        model.set_objective(&objective, Sense::Minimize);

        let deadline = Instant::now() + Duration::from_secs(5);
        let attempt = try_solve_verified_block_symmetry_candidates_attempt(&model, &[], deadline);
        assert!(attempt.earns_fresh_fallback());
        let VerifiedBlockSymmetryAttempt::Admitted(Some(decision)) = attempt else {
            panic!("expected an entered augmented search with a checked result")
        };
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact symmetric optimum")
        };
        assert_eq!(value, integer(3));
        assert_eq!(model.objective_value_at(&model_values), value);
        model
            .check_point(&model_values)
            .expect("symmetry-routed witness rechecks against source model");
    }

    #[test]
    fn portfolio_trial_obeys_preexisting_cancellation() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        assert!(try_solve_portfolio_trial_interruptible(&model, deadline, || true).is_none());
    }

    #[test]
    fn single_ranged_row_dp_proves_a_subset_sum_gap() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        // Reachable sums are 0, 6, 10, 14, 16, 20, 24, and 30: neither side
        // of this two-value interval is reachable.  The objective is aligned
        // with the row, exercising the word-parallel exact route used by the
        // large one-row MIPLIB family.
        model.add_row(17.0, 18.0, &[(x, 6.0), (y, 10.0), (z, 14.0)]);
        model.set_objective(&[(x, 6.0), (y, 10.0), (z, 14.0)], Sense::Minimize);

        assert!(matches!(
            try_solve_specialized(&model, None),
            Some(PbRouteDecision::CertifiedSingleRowInfeasible { .. })
        ));
    }

    #[test]
    fn max_objective_and_offset_map_back_exactly() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.set_objective(&[(x, 2.0), (y, 1.0)], Sense::Maximize);
        model.set_objective_offset(0.5);

        let decision =
            try_solve_specialized(&model, None).expect("single-row PB optimization route");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact optimum")
        };
        assert_eq!(value, BigRational::new(BigInt::from(7), BigInt::from(2)));
        assert_eq!(model_values, vec![integer(1), integer(1)]);
        assert_eq!(model.objective_value_at(&model_values), value);
    }

    #[test]
    fn nonbinary_model_declines() {
        let mut model = Model::new();
        model.add_col(0.0, 1.0);
        assert!(try_solve_specialized(&model, None).is_none());
    }

    #[test]
    fn expired_deadline_declines() {
        let model = Model::new();
        assert!(try_solve_specialized(&model, Some(Instant::now())).is_none());
    }

    #[test]
    fn session_routes_weighted_binary_optimization_and_records_replay() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        // Unequal weights make this a genuine PB row, not a scaled clause.
        model.add_row(1.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
        model.set_objective(&[(x, 5.0), (y, 1.0)], Sense::Minimize);

        let mut session = BabSession::new(model, &SolveOpts::default()).expect("session");
        let outcome = session.check().expect("PB-routed check");
        let Outcome::Optimal {
            value,
            model_values,
            ..
        } = outcome
        else {
            panic!("expected exact PB optimum")
        };
        assert_eq!(value, integer(1));
        assert_eq!(model_values, vec![integer(0), integer(1)]);
        assert!(session
            .replay_claims()
            .iter()
            .any(|claim| claim.claim == "pb-projection-optimal"));
    }

    /// End-to-end coverage for a two-row weighted-binary contradiction: each row
    /// is satisfiable alone and only their conjunction is not, so a single-row DP
    /// cannot settle it and a multi-row arm must.
    ///
    ///   3x + 5y >= 7   over binaries forces x = y = 1
    ///   4y + 6z <= 3   over binaries forces y = 0
    ///
    /// WHAT THIS DOES AND DOES NOT PIN — established by MUTATION, not by
    /// assumption. I added it intending to close the coverage gap around
    /// `session.rs::probe_scaled_deadline`, whose floor had been set
    /// conservatively because "no test exercises these lanes through the
    /// session-level budget". Starving that budget to zero (MULTIPLE = 0,
    /// FLOOR = 0) does NOT fail this test, so it does not pin that path.
    ///
    /// The reason is worth recording: `multi_row_bdd_infeasibility_certificate`
    /// has THREE assignment sites in session.rs — the budgeted probe, and two
    /// more inside the specialized/portfolio route handling, which carry their
    /// own budgets. The capability therefore survives a starved probe, which is
    /// reassuring for safety but means this test cannot isolate the probe.
    ///
    /// So: it pins that a multi-row contradiction is settled BY A MULTI-ROW
    /// CERTIFICATE through a full session — real coverage that did not exist
    /// before, since every other multi-row test invokes the route directly. The
    /// 2 ms floor is licensed separately, by instrumenting the probe call site
    /// itself and measuring `hit=true` at 0.000060 s on this same model.
    #[test]
    fn session_level_multi_row_infeasibility_still_routes() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        model.add_row(7.0, f64::INFINITY, &[(x, 3.0), (y, 5.0)]);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(y, 4.0), (z, 6.0)]);

        let mut session = BabSession::new(model, &SolveOpts::default()).expect("session");
        let outcome = session.check().expect("session check");
        assert!(
            matches!(outcome, Outcome::Infeasible { .. }),
            "the two-row contradiction must come back infeasible: {outcome:?}"
        );
        // NON-VACUITY. Asserting only `Infeasible` would pass with this lane
        // switched off entirely, because native branch-and-bound reaches the
        // same verdict — the assertion has to be that THIS ARM produced it.
        // A budget too small to let the lane conclude leaves this `None`.
        assert!(
            session.multi_row_bdd_infeasibility_certificate().is_some(),
            "the MULTI-ROW arm must be the one that settled it, through the \
             session-level budget; without this the test is satisfied by the \
             native lane and pins nothing"
        );
    }

    #[test]
    fn session_routes_compact_multirow_pb_through_bounded_portfolio() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        let z = model.add_binary_col();
        model.add_row(3.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
        model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (z, 2.0)]);
        model.set_objective(&[(x, 5.0), (y, 1.0), (z, 1.0)], Sense::Minimize);

        let mut session = BabSession::new(model, &SolveOpts::default()).expect("session");
        let outcome = session.check().expect("PB portfolio check");
        let Outcome::Optimal {
            value,
            model_values,
            ..
        } = outcome
        else {
            panic!("expected exact multirow PB optimum")
        };
        assert_eq!(value, integer(2));
        assert_eq!(model_values, vec![integer(0), integer(1), integer(1)]);
        assert!(session
            .replay_claims()
            .iter()
            .any(|claim| claim.claim == "pb-portfolio-projection-optimal"));
    }

    #[test]
    fn session_routes_weighted_binary_infeasibility_and_both_postures_carry_the_artifact() {
        fn contradictory_weighted_model() -> Model {
            let mut model = Model::new();
            let x = model.add_binary_col();
            let y = model.add_binary_col();
            model.add_row(4.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
            model.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 3.0)]);
            model
        }

        // BOTH halves assert on the ARTIFACT, not on a claim string.
        //
        // The route used to record `pb-projection-infeasible`, an unbacked
        // `ReplayClaim`, and this test asserted that string was present. The
        // route now returns `CertifiedSingleRowInfeasible` and the session
        // publishes a typed proof instead, so the string is deliberately gone.
        // Asserting the artifact is present AND replays against a freshly built
        // projection of the caller's own model is strictly stronger than
        // asserting a marker exists: a claim string is a solver's self-report
        // and is not model-bound.
        //
        // The old name promised the certificate posture "bypasses" the route.
        // It does not any more, and should not: gating the proof-exporting
        // lanes on `require_certificates` made the SHIPPED default (`--require
        // witness`) fall through to REPLAY-only routes, so a model refutable by
        // a succinct proof emitted an unbacked claim. Both postures now produce
        // the same evidence, and that is the property worth pinning.
        for require_certificates in [false, true] {
            let opts = SolveOpts::default().with_require_certificates(require_certificates);
            let mut session =
                BabSession::new(contradictory_weighted_model(), &opts).expect("session");
            assert!(
                matches!(
                    session.check().expect("PB infeasibility"),
                    Outcome::Infeasible { .. }
                ),
                "require_certificates={require_certificates}"
            );

            let certificate = session
                .single_row_dp_infeasibility_certificate()
                .unwrap_or_else(|| {
                    panic!(
                        "require_certificates={require_certificates}: the PB route's \
                         verdict must carry a typed single-row artifact"
                    )
                });
            verify_single_row_infeasibility_certificate_with_deadline(
                &contradictory_weighted_model(),
                certificate,
                None,
            )
            .expect("the published artifact must replay against the caller's model");
            encode_single_row_dp_infeasibility_certificate_json(certificate)
                .expect("the published artifact must encode for export");
        }
    }

    /// The artifact fields are cleared on model mutation, so "was it set on
    /// THIS check" is a real, checkable property — and it is what makes the
    /// assertion above mean something.
    #[test]
    fn a_published_single_row_artifact_belongs_to_the_check_that_produced_it() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        model.add_row(4.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 3.0)]);

        let mut session = BabSession::new(model, &SolveOpts::default()).expect("session");
        assert!(matches!(
            session.check().expect("check"),
            Outcome::Infeasible { .. }
        ));
        assert!(session.single_row_dp_infeasibility_certificate().is_some());

        session.push().expect("scope");
        session
            .add_row(f64::NEG_INFINITY, f64::INFINITY, &[])
            .expect("model mutation");
        assert!(
            session.single_row_dp_infeasibility_certificate().is_none(),
            "a model mutation must invalidate the previous check's evidence"
        );
    }
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
