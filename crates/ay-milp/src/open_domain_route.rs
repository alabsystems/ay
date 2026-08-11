// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded, fail-closed orchestration for structurally open integer domains.
//!
//! The transformations in [`crate::open_domain`] intentionally do not choose
//! a search engine.  This module supplies that missing boundary:
//!
//! * a monotone existential projection is solved as a bounded feasibility
//!   problem, then every witness is lifted and checked in the source model;
//! * for optimization, that checked source witness (or an optional checked AY
//!   incumbent supplied by the caller) is the *only* input accepted by
//!   [`ObjectiveCapPlan`];
//! * the resulting finite-integer model is sent either to the exact PB route
//!   or to the PB/LP route with the exact general-integer radix lift; and
//! * conclusive answers are promoted only after the corresponding projection
//!   or cap plan has been rebuilt and compared exactly.
//!
//! An objective-cap model contains its incumbent because its cutoff is
//! inclusive.  Consequently, an `Infeasible` answer from that model is an
//! internal inconsistency.  It is never promoted as source infeasibility and
//! is not re-labelled as optimality.  An exact optimization engine's
//! `Optimal` result may internally have established its last strict cutoff by
//! infeasibility; that result is the only cutoff-infeasibility path promoted
//! here.

use std::time::{Duration, Instant};

use ay_pb_core::{MultiRowBddInfeasibilityCertificate, SingleRowDpInfeasibilityCertificate};
use num_rational::BigRational;

use crate::model::{Col, ColKind, Model, Sense};
use crate::open_domain::{MonotoneProjection, ObjectiveCapPlan};
use crate::pb_route::PbRouteDecision;
use crate::{HybridIntegerLiftInfeasibilityCertificate, HybridPbLpInfeasibilityCertificate};

/// One absolute budget is shared by projection feasibility and capped
/// optimization.  A caller's earlier deadline always wins.
const MAX_OPEN_DOMAIN_WALL: Duration = Duration::from_secs(2);

/// A conclusive answer, or a checked optimization incumbent, from the
/// open-domain route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OpenDomainRouteDecision {
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    Infeasible,
    CertifiedSingleRowInfeasible {
        certificate: SingleRowDpInfeasibilityCertificate,
    },
    CertifiedMultiRowInfeasible {
        certificate: MultiRowBddInfeasibilityCertificate,
    },
    CertifiedHybridPbLpInfeasible {
        certificate: HybridPbLpInfeasibilityCertificate,
    },
    CertifiedHybridIntegerLiftInfeasible {
        certificate: HybridIntegerLiftInfeasibilityCertificate,
    },
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BoundedDecision {
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    /// Infeasibility of the model passed to the bounded backend.  Its meaning
    /// depends on the caller: it proves source infeasibility after a monotone
    /// feasibility projection, but is inconsistent after an inclusive cap.
    Infeasible,
    CertifiedSingleRowInfeasible {
        certificate: SingleRowDpInfeasibilityCertificate,
    },
    CertifiedMultiRowInfeasible {
        certificate: MultiRowBddInfeasibilityCertificate,
    },
    CertifiedHybridPbLpInfeasible {
        certificate: HybridPbLpInfeasibilityCertificate,
    },
    CertifiedHybridIntegerLiftInfeasible {
        certificate: HybridIntegerLiftInfeasibilityCertificate,
    },
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
    },
}

trait BoundedBackend {
    fn solve<F>(
        &mut self,
        model: &Model,
        deadline: Instant,
        should_stop: &mut F,
    ) -> Option<BoundedDecision>
    where
        F: FnMut() -> bool;
}

struct AyBoundedBackend;

impl BoundedBackend for AyBoundedBackend {
    fn solve<F>(
        &mut self,
        model: &Model,
        deadline: Instant,
        should_stop: &mut F,
    ) -> Option<BoundedDecision>
    where
        F: FnMut() -> bool,
    {
        if stopped(deadline, should_stop) {
            return None;
        }

        let mut integral_columns = 0usize;
        let mut general_integer_columns = 0usize;
        let mut continuous_columns = 0usize;
        for column in 0..model.num_cols() {
            if column & 0x3ff == 0 && stopped(deadline, should_stop) {
                return None;
            }
            let col = Col(column as u32);
            match model.col_kind(col) {
                ColKind::Binary => {
                    integral_columns += 1;
                    let (lb, ub) = model.col_bounds(col);
                    if !lb.is_finite() || !ub.is_finite() {
                        return None;
                    }
                }
                ColKind::Integer => {
                    integral_columns += 1;
                    general_integer_columns += 1;
                    let (lb, ub) = model.col_bounds(col);
                    if !lb.is_finite() || !ub.is_finite() {
                        return None;
                    }
                }
                ColKind::Continuous => continuous_columns += 1,
            }
        }
        if integral_columns == 0 {
            return None;
        }

        let decision = if continuous_columns == 0 {
            crate::pb_route::try_solve_portfolio_trial_interruptible(model, deadline, || {
                should_stop()
            })
            .map(map_pb_decision)
        } else if general_integer_columns == 0 {
            crate::hybrid_pb_lp::try_solve_certified_interruptible(model, Some(deadline), || {
                should_stop()
            })
            .map(map_certified_hybrid_decision)
        } else {
            crate::hybrid_integer_lift::try_solve_certified_interruptible(
                model,
                Some(deadline),
                || should_stop(),
            )
            .map(map_certified_integer_lift_decision)
        }?;

        (!stopped(deadline, should_stop)).then_some(decision)
    }
}

fn map_pb_decision(decision: PbRouteDecision) -> BoundedDecision {
    match decision {
        PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } => BoundedDecision::Feasible {
            model_values,
            incumbent_only,
        },
        PbRouteDecision::Infeasible => BoundedDecision::Infeasible,
        PbRouteDecision::CertifiedSingleRowInfeasible { certificate } => {
            BoundedDecision::CertifiedSingleRowInfeasible { certificate }
        }
        PbRouteDecision::CertifiedMultiRowInfeasible { certificate } => {
            BoundedDecision::CertifiedMultiRowInfeasible { certificate }
        }
        PbRouteDecision::Optimal {
            value,
            model_values,
        } => BoundedDecision::Optimal {
            value,
            model_values,
        },
    }
}

fn map_certified_hybrid_decision(
    decision: crate::hybrid_pb_lp::CertifiedHybridPbLpDecision,
) -> BoundedDecision {
    match decision {
        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible {
            model_values,
            incumbent_only,
        } => BoundedDecision::Feasible {
            model_values,
            incumbent_only,
        },
        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(certificate) => {
            BoundedDecision::CertifiedHybridPbLpInfeasible { certificate }
        }
        crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Optimal {
            value,
            model_values,
        } => BoundedDecision::Optimal {
            value,
            model_values,
        },
    }
}

fn map_certified_integer_lift_decision(
    decision: crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision,
) -> BoundedDecision {
    match decision {
        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
            model_values,
            incumbent_only,
        } => BoundedDecision::Feasible {
            model_values,
            incumbent_only,
        },
        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(certificate) => {
            BoundedDecision::CertifiedHybridIntegerLiftInfeasible { certificate }
        }
        crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Optimal {
            value,
            model_values,
        } => BoundedDecision::Optimal {
            value,
            model_values,
        },
    }
}

/// Try the production route using only an incumbent discovered by AY's exact
/// monotone projection path.
pub(crate) fn try_solve(
    model: &Model,
    outer_deadline: Option<Instant>,
) -> Option<OpenDomainRouteDecision> {
    try_solve_with_incumbent_interruptible(model, None, outer_deadline, || false)
}

/// Search only for an exportable infeasibility proof of the exact monotone
/// projection.  This certificate-required entry point never spends its
/// bounded slice optimizing a feasible objective-cap model.
pub(crate) fn try_prove_infeasibility(
    model: &Model,
    trial_deadline: Instant,
) -> Option<OpenDomainRouteDecision> {
    if Instant::now() >= trial_deadline {
        return None;
    }
    let projection = MonotoneProjection::try_build(model, Some(trial_deadline), || {
        Instant::now() >= trial_deadline
    })
    .ok()?;

    if let Some(PbRouteDecision::CertifiedSingleRowInfeasible { certificate }) =
        crate::pb_route::try_prove_single_row_infeasibility(projection.residual(), trial_deadline)
    {
        if verify_single_row_infeasibility_certificate_with_deadline(
            model,
            &certificate,
            Some(trial_deadline),
        ) {
            return Some(OpenDomainRouteDecision::CertifiedSingleRowInfeasible { certificate });
        }
        return None;
    }

    if let Some(PbRouteDecision::CertifiedMultiRowInfeasible { certificate }) =
        crate::pb_route::try_prove_multi_row_infeasibility(projection.residual(), trial_deadline)
    {
        if verify_multi_row_infeasibility_certificate_with_deadline(
            model,
            &certificate,
            Some(trial_deadline),
        ) {
            return Some(OpenDomainRouteDecision::CertifiedMultiRowInfeasible { certificate });
        }
    }

    if let Some(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(certificate)) =
        crate::hybrid_pb_lp::try_solve_certified(projection.residual(), Some(trial_deadline))
    {
        if verify_hybrid_pb_lp_infeasibility_certificate_with_deadline(
            model,
            &certificate,
            Some(trial_deadline),
        ) {
            return Some(OpenDomainRouteDecision::CertifiedHybridPbLpInfeasible { certificate });
        }
        return None;
    }

    if let Some(crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(
        certificate,
    )) =
        crate::hybrid_integer_lift::try_solve_certified(projection.residual(), Some(trial_deadline))
    {
        if verify_hybrid_integer_lift_infeasibility_certificate_with_deadline(
            model,
            &certificate,
            Some(trial_deadline),
        ) {
            return Some(
                OpenDomainRouteDecision::CertifiedHybridIntegerLiftInfeasible { certificate },
            );
        }
    }
    None
}

/// Rebuild the source-model projection and independently replay a single-row
/// residual certificate against that freshly reconstructed exact residual.
pub(crate) fn verify_single_row_infeasibility_certificate(
    model: &Model,
    certificate: &SingleRowDpInfeasibilityCertificate,
) -> bool {
    verify_single_row_infeasibility_certificate_with_deadline(model, certificate, None)
}

fn verify_single_row_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &SingleRowDpInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> bool {
    let Ok(projection) = MonotoneProjection::try_build(model, deadline, || {
        deadline.is_some_and(|deadline| Instant::now() >= deadline)
    }) else {
        return false;
    };
    crate::pb_route::verify_single_row_infeasibility_certificate_with_deadline(
        projection.residual(),
        certificate,
        deadline,
    )
    .is_ok()
}

/// Rebuild the source-model projection and independently replay a multi-row
/// residual decision DAG against that freshly reconstructed exact residual.
pub(crate) fn verify_multi_row_infeasibility_certificate(
    model: &Model,
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> bool {
    verify_multi_row_infeasibility_certificate_with_deadline(model, certificate, None)
}

fn verify_multi_row_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &MultiRowBddInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> bool {
    let Ok(projection) = MonotoneProjection::try_build(model, deadline, || {
        deadline.is_some_and(|deadline| Instant::now() >= deadline)
    }) else {
        return false;
    };
    crate::pb_route::verify_multi_row_infeasibility_certificate_with_deadline(
        projection.residual(),
        certificate,
        deadline,
    )
    .is_ok()
}

/// Rebuild the open-domain projection and replay a hybrid PB/LP cut ledger
/// against that exact residual.
pub(crate) fn verify_hybrid_pb_lp_infeasibility_certificate(
    model: &Model,
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> bool {
    verify_hybrid_pb_lp_infeasibility_certificate_with_deadline(model, certificate, None)
}

fn verify_hybrid_pb_lp_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &HybridPbLpInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> bool {
    let Ok(projection) = MonotoneProjection::try_build(model, deadline, || {
        deadline.is_some_and(|deadline| Instant::now() >= deadline)
    }) else {
        return false;
    };
    let mut should_stop = || deadline.is_some_and(|deadline| Instant::now() >= deadline);
    crate::hybrid_pb_lp::verify_hybrid_pb_lp_infeasibility_certificate_interruptible(
        projection.residual(),
        certificate,
        deadline,
        &mut should_stop,
    )
    .is_ok()
}

/// Rebuild the open-domain projection and its bounded-integer radix lift before
/// replaying the nested hybrid certificate.
pub(crate) fn verify_hybrid_integer_lift_infeasibility_certificate(
    model: &Model,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> bool {
    verify_hybrid_integer_lift_infeasibility_certificate_with_deadline(model, certificate, None)
}

fn verify_hybrid_integer_lift_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> bool {
    let Ok(projection) = MonotoneProjection::try_build(model, deadline, || {
        deadline.is_some_and(|deadline| Instant::now() >= deadline)
    }) else {
        return false;
    };
    let mut should_stop = || deadline.is_some_and(|deadline| Instant::now() >= deadline);
    crate::hybrid_integer_lift::verify_hybrid_integer_lift_infeasibility_certificate_interruptible(
        projection.residual(),
        certificate,
        deadline,
        &mut should_stop,
    )
    .is_ok()
}

/// Try the production route with an optional exact incumbent produced by an
/// AY native/heuristic path.  The values are never trusted: the original model
/// checks them exactly before they can influence a cap.
///
/// Supplying `None` is equivalent to [`try_solve`].  The optional form lets a
/// caller feed a later native incumbent to models whose open rows are not
/// monotone-projectable (notably the mixed open-domain class) without changing
/// this route's soundness boundary.
pub(crate) fn try_solve_with_incumbent(
    model: &Model,
    ay_incumbent: Option<&[BigRational]>,
    outer_deadline: Option<Instant>,
) -> Option<OpenDomainRouteDecision> {
    try_solve_with_incumbent_interruptible(model, ay_incumbent, outer_deadline, || false)
}

pub(crate) fn try_solve_with_incumbent_interruptible<F>(
    model: &Model,
    ay_incumbent: Option<&[BigRational]>,
    outer_deadline: Option<Instant>,
    mut should_stop: F,
) -> Option<OpenDomainRouteDecision>
where
    F: FnMut() -> bool,
{
    let deadline = bounded_deadline(outer_deadline)?;
    let mut backend = AyBoundedBackend;
    try_solve_with_backend(
        model,
        ay_incumbent,
        deadline,
        &mut should_stop,
        &mut backend,
    )
}

fn try_solve_with_backend<F, B>(
    model: &Model,
    ay_incumbent: Option<&[BigRational]>,
    deadline: Instant,
    should_stop: &mut F,
    backend: &mut B,
) -> Option<OpenDomainRouteDecision>
where
    F: FnMut() -> bool,
    B: BoundedBackend,
{
    if stopped(deadline, should_stop) || model.validate().is_err() {
        return None;
    }

    if model.has_objective() {
        if let Some(incumbent) = ay_incumbent {
            // ObjectiveCapPlan performs the source point and objective check.
            return solve_capped(model, incumbent, deadline, should_stop, backend);
        }
    }

    let projection = MonotoneProjection::try_build(model, Some(deadline), || should_stop()).ok()?;
    if stopped(deadline, should_stop) {
        return None;
    }
    let residual_decision = backend.solve(projection.residual(), deadline, should_stop)?;
    if stopped(deadline, should_stop) {
        return None;
    }

    match residual_decision {
        BoundedDecision::Infeasible => {
            // This implication is feasibility-preserving, unlike objective
            // capping.  Rebuild the entire projection before promotion.
            projection
                .revalidate(model, Some(deadline), || should_stop())
                .then_some(OpenDomainRouteDecision::Infeasible)
        }
        BoundedDecision::CertifiedSingleRowInfeasible { certificate } => {
            verify_single_row_infeasibility_certificate_with_deadline(
                model,
                &certificate,
                Some(deadline),
            )
            .then_some(OpenDomainRouteDecision::CertifiedSingleRowInfeasible { certificate })
        }
        BoundedDecision::CertifiedMultiRowInfeasible { certificate } => {
            verify_multi_row_infeasibility_certificate_with_deadline(
                model,
                &certificate,
                Some(deadline),
            )
            .then_some(OpenDomainRouteDecision::CertifiedMultiRowInfeasible { certificate })
        }
        BoundedDecision::CertifiedHybridPbLpInfeasible { certificate } => {
            verify_hybrid_pb_lp_infeasibility_certificate_with_deadline(
                model,
                &certificate,
                Some(deadline),
            )
            .then_some(OpenDomainRouteDecision::CertifiedHybridPbLpInfeasible { certificate })
        }
        BoundedDecision::CertifiedHybridIntegerLiftInfeasible { certificate } => {
            verify_hybrid_integer_lift_infeasibility_certificate_with_deadline(
                model,
                &certificate,
                Some(deadline),
            )
            .then_some(
                OpenDomainRouteDecision::CertifiedHybridIntegerLiftInfeasible { certificate },
            )
        }
        BoundedDecision::Feasible { model_values, .. } => {
            let incumbent =
                projection.checked_lift(model, &model_values, Some(deadline), || should_stop())?;
            if stopped(deadline, should_stop) {
                return None;
            }
            if model.has_objective() {
                solve_capped(model, &incumbent, deadline, should_stop, backend)
            } else {
                Some(OpenDomainRouteDecision::Feasible {
                    model_values: incumbent,
                    incumbent_only: false,
                })
            }
        }
        // MonotoneProjection deliberately removes the objective.  An
        // `Optimal` answer here would violate the backend contract.
        BoundedDecision::Optimal { .. } => None,
    }
}

fn solve_capped<F, B>(
    model: &Model,
    incumbent: &[BigRational],
    deadline: Instant,
    should_stop: &mut F,
    backend: &mut B,
) -> Option<OpenDomainRouteDecision>
where
    F: FnMut() -> bool,
    B: BoundedBackend,
{
    let plan =
        ObjectiveCapPlan::try_build(model, incumbent, Some(deadline), || should_stop()).ok()?;
    if stopped(deadline, should_stop) {
        return None;
    }
    let incumbent_value = model.objective_value_at(plan.incumbent());
    let decision = backend.solve(plan.bounded(), deadline, should_stop);
    if stopped(deadline, should_stop) {
        return None;
    }

    match decision {
        Some(BoundedDecision::Optimal {
            value,
            model_values,
        }) => {
            let checked_value = plan.checked_original_point(model, &model_values)?;
            if checked_value != value
                || !at_least_as_good(model.sense(), &checked_value, &incumbent_value)
                || !plan.revalidate(model, Some(deadline), || should_stop())
                || stopped(deadline, should_stop)
            {
                return None;
            }
            Some(OpenDomainRouteDecision::Optimal {
                value: checked_value,
                model_values,
            })
        }
        Some(BoundedDecision::Feasible { model_values, .. }) => {
            let candidate_value = plan.checked_original_point(model, &model_values)?;
            let best = if at_least_as_good(model.sense(), &candidate_value, &incumbent_value) {
                model_values
            } else {
                plan.incumbent().to_vec()
            };
            Some(OpenDomainRouteDecision::Feasible {
                model_values: best,
                incumbent_only: true,
            })
        }
        None => Some(OpenDomainRouteDecision::Feasible {
            model_values: plan.incumbent().to_vec(),
            incumbent_only: true,
        }),
        Some(
            BoundedDecision::Infeasible
            | BoundedDecision::CertifiedSingleRowInfeasible { .. }
            | BoundedDecision::CertifiedMultiRowInfeasible { .. }
            | BoundedDecision::CertifiedHybridPbLpInfeasible { .. }
            | BoundedDecision::CertifiedHybridIntegerLiftInfeasible { .. },
        ) => {
            // The inclusive cap model contains `plan.incumbent()`.  Treat a
            // contrary backend result as inconsistency, never as original
            // infeasibility or as an optimality proof.
            None
        }
    }
}

fn at_least_as_good(sense: Sense, candidate: &BigRational, incumbent: &BigRational) -> bool {
    match sense {
        Sense::Minimize => candidate <= incumbent,
        Sense::Maximize => candidate >= incumbent,
    }
}

fn bounded_deadline(outer: Option<Instant>) -> Option<Instant> {
    let now = Instant::now();
    if outer.is_some_and(|deadline| deadline <= now) {
        return None;
    }
    let local = now.checked_add(MAX_OPEN_DOMAIN_WALL)?;
    Some(outer.map_or(local, |deadline| deadline.min(local)))
}

fn stopped<F>(deadline: Instant, should_stop: &mut F) -> bool
where
    F: FnMut() -> bool,
{
    should_stop() || Instant::now() >= deadline
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use num_bigint::BigInt;
    use num_integer::Integer;
    use num_traits::{ToPrimitive, Zero};

    use super::*;
    use crate::model::exact;

    fn i(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    #[derive(Default)]
    struct EnumeratingBackend {
        deadlines: Vec<Instant>,
        calls: usize,
    }

    impl BoundedBackend for EnumeratingBackend {
        fn solve<F>(
            &mut self,
            model: &Model,
            deadline: Instant,
            should_stop: &mut F,
        ) -> Option<BoundedDecision>
        where
            F: FnMut() -> bool,
        {
            self.calls += 1;
            self.deadlines.push(deadline);
            let domains = finite_integer_domains(model)?;
            let mut point = vec![BigRational::zero(); model.num_cols()];
            let mut best: Option<(BigRational, Vec<BigRational>)> = None;
            enumerate_points(&domains, 0, &mut point, &mut |candidate| {
                if stopped(deadline, should_stop) {
                    return false;
                }
                if model.check_point(candidate).is_err() {
                    return true;
                }
                if !model.has_objective() {
                    best = Some((BigRational::zero(), candidate.to_vec()));
                    return false;
                }
                let value = model.objective_value_at(candidate);
                let replace = best
                    .as_ref()
                    .is_none_or(|(old, _)| at_least_as_good(model.sense(), &value, old));
                if replace {
                    best = Some((value, candidate.to_vec()));
                }
                true
            });
            if stopped(deadline, should_stop) {
                return None;
            }
            match best {
                None => Some(BoundedDecision::Infeasible),
                Some((_, model_values)) if !model.has_objective() => {
                    Some(BoundedDecision::Feasible {
                        model_values,
                        incumbent_only: false,
                    })
                }
                Some((value, model_values)) => Some(BoundedDecision::Optimal {
                    value,
                    model_values,
                }),
            }
        }
    }

    fn finite_integer_domains(model: &Model) -> Option<Vec<Vec<BigRational>>> {
        let mut domains = Vec::with_capacity(model.num_cols());
        let mut product = 1usize;
        for column in 0..model.num_cols() {
            let col = Col(column as u32);
            if matches!(model.col_kind(col), ColKind::Continuous) {
                return None;
            }
            let (lb, ub) = model.col_bounds(col);
            let lower = exact(lb)?;
            let upper = exact(ub)?;
            let lo = lower.numer().div_ceil(lower.denom());
            let hi = upper.numer().div_floor(upper.denom());
            if lo > hi {
                domains.push(Vec::new());
                continue;
            }
            let width = (&hi - &lo).to_usize()?.checked_add(1)?;
            product = product.checked_mul(width)?;
            if product > 250_000 {
                return None;
            }
            let mut values = Vec::with_capacity(width);
            let mut value = lo;
            while value <= hi {
                values.push(BigRational::from_integer(value.clone()));
                value += 1;
            }
            domains.push(values);
        }
        Some(domains)
    }

    fn enumerate_points<F>(
        domains: &[Vec<BigRational>],
        column: usize,
        point: &mut [BigRational],
        visit: &mut F,
    ) -> bool
    where
        F: FnMut(&[BigRational]) -> bool,
    {
        if column == domains.len() {
            return visit(point);
        }
        for value in &domains[column] {
            point[column] = value.clone();
            if !enumerate_points(domains, column + 1, point, visit) {
                return false;
            }
        }
        true
    }

    fn brute_original(
        model: &Model,
        domains: &[Vec<BigRational>],
    ) -> Option<(BigRational, Vec<BigRational>)> {
        let mut point = vec![BigRational::zero(); model.num_cols()];
        let mut best: Option<(BigRational, Vec<BigRational>)> = None;
        enumerate_points(domains, 0, &mut point, &mut |candidate| {
            if model.check_point(candidate).is_err() {
                return true;
            }
            let value = model.objective_value_at(candidate);
            if !model.has_objective()
                || best
                    .as_ref()
                    .is_none_or(|(old, _)| at_least_as_good(model.sense(), &value, old))
            {
                best = Some((value, candidate.to_vec()));
            }
            true
        });
        best
    }

    fn run_enumerating(model: &Model) -> (Option<OpenDomainRouteDecision>, EnumeratingBackend) {
        let mut backend = EnumeratingBackend::default();
        let result = try_solve_with_backend(
            model,
            None,
            Instant::now() + Duration::from_secs(30),
            &mut || false,
            &mut backend,
        );
        (result, backend)
    }

    #[test]
    fn exhaustive_monotone_projection_preserves_feasibility_and_infeasibility() {
        for demand in 0..=4 {
            for retained_requirement in 0..=2 {
                let mut model = Model::new();
                let x = model.add_binary_col();
                let open = model.add_int_col(0.0, f64::INFINITY);
                model.add_row(demand as f64, f64::INFINITY, &[(x, 1.0), (open, 1.0)]);
                model.add_row(retained_requirement as f64, f64::INFINITY, &[(x, 1.0)]);

                let domains = vec![vec![i(0), i(1)], (0..=6).map(i).collect()];
                let expected = brute_original(&model, &domains).is_some();
                let (decision, backend) = run_enumerating(&model);
                assert_eq!(backend.calls, 1);
                match decision {
                    Some(OpenDomainRouteDecision::Feasible {
                        model_values,
                        incumbent_only: false,
                    }) => {
                        assert!(expected);
                        model.check_point(&model_values).unwrap();
                    }
                    Some(OpenDomainRouteDecision::Infeasible) => assert!(!expected),
                    other => panic!("unexpected result {other:?}"),
                }
            }
        }
    }

    #[test]
    fn exhaustive_project_then_cap_preserves_integer_optimum() {
        for demand in 0..=5 {
            for retained_cost in -2..=3 {
                for open_cost in 1..=2 {
                    let mut model = Model::new();
                    let x = model.add_int_col(0.0, 2.0);
                    let open = model.add_int_col(0.0, f64::INFINITY);
                    model.add_row(demand as f64, f64::INFINITY, &[(x, 1.0), (open, 1.0)]);
                    model.set_objective(
                        &[(x, retained_cost as f64), (open, open_cost as f64)],
                        Sense::Minimize,
                    );

                    let domains = vec![(0..=2).map(i).collect(), (0..=8).map(i).collect()];
                    let (expected, _) = brute_original(&model, &domains).unwrap();
                    let (decision, backend) = run_enumerating(&model);
                    assert_eq!(backend.calls, 2);
                    let Some(OpenDomainRouteDecision::Optimal {
                        value,
                        model_values,
                    }) = decision
                    else {
                        panic!("expected exact optimum")
                    };
                    assert_eq!(value, expected);
                    assert_eq!(model.objective_value_at(&model_values), expected);
                    model.check_point(&model_values).unwrap();
                }
            }
        }
    }

    #[test]
    fn all_integer_amur_shape_projects_then_caps() {
        let mut model = Model::new();
        let a = model.add_int_col(0.0, 2.0);
        let b = model.add_int_col(0.0, 2.0);
        let open_a = model.add_int_col(0.0, f64::INFINITY);
        let open_b = model.add_int_col(0.0, f64::INFINITY);
        let objective_only = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(3.0, f64::INFINITY, &[(a, 1.0), (open_a, 1.0)]);
        model.add_row(2.0, f64::INFINITY, &[(b, 1.0), (open_b, 1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(a, 1.0), (b, 1.0)]);
        model.set_objective(
            &[
                (a, 2.0),
                (b, 1.0),
                (open_a, 3.0),
                (open_b, 4.0),
                (objective_only, 1.0),
            ],
            Sense::Minimize,
        );

        let domains = vec![
            (0..=2).map(i).collect(),
            (0..=2).map(i).collect(),
            (0..=5).map(i).collect(),
            (0..=5).map(i).collect(),
            (0..=5).map(i).collect(),
        ];
        let (expected, _) = brute_original(&model, &domains).unwrap();
        let (decision, backend) = run_enumerating(&model);
        assert_eq!(backend.calls, 2, "projection plus objective-cap solve");
        let Some(OpenDomainRouteDecision::Optimal {
            value,
            model_values,
        }) = decision
        else {
            panic!("AMUR structural analogue must close")
        };
        assert_eq!(value, expected);
        model.check_point(&model_values).unwrap();
    }

    #[test]
    fn aoos_and_coxs_shapes_promote_only_revalidated_projection_infeasibility() {
        for extra_open_cover in [false, true] {
            let mut model = Model::new();
            let x = model.add_binary_col();
            let open = model.add_int_col(0.0, f64::INFINITY);
            model.add_row(4.0, f64::INFINITY, &[(open, 1.0)]);
            if extra_open_cover {
                model.add_row(7.0, f64::INFINITY, &[(open, 2.0)]);
            }
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
            model.set_objective(&[(open, 1.0)], Sense::Minimize);

            let (decision, backend) = run_enumerating(&model);
            assert_eq!(backend.calls, 1);
            assert_eq!(decision, Some(OpenDomainRouteDecision::Infeasible));
        }
    }

    #[derive(Default)]
    struct CountingBackend {
        calls: usize,
    }

    impl BoundedBackend for CountingBackend {
        fn solve<F>(
            &mut self,
            _model: &Model,
            _deadline: Instant,
            _should_stop: &mut F,
        ) -> Option<BoundedDecision>
        where
            F: FnMut() -> bool,
        {
            self.calls += 1;
            None
        }
    }

    #[test]
    fn mixed_murg_motu_shape_declines_without_an_ay_incumbent() {
        for maximum in [false, true] {
            let mut model = Model::new();
            let open = model.add_int_col(0.0, f64::INFINITY);
            let continuous_peer = model.add_col(0.0, f64::INFINITY);
            // This is the MURG/MOTU obstruction: an attempted upper row for
            // the integer still has an open continuous peer.  Increasing the
            // open integer can hurt it, so existential projection must stop.
            model.add_row(
                f64::NEG_INFINITY,
                0.0,
                &[(open, 1.0), (continuous_peer, -1.0)],
            );
            model.set_objective(
                &[(open, if maximum { -1.0 } else { 1.0 })],
                if maximum {
                    Sense::Maximize
                } else {
                    Sense::Minimize
                },
            );
            let mut backend = CountingBackend::default();
            let decision = try_solve_with_backend(
                &model,
                None,
                Instant::now() + Duration::from_secs(30),
                &mut || false,
                &mut backend,
            );
            assert_eq!(decision, None);
            assert_eq!(backend.calls, 0);
        }
    }

    struct InspectCappedBackend {
        expected: Vec<BigRational>,
        calls: usize,
    }

    impl BoundedBackend for InspectCappedBackend {
        fn solve<F>(
            &mut self,
            model: &Model,
            _deadline: Instant,
            _should_stop: &mut F,
        ) -> Option<BoundedDecision>
        where
            F: FnMut() -> bool,
        {
            self.calls += 1;
            for column in 0..model.num_cols() {
                let col = Col(column as u32);
                if matches!(model.col_kind(col), ColKind::Integer) {
                    let (lb, ub) = model.col_bounds(col);
                    assert!(lb.is_finite() && ub.is_finite());
                }
            }
            Some(BoundedDecision::Optimal {
                value: model.objective_value_at(&self.expected),
                model_values: self.expected.clone(),
            })
        }
    }

    #[test]
    fn supplied_exact_ay_incumbent_unlocks_mixed_open_domain_cap() {
        let mut model = Model::new();
        let open = model.add_int_col(0.0, f64::INFINITY);
        let continuous_peer = model.add_col(0.0, f64::INFINITY);
        model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(open, 1.0), (continuous_peer, -1.0)],
        );
        model.set_objective(&[(open, 1.0)], Sense::Minimize);
        let incumbent = vec![i(0), i(0)];
        let mut backend = InspectCappedBackend {
            expected: incumbent.clone(),
            calls: 0,
        };
        let decision = try_solve_with_backend(
            &model,
            Some(&incumbent),
            Instant::now() + Duration::from_secs(30),
            &mut || false,
            &mut backend,
        );
        assert_eq!(backend.calls, 1);
        assert_eq!(
            decision,
            Some(OpenDomainRouteDecision::Optimal {
                value: i(0),
                model_values: incumbent,
            })
        );
    }

    struct ScriptedBackend {
        decisions: VecDeque<Option<BoundedDecision>>,
        deadlines: Vec<Instant>,
    }

    impl BoundedBackend for ScriptedBackend {
        fn solve<F>(
            &mut self,
            _model: &Model,
            deadline: Instant,
            _should_stop: &mut F,
        ) -> Option<BoundedDecision>
        where
            F: FnMut() -> bool,
        {
            self.deadlines.push(deadline);
            self.decisions.pop_front().flatten()
        }
    }

    #[test]
    fn inclusive_cap_infeasibility_is_inconsistency_not_a_source_verdict() {
        let mut model = Model::new();
        let open = model.add_int_col(0.0, f64::INFINITY);
        model.set_objective(&[(open, 1.0)], Sense::Minimize);
        let incumbent = vec![i(3)];
        let mut backend = ScriptedBackend {
            decisions: VecDeque::from([Some(BoundedDecision::Infeasible)]),
            deadlines: Vec::new(),
        };
        let decision = try_solve_with_backend(
            &model,
            Some(&incumbent),
            Instant::now() + Duration::from_secs(30),
            &mut || false,
            &mut backend,
        );
        assert_eq!(decision, None);
    }

    #[test]
    fn invalid_supplied_incumbent_never_reaches_the_backend() {
        let mut model = Model::new();
        let open = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(2.0, f64::INFINITY, &[(open, 1.0)]);
        model.set_objective(&[(open, 1.0)], Sense::Minimize);
        let mut backend = CountingBackend::default();
        let decision = try_solve_with_backend(
            &model,
            Some(&[i(1)]),
            Instant::now() + Duration::from_secs(30),
            &mut || false,
            &mut backend,
        );
        assert_eq!(decision, None);
        assert_eq!(backend.calls, 0);
    }

    #[test]
    fn one_absolute_deadline_is_shared_by_both_backend_phases() {
        let mut model = Model::new();
        let retained = model.add_int_col(0.0, 1.0);
        let open = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(1.0, f64::INFINITY, &[(retained, 1.0), (open, 1.0)]);
        model.set_objective(&[(retained, 1.0), (open, 1.0)], Sense::Minimize);

        let route_start = Instant::now();
        let deadline = bounded_deadline(Some(route_start + Duration::from_secs(60))).unwrap();
        let mut backend = EnumeratingBackend::default();
        let decision = try_solve_with_backend(&model, None, deadline, &mut || false, &mut backend);
        assert!(matches!(
            decision,
            Some(OpenDomainRouteDecision::Optimal { .. })
        ));
        assert_eq!(backend.deadlines, vec![deadline, deadline]);
        assert!(deadline <= route_start + MAX_OPEN_DOMAIN_WALL + Duration::from_millis(10));
    }

    #[test]
    fn expired_deadline_and_stop_request_prevent_backend_work() {
        let mut model = Model::new();
        model.add_int_col(0.0, f64::INFINITY);

        assert_eq!(
            try_solve_with_incumbent_interruptible(&model, None, Some(Instant::now()), || false),
            None
        );

        let mut backend = CountingBackend::default();
        let decision = try_solve_with_backend(
            &model,
            None,
            Instant::now() + Duration::from_secs(30),
            &mut || true,
            &mut backend,
        );
        assert_eq!(decision, None);
        assert_eq!(backend.calls, 0);
    }

    #[test]
    fn source_shape_cap_declines_before_backend_allocation() {
        let mut model = Model::new();
        model.add_int_col(0.0, f64::INFINITY);
        for _ in 0..8_192 {
            model.add_binary_col();
        }
        let mut backend = CountingBackend::default();
        let decision = try_solve_with_backend(
            &model,
            None,
            Instant::now() + Duration::from_secs(30),
            &mut || false,
            &mut backend,
        );
        assert_eq!(decision, None);
        assert_eq!(backend.calls, 0);
    }
}
