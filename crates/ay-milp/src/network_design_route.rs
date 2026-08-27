// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded production adapter for the exact network-design projection.
//!
//! [`crate::network_design_pb`] proves a small capacitated-flow block equivalent
//! to a bounded-integral master.  This adapter gives that master a bounded slice
//! of AY's PB portfolio, lifts every returned master point through an exact
//! rational transshipment, and checks the complete point against the original
//! model.  A structural, resource, deadline, PB, or reconstruction decline
//! leaves the ordinary MILP path authoritative.

use std::time::{Duration, Instant};

use ay_pb_core::{MultiRowBddInfeasibilityCertificate, SingleRowDpInfeasibilityCertificate};
use num_rational::BigRational;
use num_traits::Zero;

use crate::network_design_pb::{
    project_network_design, project_network_design_lazy, NetworkDesignProjection,
};
use crate::pb_route::{try_solve_portfolio_trial, PbRouteDecision, VerifiedBlockSymmetryAttempt};
use crate::{Col, ColKind, Model, Sense};

/// General PB search is a trial, not a replacement for the native fallback.
/// Each phase receives a fifth of the then-remaining finite budget, capped at
/// two seconds. Ordinary models own one phase. An exactly recognized repeated-
/// block model may own a symmetry phase plus a separately bounded unaugmented
/// fallback phase, leaving at least 64% of the caller's original remaining
/// time for the native engine. A successful phase necessarily returns before
/// its cap.
const MAX_NETWORK_PB_TRIAL: Duration = Duration::from_secs(2);

/// Eager-first is useful only when the complete Hoffman master is genuinely
/// compact.  Bound projection construction independently so a larger matching
/// network cannot spend the lazy route's whole trial enumerating subsets before
/// fallback gets control.
const MAX_NETWORK_EAGER_PREFLIGHT: Duration = Duration::from_millis(100);

/// Structural candidate extraction is cheaper than eager projection and must
/// leave the PB verifier/generic fallback a live clock even on adversarial
/// many-component inputs.
const MAX_NETWORK_BLOCK_CANDIDATE_PREFLIGHT: Duration = Duration::from_millis(25);

/// Keep a small tail of the bounded PB slice for exact transshipment and the
/// source-model witness gate after a pattern-count optimum is found.
const NETWORK_PATTERN_COMPLETION_RESERVE: Duration = Duration::from_millis(100);

/// Once search has produced a conclusive network verdict, certificate posture
/// may spend a small bounded grace rebuilding and replaying the artifact.  This
/// is proof work, not a second search budget, and never crosses the caller's
/// absolute deadline.
const MAX_NETWORK_CERT_GRACE: Duration = Duration::from_secs(5);

/// Certificate construction may not consume the clock needed by the final
/// model-bound replay.  The producer gets the first half of the live proof
/// grace; the independently rebuilt network projection and PB verifier retain
/// the second half.  A tiny clock that cannot represent both halves declines.
const NETWORK_CERT_GENERATION_SHARE_DIVISOR: u32 = 2;

/// Exact PB refutation attached to a deterministically rebuilt eager Hoffman
/// projection.  The enum is private so a caller cannot manufacture a
/// network-design proof from a PB artifact without passing the model-bound
/// verifier in this module.
#[derive(Debug, Clone, PartialEq, Eq)]
enum NetworkDesignPbRefutation {
    SingleRow(SingleRowDpInfeasibilityCertificate),
    MultiRow(MultiRowBddInfeasibilityCertificate),
}

/// Independently replayable proof that the exact Hoffman master is empty.
///
/// The original-to-master equivalence is never serialized or trusted: every
/// verifier invocation recognizes and rebuilds it from the source model, then
/// replays this PB refutation against that fresh master.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NetworkDesignInfeasibilityCertificate {
    proof: NetworkDesignPbRefutation,
}

/// Independently replayable dual half of a network-design optimum.
///
/// `value` is always in the source model's objective frame. Verification
/// rebuilds any exact objective-singleton reduction plus the eager Hoffman
/// master, maps the strict-better face by the exact constant delta, proves that
/// face empty using `proof`, and separately requires the caller's source-model
/// witness to attain `value`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NetworkDesignOptimalityCertificate {
    value: BigRational,
    proof: NetworkDesignOptimalityProof,
}

/// Exact dual-side artifact for an eager network master optimum.
///
/// The legacy arm proves the strict-better face empty with a decision DAG. The
/// repeated-block arm instead replays a complete local-pattern frontier and an
/// exact block-count DP against a freshly rebuilt PB projection. Both variants
/// remain model-bound by [`verify_optimality_certificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum NetworkDesignOptimalityProof {
    StrictBetter(MultiRowBddInfeasibilityCertificate),
    PatternCount(crate::pattern_count_route::PatternCountOptimalityCertificate),
}

/// A certificate-posture result.  Feasibility needs only the exact original
/// witness; infeasibility and optimality carry their independently replayable
/// second half explicitly.
pub(crate) enum CertifiedNetworkDesignDecision {
    Feasible {
        model_values: Vec<BigRational>,
        incumbent_only: bool,
    },
    Infeasible(NetworkDesignInfeasibilityCertificate),
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
        certificate: NetworkDesignOptimalityCertificate,
    },
}

/// Production result of the certificate-first network route.
///
/// `ReadyReplay` carries a checked conclusive source-model result that did not
/// acquire a replayable certificate. `LazyOnly` means eager recognition/search
/// was consumed but the distinct lazy Hoffman/Benders arm remains available;
/// its optional payload is a checked source-model incumbent to combine with
/// that arm. Neither state may rerun eager projection, symmetry, or unaugmented
/// PB. Only `NotApplicable` authorizes the complete default route.
// This one-shot handoff is immediately consumed by `Session`; keeping payloads
// inline avoids an allocation on every network-design attempt and never nests.
#[allow(clippy::large_enum_variant)]
pub(crate) enum CertifiedNetworkDesignAttempt {
    NotApplicable,
    Decided(CertifiedNetworkDesignDecision),
    ReadyReplay(PbRouteDecision),
    LazyOnly(Option<PbRouteDecision>),
}

// Internal form of the same non-recursive, immediately consumed handoff.
#[allow(clippy::large_enum_variant)]
enum CertifiedNetworkDesignDirectAttempt {
    ReadyReplay(PbRouteDecision),
    LazyOnly(Option<PbRouteDecision>),
    Candidate {
        decision: CertifiedNetworkDesignDecision,
        replay_decision: PbRouteDecision,
        proof_deadline: Instant,
    },
}

pub(crate) fn try_solve(model: &Model, outer_deadline: Option<Instant>) -> Option<PbRouteDecision> {
    let started = Instant::now();
    let initial_trial_deadline = trial_deadline(outer_deadline, Instant::now())?;

    if needs_objective_singleton_composition(model) {
        let (reduced, postsolve) = crate::presolve::substitute_objective_singletons_with_deadline(
            model,
            Some(initial_trial_deadline),
        )?;
        let decision = try_solve_direct(&reduced, outer_deadline, initial_trial_deadline, started)?;
        return lift_objective_singleton_decision(model, &reduced, &postsolve, decision);
    }
    try_solve_direct(model, outer_deadline, initial_trial_deadline, started)
}

/// Resume only the lazy Hoffman/Benders capability after certificate-first
/// eager work has already run in this solve. This function deliberately has no
/// eager projection, symmetry, or unaugmented-portfolio path.
pub(crate) fn try_solve_lazy_only(
    model: &Model,
    outer_deadline: Option<Instant>,
    saved_incumbent: Option<PbRouteDecision>,
) -> Option<PbRouteDecision> {
    let Some(lazy_deadline) = trial_deadline(outer_deadline, Instant::now()) else {
        return saved_incumbent;
    };
    let lazy_decision = if needs_objective_singleton_composition(model) {
        let Some((reduced, postsolve)) =
            crate::presolve::substitute_objective_singletons_with_deadline(
                model,
                Some(lazy_deadline),
            )
        else {
            return saved_incumbent;
        };
        try_solve_lazy_only_direct(&reduced, lazy_deadline).and_then(|decision| {
            lift_objective_singleton_decision(model, &reduced, &postsolve, decision)
        })
    } else {
        try_solve_lazy_only_direct(model, lazy_deadline)
    };
    prefer_pb_route_decision(model, saved_incumbent, lazy_decision)
}

fn try_solve_lazy_only_direct(model: &Model, deadline: Instant) -> Option<PbRouteDecision> {
    let lazy = project_network_design_lazy(model, Some(deadline)).ok()?;
    crate::network_design_benders::try_solve_projection(model, lazy, deadline)
}

fn try_solve_direct(
    model: &Model,
    outer_deadline: Option<Instant>,
    initial_trial_deadline: Instant,
    started: Instant,
) -> Option<PbRouteDecision> {
    // Build the lazy recognition result once.  It is both the cheap component
    // census for eager-symmetry ownership and, if that attempt declines, the
    // exact state consumed by Benders below.
    let lazy = match project_network_design_lazy(model, Some(initial_trial_deadline)) {
        Ok(projection) => projection,
        Err(reason) => {
            if trace_enabled() {
                eprintln!("--trace network-pb: lazy-projection-declined={reason}");
            }
            return None;
        }
    };
    let block_symmetry_candidate = has_repeated_network_component_shape(&lazy.components);

    // A compact eager projection exposes the complete block automorphism to the
    // PB layer in one immutable model.  Try that verified symmetry route before
    // lazy separation: repeatedly solving an underconstrained design master
    // throws away the optimizer's learned state after every Hoffman cut.  A
    // failed eager construction or a symmetry miss remains cheap and leaves the
    // established lazy/native fallback authoritative.
    let mut eager = None;
    let mut symmetry_attempt = VerifiedBlockSymmetryAttempt::Declined;
    if block_symmetry_candidate {
        let eager_deadline = Instant::now()
            .checked_add(MAX_NETWORK_EAGER_PREFLIGHT)?
            .min(initial_trial_deadline);
        eager = match project_network_design(model, Some(eager_deadline)) {
            Ok(projection) => Some(projection),
            Err(reason) => {
                if trace_enabled() {
                    eprintln!("--trace network-pb: eager-projection-declined={reason}");
                }
                None
            }
        };
    }
    let mut symmetry_trial_deadline = initial_trial_deadline;
    let mut pattern_admitted = false;
    if let Some(projection) = eager.as_ref() {
        let pattern_attempt = initial_trial_deadline
            .checked_sub(NETWORK_PATTERN_COMPLETION_RESERVE)
            .filter(|deadline| *deadline > Instant::now())
            .map_or(PatternCountMasterAttempt::Declined, |pattern_deadline| {
                try_solve_pattern_count_master(projection, pattern_deadline)
            });
        if let Some(pattern) = pattern_attempt.optimum() {
            let master_decision = PbRouteDecision::Optimal {
                value: pattern.value.clone(),
                model_values: pattern.master_values.clone(),
            };
            if let Some(decision) =
                lift_network_decision(model, projection, &master_decision, initial_trial_deadline)
            {
                trace_result("eager-pattern-count", projection, &decision, started);
                return Some(decision);
            }
        }
        pattern_admitted = pattern_attempt.earns_fresh_fallback();
        if pattern_admitted {
            symmetry_trial_deadline =
                trial_deadline(outer_deadline, Instant::now()).unwrap_or(initial_trial_deadline);
        }

        let candidate_deadline = Instant::now()
            .checked_add(MAX_NETWORK_BLOCK_CANDIDATE_PREFLIGHT)
            .map_or(symmetry_trial_deadline, |limit| {
                limit.min(symmetry_trial_deadline)
            });
        let candidates = projection.adjacent_block_swap_candidates(Some(candidate_deadline));
        symmetry_attempt = crate::pb_route::try_solve_verified_block_symmetry_candidates_attempt(
            &projection.master,
            &candidates,
            symmetry_trial_deadline,
        );
        if let Some(master_decision) = symmetry_attempt.decision() {
            if pb_route_decision_is_conclusive(master_decision) {
                if let Some(decision) = lift_network_decision(
                    model,
                    projection,
                    master_decision,
                    symmetry_trial_deadline,
                ) {
                    trace_result("eager-symmetry", projection, &decision, started);
                    return Some(decision);
                }
            }
        }
    }

    // A verified pattern quotient or symmetry augmentation may consume its
    // complete structural slice before returning no decision. Reusing that
    // absolute deadline makes the next exact arm unreachable. Only an exactly
    // admitted structure receives a fresh bounded phase; ordinary and
    // nonmatching models retain the original deadline byte-for-byte.
    let fallback_deadline = if pattern_admitted {
        // Pattern admission already refreshed the one structural fallback
        // phase used by symmetry. Never grant a third phase if symmetry also
        // admits: the native engine must retain the documented 64% floor.
        symmetry_trial_deadline
    } else {
        replay_fallback_deadline(
            &symmetry_attempt,
            outer_deadline,
            symmetry_trial_deadline,
            Instant::now(),
        )?
    };
    let symmetry_master_decision = symmetry_attempt.into_decision();
    let best_incumbent = match (eager.as_ref(), symmetry_master_decision) {
        (Some(projection), Some(master_decision)) => {
            lift_network_decision(model, projection, &master_decision, fallback_deadline)
        }
        _ => None,
    };
    if best_incumbent
        .as_ref()
        .is_some_and(pb_route_decision_is_conclusive)
    {
        let decision = best_incumbent?;
        if let Some(projection) = eager.as_ref() {
            trace_result("eager-symmetry-retry", projection, &decision, started);
        }
        return Some(decision);
    }

    if let Some(decision) =
        crate::network_design_benders::try_solve_projection(model, lazy, fallback_deadline)
    {
        return prefer_pb_route_decision(model, best_incumbent, Some(decision));
    }
    if Instant::now() >= fallback_deadline {
        return best_incumbent;
    }
    let projection = match eager {
        Some(projection) => projection,
        None => project_network_design(model, Some(fallback_deadline)).ok()?,
    };
    let fallback = try_solve_portfolio_trial(&projection.master, fallback_deadline).and_then(
        |master_decision| {
            lift_network_decision(model, &projection, &master_decision, fallback_deadline)
        },
    );
    let decision = prefer_pb_route_decision(model, best_incumbent, fallback)?;
    trace_result("eager", &projection, &decision, started);
    Some(decision)
}

/// The native network recognizer deliberately owns at most one continuous
/// objective column.  More than one is the exact qnet shape: objective-only
/// aggregate columns must first be substituted before the underlying fixed-
/// charge network becomes visible.
fn needs_objective_singleton_composition(model: &Model) -> bool {
    let mut found = 0usize;
    for index in 0..model.num_cols() {
        let col = Col(index as u32);
        let coefficient = model.obj_coeff(col);
        if model.col_kind(col) == ColKind::Continuous
            && !model
                .obj_coeff_exact_at(index as u32, coefficient)
                .is_zero()
        {
            found += 1;
            if found > 1 {
                return true;
            }
        }
    }
    false
}

fn lift_objective_singleton_decision(
    source: &Model,
    reduced: &Model,
    postsolve: &crate::presolve::ObjectiveSingletonPostsolve,
    decision: PbRouteDecision,
) -> Option<PbRouteDecision> {
    match decision {
        PbRouteDecision::Infeasible
        | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
        | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => Some(PbRouteDecision::Infeasible),
        PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } => {
            reduced.check_point(&model_values).ok()?;
            let source_values = postsolve.widen(&model_values);
            source.check_point(&source_values).ok()?;
            Some(PbRouteDecision::Feasible {
                model_values: source_values,
                incumbent_only,
            })
        }
        PbRouteDecision::Optimal {
            value,
            model_values,
        } => {
            reduced.check_point(&model_values).ok()?;
            if reduced.objective_value_at(&model_values) != value {
                return None;
            }
            let source_values = postsolve.widen(&model_values);
            source.check_point(&source_values).ok()?;
            let source_value = source.objective_value_at(&source_values);
            if source_value != value + postsolve.const_delta() {
                return None;
            }
            Some(PbRouteDecision::Optimal {
                value: source_value,
                model_values: source_values,
            })
        }
    }
}

/// Cheap necessary condition for a block permutation.  It grants no
/// correctness authority (the PB detector still verifies the full augmented
/// master exactly); it only prevents one-off/asymmetric network projections
/// from paying the bounded graph-automorphism search.
fn has_repeated_network_component_shape(
    components: &[crate::network_design_pb::ProjectedNetworkComponent],
) -> bool {
    components.iter().enumerate().any(|(left_index, left)| {
        components[left_index + 1..].iter().any(|right| {
            left.balance_rows.len() == right.balance_rows.len()
                && left.flow_columns.len() == right.flow_columns.len()
                && left.retained_flows == right.retained_flows
        })
    })
}

/// Lift and independently check one result from either eager master solver.
/// Symmetry rows are search-only: this boundary checks the assignment against
/// the unaugmented master, reconstructs the exact flows, and checks the original
/// rational model before a witness can leave the route.
fn lift_network_decision(
    model: &Model,
    projection: &NetworkDesignProjection,
    master_decision: &PbRouteDecision,
    deadline: Instant,
) -> Option<PbRouteDecision> {
    match master_decision {
        PbRouteDecision::Infeasible
        | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
        | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => Some(PbRouteDecision::Infeasible),
        PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } => {
            let original_values = projection
                .complete_exact(model, model_values, Some(deadline))
                .ok()?;
            Some(PbRouteDecision::Feasible {
                model_values: original_values,
                incumbent_only: *incumbent_only,
            })
        }
        PbRouteDecision::Optimal {
            value,
            model_values,
        } => {
            let original_values = projection
                .complete_exact(model, model_values, Some(deadline))
                .ok()?;
            if &model.objective_value_at(&original_values) != value {
                return None;
            }
            Some(PbRouteDecision::Optimal {
                value: value.clone(),
                model_values: original_values,
            })
        }
    }
}

struct PatternCountMasterOptimum {
    value: BigRational,
    master_values: Vec<BigRational>,
    certificate: crate::pattern_count_route::PatternCountOptimalityCertificate,
}

enum PatternCountMasterAttempt {
    Declined,
    Admitted(Option<PatternCountMasterOptimum>),
}

impl PatternCountMasterAttempt {
    fn optimum(&self) -> Option<&PatternCountMasterOptimum> {
        match self {
            Self::Admitted(Some(optimum)) => Some(optimum),
            Self::Declined | Self::Admitted(None) => None,
        }
    }

    fn earns_fresh_fallback(&self) -> bool {
        matches!(self, Self::Admitted(_))
    }
}

/// Solve a complete repeated-block eager master by exact local-pattern
/// projection plus a packing-count DP. Network descriptors supply only ordered
/// candidates. The PB lift, ordered-partition verifier, classifier, full-plan
/// checks, and exact objective map all remain authoritative at this boundary.
fn try_solve_pattern_count_master(
    projection: &NetworkDesignProjection,
    deadline: Instant,
) -> PatternCountMasterAttempt {
    let plan = match crate::pb_translate::translate(&projection.master, Some(deadline)) {
        Ok(plan) => plan,
        Err(reason) => {
            if trace_enabled() {
                eprintln!("--trace network-pattern-count: translate-declined={reason:?}");
            }
            return PatternCountMasterAttempt::Declined;
        }
    };
    let Some(objective) = plan.objective.as_ref() else {
        if trace_enabled() {
            eprintln!("--trace network-pattern-count: no-objective");
        }
        return PatternCountMasterAttempt::Declined;
    };
    let families = projection.ordered_interchangeable_block_families(Some(deadline));
    if trace_enabled() {
        eprintln!(
            "--trace network-pattern-count: families={} pb-vars={} rows={}",
            families.len(),
            plan.num_vars,
            plan.num_constraints
        );
    }
    for family in families {
        if Instant::now() >= deadline {
            return PatternCountMasterAttempt::Declined;
        }
        let Some(blocks) = plan.lift_model_column_blocks_to_pb(&family) else {
            if trace_enabled() {
                eprintln!("--trace network-pattern-count: block-lift-declined");
            }
            continue;
        };
        let attempt = crate::pattern_count_route::attempt_solve_exact_pattern_count(
            &plan,
            &blocks,
            Some(deadline),
        );
        let result = match attempt {
            crate::pattern_count_route::PatternCountSolveAttempt::Declined(reason) => {
                if trace_enabled() {
                    eprintln!("--trace network-pattern-count: partition-declined={reason:?}");
                }
                continue;
            }
            crate::pattern_count_route::PatternCountSolveAttempt::VerifiedDeclined(reason) => {
                if trace_enabled() {
                    eprintln!("--trace network-pattern-count: quotient-declined={reason:?}");
                }
                return PatternCountMasterAttempt::Admitted(None);
            }
            crate::pattern_count_route::PatternCountSolveAttempt::Admitted(result) => result,
        };
        let solution = match result {
            Ok(Some(solution)) => solution,
            Ok(None) => {
                if trace_enabled() {
                    eprintln!("--trace network-pattern-count: exact-infeasible");
                }
                return PatternCountMasterAttempt::Admitted(None);
            }
            Err(reason) => {
                if trace_enabled() {
                    eprintln!("--trace network-pattern-count: solve-declined={reason:?}");
                }
                return PatternCountMasterAttempt::Admitted(None);
            }
        };
        if objective.value_at(&solution.assignment) != Some(solution.pb_value)
            || solution.certificate.pb_value != solution.pb_value
        {
            return PatternCountMasterAttempt::Admitted(None);
        }
        let Some(master_values) = plan.lift(&solution.assignment) else {
            return PatternCountMasterAttempt::Admitted(None);
        };
        if projection.master.check_point(&master_values).is_err() {
            return PatternCountMasterAttempt::Admitted(None);
        }
        let value = objective.map.model_value(solution.pb_value);
        if projection.master.objective_value_at(&master_values) != value {
            return PatternCountMasterAttempt::Admitted(None);
        }
        return PatternCountMasterAttempt::Admitted(Some(PatternCountMasterOptimum {
            value,
            master_values,
            certificate: solution.certificate,
        }));
    }
    PatternCountMasterAttempt::Declined
}

fn trace_result(
    engine: &str,
    projection: &NetworkDesignProjection,
    decision: &PbRouteDecision,
    started: Instant,
) {
    if trace_enabled() {
        let verdict = match decision {
            PbRouteDecision::Feasible { .. } => "FEASIBLE",
            PbRouteDecision::Infeasible
            | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
            | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => "INFEASIBLE",
            PbRouteDecision::Optimal { .. } => "OPTIMAL",
        };
        eprintln!(
            "--trace network-pb: engine={} master-cols={} master-rows={} components={} \
             hoffman-rows={} verdict={} wall={:.6}s",
            engine,
            projection.master.num_cols(),
            projection.master.num_rows(),
            projection.components.len(),
            projection.hoffman_rows,
            verdict,
            started.elapsed().as_secs_f64(),
        );
    }
}

/// Solve the eager exact projection only when the complete claim can leave the
/// process as a typed artifact.  This entry point is used by `--require full`;
/// any proof export/replay failure declines to the native proof-producing path
/// instead of turning a valid but uncheckable network result into `Unknown`.
#[cfg(test)]
pub(crate) fn try_solve_certified(
    model: &Model,
    outer_deadline: Option<Instant>,
) -> Option<CertifiedNetworkDesignDecision> {
    match try_solve_certified_attempt(model, outer_deadline) {
        CertifiedNetworkDesignAttempt::Decided(decision) => Some(decision),
        CertifiedNetworkDesignAttempt::NotApplicable
        | CertifiedNetworkDesignAttempt::ReadyReplay(_)
        | CertifiedNetworkDesignAttempt::LazyOnly(_) => None,
    }
}

pub(crate) fn try_solve_certified_attempt(
    model: &Model,
    outer_deadline: Option<Instant>,
) -> CertifiedNetworkDesignAttempt {
    let Some(initial_trial_deadline) = trial_deadline(outer_deadline, Instant::now()) else {
        return CertifiedNetworkDesignAttempt::NotApplicable;
    };
    if needs_objective_singleton_composition(model) {
        let Some((reduced, postsolve)) =
            crate::presolve::substitute_objective_singletons_with_deadline(
                model,
                Some(initial_trial_deadline),
            )
        else {
            return CertifiedNetworkDesignAttempt::NotApplicable;
        };
        return match try_solve_certified_direct(&reduced, outer_deadline, initial_trial_deadline) {
            CertifiedNetworkDesignDirectAttempt::ReadyReplay(replay_decision) => replay_handoff(
                lift_objective_singleton_decision(model, &reduced, &postsolve, replay_decision),
            ),
            CertifiedNetworkDesignDirectAttempt::LazyOnly(replay_decision) => {
                CertifiedNetworkDesignAttempt::LazyOnly(replay_decision.and_then(|decision| {
                    lift_objective_singleton_decision(model, &reduced, &postsolve, decision)
                }))
            }
            CertifiedNetworkDesignDirectAttempt::Candidate {
                decision,
                replay_decision,
                proof_deadline,
            } => {
                let replay_decision =
                    lift_objective_singleton_decision(model, &reduced, &postsolve, replay_decision);
                let Some(decision) = lift_objective_singleton_certified_decision(
                    model, &reduced, &postsolve, decision,
                ) else {
                    return replay_handoff(replay_decision);
                };
                finish_certified_attempt(model, decision, replay_decision, proof_deadline)
            }
        };
    }

    match try_solve_certified_direct(model, outer_deadline, initial_trial_deadline) {
        CertifiedNetworkDesignDirectAttempt::ReadyReplay(replay_decision) => {
            CertifiedNetworkDesignAttempt::ReadyReplay(replay_decision)
        }
        CertifiedNetworkDesignDirectAttempt::LazyOnly(replay_decision) => {
            CertifiedNetworkDesignAttempt::LazyOnly(replay_decision)
        }
        CertifiedNetworkDesignDirectAttempt::Candidate {
            decision,
            replay_decision,
            proof_deadline,
        } => finish_certified_attempt(model, decision, Some(replay_decision), proof_deadline),
    }
}

fn finish_certified_attempt(
    model: &Model,
    decision: CertifiedNetworkDesignDecision,
    replay_decision: Option<PbRouteDecision>,
    proof_deadline: Instant,
) -> CertifiedNetworkDesignAttempt {
    let verified = match &decision {
        CertifiedNetworkDesignDecision::Infeasible(certificate) => {
            verify_infeasibility_certificate_with_deadline(model, certificate, Some(proof_deadline))
                .is_ok()
        }
        CertifiedNetworkDesignDecision::Optimal {
            value, certificate, ..
        } => verify_optimality_certificate_with_deadline(
            model,
            value,
            certificate,
            Some(proof_deadline),
        )
        .is_ok(),
        CertifiedNetworkDesignDecision::Feasible { model_values, .. } => {
            model.check_point(model_values).is_ok()
        }
    };
    if verified {
        CertifiedNetworkDesignAttempt::Decided(decision)
    } else if matches!(&decision, CertifiedNetworkDesignDecision::Feasible { .. }) {
        // The replay payload contains the same point. If the independent
        // source check rejected it, it cannot seed lazy continuation.
        CertifiedNetworkDesignAttempt::LazyOnly(None)
    } else {
        replay_handoff(replay_decision)
    }
}

fn replay_handoff(replay_decision: Option<PbRouteDecision>) -> CertifiedNetworkDesignAttempt {
    match replay_decision {
        Some(decision) if pb_route_decision_is_conclusive(&decision) => {
            CertifiedNetworkDesignAttempt::ReadyReplay(decision)
        }
        decision => CertifiedNetworkDesignAttempt::LazyOnly(decision),
    }
}

fn try_solve_certified_direct(
    model: &Model,
    outer_deadline: Option<Instant>,
    initial_trial_deadline: Instant,
) -> CertifiedNetworkDesignDirectAttempt {
    let projection = match project_network_design(model, Some(initial_trial_deadline)) {
        Ok(projection) => projection,
        Err(_) => return CertifiedNetworkDesignDirectAttempt::LazyOnly(None),
    };
    let pattern_attempt = initial_trial_deadline
        .checked_sub(NETWORK_PATTERN_COMPLETION_RESERVE)
        .filter(|deadline| *deadline > Instant::now())
        .map_or(PatternCountMasterAttempt::Declined, |pattern_deadline| {
            try_solve_pattern_count_master(&projection, pattern_deadline)
        });
    if let Some(pattern) = pattern_attempt.optimum() {
        if let Some(proof_deadline) = certificate_deadline(outer_deadline, Instant::now()) {
            if let Some(completion_deadline) =
                certificate_generation_deadline(proof_deadline, Instant::now())
            {
                if let Ok(original_values) = projection.complete_exact(
                    model,
                    &pattern.master_values,
                    Some(completion_deadline),
                ) {
                    let value = model.objective_value_at(&original_values);
                    if value == pattern.value {
                        let replay_decision = PbRouteDecision::Optimal {
                            value: value.clone(),
                            model_values: original_values.clone(),
                        };
                        return CertifiedNetworkDesignDirectAttempt::Candidate {
                            decision: CertifiedNetworkDesignDecision::Optimal {
                                value: value.clone(),
                                model_values: original_values,
                                certificate: NetworkDesignOptimalityCertificate {
                                    value,
                                    proof: NetworkDesignOptimalityProof::PatternCount(
                                        pattern.certificate.clone(),
                                    ),
                                },
                            },
                            replay_decision,
                            proof_deadline,
                        };
                    }
                }
            }
        }
    }
    let pattern_admitted = pattern_attempt.earns_fresh_fallback();
    let symmetry_trial_deadline = if pattern_admitted {
        trial_deadline(outer_deadline, Instant::now()).unwrap_or(initial_trial_deadline)
    } else {
        initial_trial_deadline
    };

    // Repeated network blocks expose an exact automorphism in the complete
    // Hoffman master.  Use the same verified symmetry-first search as the
    // replay route before trying the unaugmented portfolio.  Previously the
    // certificate lane spent its complete network slice on the unaugmented
    // master and the replay lane then rebuilt and searched the same projection
    // with symmetry.  Besides duplicating work, that ordering could reach a
    // fast symmetry result only after the outer deadline.  The lex rows remain
    // search-only: every optimality/refutation artifact below is still produced
    // and replayed against `projection.master`, never the augmented instance.
    let repeated_blocks = has_repeated_network_component_shape(&projection.components);
    let symmetry_attempt = if repeated_blocks {
        let candidate_deadline = Instant::now()
            .checked_add(MAX_NETWORK_BLOCK_CANDIDATE_PREFLIGHT)
            .map_or(symmetry_trial_deadline, |limit| {
                limit.min(symmetry_trial_deadline)
            });
        let candidates = projection.adjacent_block_swap_candidates(Some(candidate_deadline));
        crate::pb_route::try_solve_verified_block_symmetry_candidates_attempt(
            &projection.master,
            &candidates,
            symmetry_trial_deadline,
        )
    } else {
        VerifiedBlockSymmetryAttempt::Declined
    };
    let symmetry_is_conclusive = symmetry_attempt
        .decision()
        .is_some_and(pb_route_decision_is_conclusive);
    let symmetry_earns_fallback = symmetry_attempt.earns_fresh_fallback();
    let symmetry_decision = symmetry_attempt.into_decision();
    let master_decision = if symmetry_is_conclusive {
        let Some(decision) = symmetry_decision else {
            return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
        };
        decision
    } else if symmetry_earns_fallback && !pattern_admitted {
        // An exactly admitted augmentation owns the first structural slice and
        // cannot share its spent deadline with the legacy unaugmented
        // portfolio. Recompute one bounded slice from the still-live outer
        // deadline. A pre-admission decline instead falls into the branch below
        // and keeps the original clock byte-for-byte.
        let Some(fallback_deadline) = trial_deadline(outer_deadline, Instant::now()) else {
            return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
        };
        let fallback = try_solve_portfolio_trial(&projection.master, fallback_deadline);
        let Some(decision) =
            prefer_pb_route_decision(&projection.master, symmetry_decision, fallback)
        else {
            return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
        };
        decision
    } else {
        let fallback = try_solve_portfolio_trial(&projection.master, symmetry_trial_deadline);
        let Some(decision) =
            prefer_pb_route_decision(&projection.master, symmetry_decision, fallback)
        else {
            return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
        };
        decision
    };
    let Some(proof_deadline) = certificate_deadline(outer_deadline, Instant::now()) else {
        let replay_decision = matches!(
            master_decision,
            PbRouteDecision::Infeasible
                | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
                | PbRouteDecision::CertifiedMultiRowInfeasible { .. }
        )
        .then_some(PbRouteDecision::Infeasible);
        return match replay_decision {
            Some(decision) => CertifiedNetworkDesignDirectAttempt::ReadyReplay(decision),
            None => CertifiedNetworkDesignDirectAttempt::LazyOnly(None),
        };
    };
    let (decision, replay_decision) = match master_decision {
        PbRouteDecision::CertifiedSingleRowInfeasible { certificate } => (
            CertifiedNetworkDesignDecision::Infeasible(NetworkDesignInfeasibilityCertificate {
                proof: NetworkDesignPbRefutation::SingleRow(certificate),
            }),
            PbRouteDecision::Infeasible,
        ),
        PbRouteDecision::CertifiedMultiRowInfeasible { certificate } => (
            CertifiedNetworkDesignDecision::Infeasible(NetworkDesignInfeasibilityCertificate {
                proof: NetworkDesignPbRefutation::MultiRow(certificate),
            }),
            PbRouteDecision::Infeasible,
        ),
        // A bare exhaustive verdict is valid in the default posture.  Give its
        // separately bounded proof pass the certificate grace; only a typed
        // model-bound refutation may leave this entry point.
        PbRouteDecision::Infeasible => {
            let replay_decision = PbRouteDecision::Infeasible;
            let Some(generation_deadline) =
                certificate_generation_deadline(proof_deadline, Instant::now())
            else {
                return CertifiedNetworkDesignDirectAttempt::ReadyReplay(replay_decision);
            };
            let Some(certificate) =
                crate::pb_route::try_generate_network_multi_row_infeasibility_certificate(
                    &projection.master,
                    generation_deadline,
                )
            else {
                return CertifiedNetworkDesignDirectAttempt::ReadyReplay(replay_decision);
            };
            (
                CertifiedNetworkDesignDecision::Infeasible(NetworkDesignInfeasibilityCertificate {
                    proof: NetworkDesignPbRefutation::MultiRow(certificate),
                }),
                replay_decision,
            )
        }
        PbRouteDecision::Feasible {
            model_values,
            incumbent_only,
        } => {
            let Ok(original_values) =
                projection.complete_exact(model, &model_values, Some(proof_deadline))
            else {
                return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
            };
            (
                CertifiedNetworkDesignDecision::Feasible {
                    model_values: original_values.clone(),
                    incumbent_only,
                },
                PbRouteDecision::Feasible {
                    model_values: original_values,
                    incumbent_only,
                },
            )
        }
        PbRouteDecision::Optimal {
            value,
            model_values,
        } => {
            let Some(generation_deadline) =
                certificate_generation_deadline(proof_deadline, Instant::now())
            else {
                return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
            };
            let Ok(original_values) =
                projection.complete_exact(model, &model_values, Some(generation_deadline))
            else {
                return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
            };
            if model.objective_value_at(&original_values) != value {
                return CertifiedNetworkDesignDirectAttempt::LazyOnly(None);
            }
            let replay_decision = PbRouteDecision::Optimal {
                value: value.clone(),
                model_values: original_values.clone(),
            };
            let Some(proof) = crate::pb_route::try_generate_network_objective_bound_certificate(
                &projection.master,
                &value,
                generation_deadline,
            ) else {
                return CertifiedNetworkDesignDirectAttempt::ReadyReplay(replay_decision);
            };
            (
                CertifiedNetworkDesignDecision::Optimal {
                    value: value.clone(),
                    model_values: original_values,
                    certificate: NetworkDesignOptimalityCertificate {
                        value,
                        proof: NetworkDesignOptimalityProof::StrictBetter(proof),
                    },
                },
                replay_decision,
            )
        }
    };

    CertifiedNetworkDesignDirectAttempt::Candidate {
        decision,
        replay_decision,
        proof_deadline,
    }
}

fn lift_objective_singleton_certified_decision(
    source: &Model,
    reduced: &Model,
    postsolve: &crate::presolve::ObjectiveSingletonPostsolve,
    decision: CertifiedNetworkDesignDecision,
) -> Option<CertifiedNetworkDesignDecision> {
    match decision {
        CertifiedNetworkDesignDecision::Infeasible(certificate) => {
            Some(CertifiedNetworkDesignDecision::Infeasible(certificate))
        }
        CertifiedNetworkDesignDecision::Feasible {
            model_values,
            incumbent_only,
        } => {
            reduced.check_point(&model_values).ok()?;
            let source_values = postsolve.widen(&model_values);
            source.check_point(&source_values).ok()?;
            Some(CertifiedNetworkDesignDecision::Feasible {
                model_values: source_values,
                incumbent_only,
            })
        }
        CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            mut certificate,
        } => {
            reduced.check_point(&model_values).ok()?;
            if reduced.objective_value_at(&model_values) != value || certificate.value != value {
                return None;
            }
            let source_values = postsolve.widen(&model_values);
            source.check_point(&source_values).ok()?;
            let source_value = source.objective_value_at(&source_values);
            if source_value != value + postsolve.const_delta() {
                return None;
            }
            certificate.value = source_value.clone();
            Some(CertifiedNetworkDesignDecision::Optimal {
                value: source_value,
                model_values: source_values,
                certificate,
            })
        }
    }
}

struct RebuiltNetworkProjection {
    projection: NetworkDesignProjection,
    /// `source objective = rebuilt-master objective + objective_delta`.
    objective_delta: BigRational,
}

fn rebuild_network_projection(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<RebuiltNetworkProjection, String> {
    if needs_objective_singleton_composition(model) {
        let (reduced, postsolve) =
            crate::presolve::substitute_objective_singletons_with_deadline(model, deadline)
                .ok_or_else(|| {
                    "objective-singleton reduction rebuild declined or exceeded deadline".to_owned()
                })?;
        let projection = project_network_design(&reduced, deadline)
            .map_err(|reason| format!("network-design projection rebuild declined: {reason}"))?;
        return Ok(RebuiltNetworkProjection {
            projection,
            objective_delta: postsolve.const_delta().clone(),
        });
    }

    let projection = project_network_design(model, deadline)
        .map_err(|reason| format!("network-design projection rebuild declined: {reason}"))?;
    Ok(RebuiltNetworkProjection {
        projection,
        objective_delta: BigRational::zero(),
    })
}

/// Rebuild the exact eager Hoffman projection and replay an infeasibility
/// artifact against the rebuilt master.
pub fn verify_infeasibility_certificate(
    model: &Model,
    certificate: &NetworkDesignInfeasibilityCertificate,
) -> Result<(), String> {
    verify_infeasibility_certificate_with_deadline(model, certificate, None)
}

fn verify_infeasibility_certificate_with_deadline(
    model: &Model,
    certificate: &NetworkDesignInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    let rebuilt = rebuild_network_projection(model, deadline)?;
    match &certificate.proof {
        NetworkDesignPbRefutation::SingleRow(proof) => {
            crate::pb_route::verify_single_row_infeasibility_certificate_with_deadline(
                &rebuilt.projection.master,
                proof,
                deadline,
            )
        }
        NetworkDesignPbRefutation::MultiRow(proof) => {
            crate::pb_route::verify_multi_row_infeasibility_certificate_with_deadline(
                &rebuilt.projection.master,
                proof,
                deadline,
            )
        }
    }
}

/// Rebuild the exact eager Hoffman projection and prove that no master point
/// has an objective strictly better than `claimed_value`.
pub fn verify_optimality_certificate(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &NetworkDesignOptimalityCertificate,
) -> Result<(), String> {
    verify_optimality_certificate_with_deadline(model, claimed_value, certificate, None)
}

fn verify_optimality_certificate_with_deadline(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &NetworkDesignOptimalityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    if &certificate.value != claimed_value {
        return Err(format!(
            "network-design artifact value {} does not match claimed optimum {claimed_value}",
            certificate.value
        ));
    }
    let rebuilt = rebuild_network_projection(model, deadline)?;
    let reduced_value = claimed_value - &rebuilt.objective_delta;
    match &certificate.proof {
        NetworkDesignOptimalityProof::StrictBetter(proof) => {
            crate::pb_route::verify_objective_bound_with_deadline(
                &rebuilt.projection.master,
                &reduced_value,
                proof,
                deadline,
            )
        }
        NetworkDesignOptimalityProof::PatternCount(proof) => {
            let plan = crate::pb_translate::translate(&rebuilt.projection.master, deadline)
                .map_err(|reason| {
                    format!("network-design pattern-count PB rebuild declined: {reason:?}")
                })?;
            let objective = plan.objective.as_ref().ok_or_else(|| {
                "network-design pattern-count optimum has no rebuilt PB objective".to_owned()
            })?;
            let expected_pb_value = objective.map.pb_value(&reduced_value).ok_or_else(|| {
                "claimed network-design optimum is outside the rebuilt PB objective lattice"
                    .to_owned()
            })?;
            let replay =
                crate::pattern_count_route::verify_pattern_count_optimality(&plan, proof, deadline)
                    .map_err(|reason| {
                        format!("network-design pattern-count artifact replay declined: {reason:?}")
                    })?;
            if replay.pb_value != expected_pb_value {
                return Err(format!(
                    "network-design pattern-count optimum {} does not match rebuilt PB value \
                     {expected_pb_value}",
                    replay.pb_value
                ));
            }
            let master_values = plan.lift(&replay.assignment).ok_or_else(|| {
                "network-design pattern-count assignment did not lift to the rebuilt master"
                    .to_owned()
            })?;
            rebuilt
                .projection
                .master
                .check_point(&master_values)
                .map_err(|error| {
                    format!(
                        "network-design pattern-count assignment failed rebuilt-master check: \
                         {error:?}"
                    )
                })?;
            if rebuilt.projection.master.objective_value_at(&master_values) != reduced_value {
                return Err(
                    "network-design pattern-count assignment does not attain the rebuilt value"
                        .to_owned(),
                );
            }
            Ok(())
        }
    }
}

pub(crate) enum NetworkDesignPbRefutationRef<'a> {
    SingleRow(&'a SingleRowDpInfeasibilityCertificate),
    MultiRow(&'a MultiRowBddInfeasibilityCertificate),
}

pub(crate) fn infeasibility_refutation(
    certificate: &NetworkDesignInfeasibilityCertificate,
) -> NetworkDesignPbRefutationRef<'_> {
    match &certificate.proof {
        NetworkDesignPbRefutation::SingleRow(proof) => {
            NetworkDesignPbRefutationRef::SingleRow(proof)
        }
        NetworkDesignPbRefutation::MultiRow(proof) => NetworkDesignPbRefutationRef::MultiRow(proof),
    }
}

pub(crate) enum NetworkDesignOptimalityProofRef<'a> {
    StrictBetter(&'a MultiRowBddInfeasibilityCertificate),
    PatternCount(&'a crate::pattern_count_route::PatternCountOptimalityCertificate),
}

pub(crate) fn optimality_parts(
    certificate: &NetworkDesignOptimalityCertificate,
) -> (&BigRational, NetworkDesignOptimalityProofRef<'_>) {
    let proof = match &certificate.proof {
        NetworkDesignOptimalityProof::StrictBetter(proof) => {
            NetworkDesignOptimalityProofRef::StrictBetter(proof)
        }
        NetworkDesignOptimalityProof::PatternCount(proof) => {
            NetworkDesignOptimalityProofRef::PatternCount(proof)
        }
    };
    (&certificate.value, proof)
}

pub(crate) fn infeasibility_from_single_row(
    proof: SingleRowDpInfeasibilityCertificate,
) -> NetworkDesignInfeasibilityCertificate {
    NetworkDesignInfeasibilityCertificate {
        proof: NetworkDesignPbRefutation::SingleRow(proof),
    }
}

pub(crate) fn infeasibility_from_multi_row(
    proof: MultiRowBddInfeasibilityCertificate,
) -> NetworkDesignInfeasibilityCertificate {
    NetworkDesignInfeasibilityCertificate {
        proof: NetworkDesignPbRefutation::MultiRow(proof),
    }
}

pub(crate) fn optimality_from_strict_better(
    value: BigRational,
    proof: MultiRowBddInfeasibilityCertificate,
) -> NetworkDesignOptimalityCertificate {
    NetworkDesignOptimalityCertificate {
        value,
        proof: NetworkDesignOptimalityProof::StrictBetter(proof),
    }
}

pub(crate) fn optimality_from_pattern_count(
    value: BigRational,
    proof: crate::pattern_count_route::PatternCountOptimalityCertificate,
) -> NetworkDesignOptimalityCertificate {
    NetworkDesignOptimalityCertificate {
        value,
        proof: NetworkDesignOptimalityProof::PatternCount(proof),
    }
}

fn pb_route_decision_is_conclusive(decision: &PbRouteDecision) -> bool {
    !matches!(decision, PbRouteDecision::Feasible { .. })
}

/// Prefer a proof-bearing/conclusive decision over an incumbent, otherwise
/// retain the better exact incumbent for the model's objective sense.
///
/// Both arguments have already crossed their producing route's exact
/// source-model result gate. This helper only combines independently valid
/// results; it cannot create a verdict or authorize a proof.
fn prefer_pb_route_decision(
    model: &Model,
    first: Option<PbRouteDecision>,
    second: Option<PbRouteDecision>,
) -> Option<PbRouteDecision> {
    let (first, second) = match (first, second) {
        (Some(first), Some(second)) => (first, second),
        (Some(first), None) => return Some(first),
        (None, Some(second)) => return Some(second),
        (None, None) => return None,
    };
    let first_is_infeasible = pb_route_decision_is_infeasible(&first);
    let second_is_infeasible = pb_route_decision_is_infeasible(&second);
    let first_has_witness = pb_route_decision_has_witness(&first);
    let second_has_witness = pb_route_decision_has_witness(&second);

    // A checked point is a complete refutation of infeasibility.  Never let a
    // contradictory terminal claim erase the counterexample already in hand.
    if (first_is_infeasible && second_has_witness) || (second_is_infeasible && first_has_witness) {
        return best_checked_witness_as_feasible(model, first, second);
    }
    if first_is_infeasible && second_is_infeasible {
        return if matches!(&first, PbRouteDecision::Infeasible)
            && !matches!(&second, PbRouteDecision::Infeasible)
        {
            Some(second)
        } else {
            Some(first)
        };
    }

    match (&first, &second) {
        (
            PbRouteDecision::Optimal {
                value: first_value,
                model_values: first_values,
            },
            PbRouteDecision::Optimal {
                value: second_value,
                model_values: second_values,
            },
        ) => {
            let first_attained = model.objective_value_at(first_values);
            let second_attained = model.objective_value_at(second_values);
            if first_attained == *first_value
                && second_attained == *second_value
                && first_value == second_value
            {
                return Some(first);
            }
            return best_checked_witness_as_feasible(model, first, second);
        }
        (
            PbRouteDecision::Optimal {
                value,
                model_values,
            },
            PbRouteDecision::Feasible {
                model_values: feasible_values,
                ..
            },
        ) => {
            let attained = model.objective_value_at(model_values);
            let feasible_value = model.objective_value_at(feasible_values);
            if attained == *value && objective_bound_covers(model, value, &feasible_value) {
                return Some(first);
            }
            return best_checked_witness_as_feasible(model, first, second);
        }
        (
            PbRouteDecision::Feasible {
                model_values: feasible_values,
                ..
            },
            PbRouteDecision::Optimal {
                value,
                model_values,
            },
        ) => {
            let attained = model.objective_value_at(model_values);
            let feasible_value = model.objective_value_at(feasible_values);
            if attained == *value && objective_bound_covers(model, value, &feasible_value) {
                return Some(second);
            }
            return best_checked_witness_as_feasible(model, first, second);
        }
        _ => {}
    }

    let PbRouteDecision::Feasible {
        model_values: first_values,
        incumbent_only: first_incumbent_only,
    } = &first
    else {
        return Some(first);
    };
    let PbRouteDecision::Feasible {
        model_values: second_values,
        incumbent_only: second_incumbent_only,
    } = &second
    else {
        return Some(second);
    };
    let first_value = model.objective_value_at(first_values);
    let second_value = model.objective_value_at(second_values);
    let second_is_better = match model.sense() {
        Sense::Minimize => second_value < first_value,
        Sense::Maximize => second_value > first_value,
    };
    if second_is_better
        || (second_value == first_value && *first_incumbent_only && !*second_incumbent_only)
    {
        Some(second)
    } else {
        Some(first)
    }
}

fn pb_route_decision_is_infeasible(decision: &PbRouteDecision) -> bool {
    matches!(
        decision,
        PbRouteDecision::Infeasible
            | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
            | PbRouteDecision::CertifiedMultiRowInfeasible { .. }
    )
}

fn pb_route_decision_has_witness(decision: &PbRouteDecision) -> bool {
    matches!(
        decision,
        PbRouteDecision::Feasible { .. } | PbRouteDecision::Optimal { .. }
    )
}

fn objective_bound_covers(
    model: &Model,
    claimed_optimum: &BigRational,
    feasible_value: &BigRational,
) -> bool {
    match model.sense() {
        Sense::Minimize => claimed_optimum <= feasible_value,
        Sense::Maximize => claimed_optimum >= feasible_value,
    }
}

/// Internal disagreement removes every terminal claim. Independently recheck
/// each candidate against the source model, then retain the better surviving
/// witness as an anytime result. Producer contracts are not enough at this
/// conflict boundary: an invalid point must not veto a refutation or become an
/// incumbent.
fn best_checked_witness_as_feasible(
    model: &Model,
    first: PbRouteDecision,
    second: PbRouteDecision,
) -> Option<PbRouteDecision> {
    let first_values = match first {
        PbRouteDecision::Feasible { model_values, .. }
        | PbRouteDecision::Optimal { model_values, .. } => Some(model_values),
        PbRouteDecision::Infeasible
        | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
        | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => None,
    }
    .filter(|model_values| model.check_point(model_values).is_ok());
    let second_values = match second {
        PbRouteDecision::Feasible { model_values, .. }
        | PbRouteDecision::Optimal { model_values, .. } => Some(model_values),
        PbRouteDecision::Infeasible
        | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
        | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => None,
    }
    .filter(|model_values| model.check_point(model_values).is_ok());
    let model_values = match (first_values, second_values) {
        (Some(first_values), Some(second_values)) => {
            let first_value = model.objective_value_at(&first_values);
            let second_value = model.objective_value_at(&second_values);
            let second_is_better = match model.sense() {
                Sense::Minimize => second_value < first_value,
                Sense::Maximize => second_value > first_value,
            };
            if second_is_better {
                second_values
            } else {
                first_values
            }
        }
        (Some(values), None) | (None, Some(values)) => values,
        (None, None) => return None,
    };
    Some(PbRouteDecision::Feasible {
        model_values,
        incumbent_only: model.has_objective(),
    })
}

/// Select the deadline owned by the default/replay fallback phase.
///
/// A changed, exactly validated, compact admitted augmentation earns one fresh
/// bounded phase from the still-live outer clock. Every pre-admission decline
/// returns the original live deadline exactly; a count-only component match or
/// expired detector therefore cannot enlarge this route's budget.
fn replay_fallback_deadline(
    symmetry_attempt: &VerifiedBlockSymmetryAttempt,
    outer: Option<Instant>,
    initial: Instant,
    now: Instant,
) -> Option<Instant> {
    if symmetry_attempt.earns_fresh_fallback() {
        trial_deadline(outer, now)
    } else {
        (initial > now).then_some(initial)
    }
}

fn trial_deadline(outer: Option<Instant>, now: Instant) -> Option<Instant> {
    let slice = match outer {
        Some(deadline) => {
            let remaining = deadline.checked_duration_since(now)?;
            if remaining.is_zero() {
                return None;
            }
            (remaining / 5).min(MAX_NETWORK_PB_TRIAL)
        }
        None => MAX_NETWORK_PB_TRIAL,
    };
    (!slice.is_zero()).then(|| now + slice)
}

fn certificate_deadline(outer: Option<Instant>, now: Instant) -> Option<Instant> {
    let ceiling = now.checked_add(MAX_NETWORK_CERT_GRACE)?;
    match outer {
        Some(deadline) if deadline > now => Some(deadline.min(ceiling)),
        Some(_) => None,
        None => Some(ceiling),
    }
}

fn certificate_generation_deadline(final_deadline: Instant, now: Instant) -> Option<Instant> {
    let remaining = final_deadline.checked_duration_since(now)?;
    let generation = remaining / NETWORK_CERT_GENERATION_SHARE_DIVISOR;
    (!generation.is_zero()).then(|| now + generation)
}

fn trace_enabled() -> bool {
    // Cached: the ratchet in `tests/env_ledger.rs` counts a bare `env::var_os`
    // on the solve path as a LIVE read — a fresh `getenv` a concurrent
    // `set_var` can race, which priming cannot help. `OnceLock` is the shape
    // that ratchet asks for and `simplex.rs` already uses.
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BabSession, Col, Outcome, Sense, SolveOpts};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn rational(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn one_arc_model(enabled_ub: f64) -> Model {
        let mut model = Model::new();
        let flow = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.set_col_bounds(enabled, 0.0, enabled_ub);

        // objective = 5*enabled; one unit must enter the balance node and the
        // capacity controller licenses exactly that flow when enabled.
        model.add_row(0.0, 0.0, &[(objective, 1.0), (enabled, -5.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        model.add_row(1.0, 1.0, &[(flow, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        model
    }

    fn two_identical_arc_components_model() -> Model {
        let mut model = Model::new();
        let first_flow = model.add_col(0.0, f64::INFINITY);
        let second_flow = model.add_col(0.0, f64::INFINITY);
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let first_enabled = model.add_binary_col();
        let second_enabled = model.add_binary_col();

        model.add_row(
            0.0,
            0.0,
            &[
                (objective, 1.0),
                (first_enabled, -5.0),
                (second_enabled, -5.0),
            ],
        );
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);
        for (flow, enabled) in [(first_flow, first_enabled), (second_flow, second_enabled)] {
            model.add_row(1.0, 1.0, &[(flow, 1.0)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        }
        model
    }

    fn two_identical_components_with_separate_objectives() -> Model {
        let mut model = Model::new();
        let first_flow = model.add_col(0.0, f64::INFINITY);
        let second_flow = model.add_col(0.0, f64::INFINITY);
        let first_objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let second_objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let first_enabled = model.add_binary_col();
        let second_enabled = model.add_binary_col();

        for (objective, enabled) in [
            (first_objective, first_enabled),
            (second_objective, second_enabled),
        ] {
            model.add_row(0.0, 0.0, &[(objective, 1.0), (enabled, -5.0)]);
        }
        model.set_objective(
            &[(first_objective, 1.0), (second_objective, 1.0)],
            Sense::Minimize,
        );
        for (flow, enabled) in [(first_flow, first_enabled), (second_flow, second_enabled)] {
            model.add_row(1.0, 1.0, &[(flow, 1.0)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        }
        model
    }

    fn multi_objective_arc_model(enabled_ub: f64) -> Model {
        let mut model = Model::new();
        let flow = model.add_col(0.0, f64::INFINITY);
        let first_cost = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let second_cost = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let enabled = model.add_binary_col();
        model.set_col_bounds(enabled, 0.0, enabled_ub);

        // qnet stores many independent continuous objective aggregates.  Each
        // is defined by one exact row over a binary network controller.
        let first_definition = model.add_row(4.1, 4.1, &[(first_cost, 1.0), (enabled, -2.1)]);
        model.record_inexact_row_coeff(first_definition, enabled.0, rational(-21, 10));
        model.record_inexact_row_bound(first_definition, true, rational(41, 10));
        model.record_inexact_row_bound(first_definition, false, rational(41, 10));
        let second_definition = model.add_row(0.0, 0.0, &[(second_cost, 1.0), (enabled, -3.2)]);
        model.record_inexact_row_coeff(second_definition, enabled.0, rational(-16, 5));
        model.set_objective(&[(first_cost, 1.0), (second_cost, 1.0)], Sense::Minimize);
        model.set_objective_offset(0.3);
        model.record_inexact_obj_offset(rational(3, 10));
        model.add_row(1.0, 1.0, &[(flow, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(flow, 1.0), (enabled, -1.0)]);
        model
    }

    #[test]
    fn route_proves_and_exactly_completes_network_optimum() {
        let model = one_arc_model(1.0);
        let decision = try_solve(&model, None).expect("network PB route");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact network optimum")
        };
        assert_eq!(value, integer(5));
        assert_eq!(model_values, vec![integer(1), integer(5), integer(1)]);
        model
            .check_point(&model_values)
            .expect("completed point rechecks");
    }

    #[test]
    fn lazy_only_resume_keeps_the_distinct_benders_capability() {
        let model = one_arc_model(1.0);
        let decision = try_solve_lazy_only(&model, None, None).expect("lazy-only network result");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact lazy-only optimum")
        };
        assert_eq!(value, integer(5));
        model
            .check_point(&model_values)
            .expect("lazy-only completion rechecks");
    }

    #[test]
    fn objective_singletons_expose_and_lift_qnet_shaped_optimum() {
        let model = multi_objective_arc_model(1.0);
        assert!(matches!(
            project_network_design(&model, None),
            Err(
                crate::network_design_pb::NetworkDesignDecline::ObjectiveSingletonCount {
                    found: 2
                }
            )
        ));

        let (reduced, postsolve) =
            crate::presolve::substitute_objective_singletons(&model).expect("exact reduction");
        assert!(reduced.has_inexact_coeffs());
        assert_eq!(
            reduced.obj_coeff_exact_at(1, reduced.obj_coeff(Col(1))),
            rational(53, 10)
        );
        assert_eq!(reduced.obj_offset_exact(), rational(3, 10));
        assert_eq!(postsolve.const_delta(), &rational(41, 10));
        project_network_design(&reduced, None).expect("reduced network activates");

        let decision = try_solve(&model, None).expect("composed network route");
        let PbRouteDecision::Optimal {
            value,
            model_values,
        } = decision
        else {
            panic!("expected exact composed optimum")
        };
        assert_eq!(value, rational(97, 10));
        assert_eq!(
            model_values,
            vec![integer(1), rational(31, 5), rational(16, 5), integer(1)]
        );
        model
            .check_point(&model_values)
            .expect("source-frame point rechecks");
    }

    #[test]
    fn route_proves_projected_network_infeasibility() {
        let model = one_arc_model(0.0);
        assert!(matches!(
            try_solve(&model, None),
            Some(PbRouteDecision::Infeasible)
        ));
    }

    #[test]
    fn certified_route_rebuilds_and_replays_network_optimum() {
        let model = one_arc_model(1.0);
        let decision = try_solve_certified(&model, None).expect("certified network route");
        let CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision
        else {
            panic!("expected certified network optimum")
        };
        assert_eq!(value, integer(5));
        assert_eq!(model_values, vec![integer(1), integer(5), integer(1)]);
        verify_optimality_certificate(&model, &value, &certificate)
            .expect("strict-better face replays");

        let mut wrong_value = certificate.clone();
        wrong_value.value += integer(1);
        assert!(verify_optimality_certificate(&model, &value, &wrong_value).is_err());
    }

    #[test]
    fn certified_route_searches_repeated_blocks_with_verified_symmetry() {
        let model = two_identical_arc_components_model();
        let projection = project_network_design(&model, None).expect("network projection");
        assert!(has_repeated_network_component_shape(&projection.components));
        assert_eq!(projection.adjacent_block_swap_candidates(None).len(), 1);

        let decision = try_solve_certified(&model, None).expect("certified symmetry route");
        let CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision
        else {
            panic!("expected certified network optimum")
        };
        assert_eq!(value, integer(10));
        model
            .check_point(&model_values)
            .expect("symmetry-routed point rechecks against the source model");
        assert!(matches!(
            &certificate.proof,
            NetworkDesignOptimalityProof::PatternCount(_)
        ));
        verify_optimality_certificate(&model, &value, &certificate)
            .expect("pattern frontier and count master replay against the unaugmented master");

        let mut tampered = certificate.clone();
        let NetworkDesignOptimalityProof::PatternCount(proof) = &mut tampered.proof else {
            unreachable!("variant checked above")
        };
        proof.pb_value = proof.pb_value.checked_add(1).expect("small fixture value");
        assert!(verify_optimality_certificate(&model, &value, &tampered).is_err());
    }

    #[test]
    fn pattern_count_certificate_maps_maximize_objective_exactly() {
        let mut model = two_identical_arc_components_model();
        model.set_objective(&[(Col(2), 1.0)], Sense::Maximize);

        let decision = try_solve_certified(&model, None).expect("certified maximize route");
        let CertifiedNetworkDesignDecision::Optimal {
            value, certificate, ..
        } = decision
        else {
            panic!("expected certified network optimum")
        };
        assert_eq!(value, integer(10));
        assert!(matches!(
            &certificate.proof,
            NetworkDesignOptimalityProof::PatternCount(_)
        ));
        verify_optimality_certificate(&model, &value, &certificate)
            .expect("maximize PB map replays exactly");
    }

    #[test]
    fn pattern_count_certificate_survives_objective_singleton_composition() {
        let model = two_identical_components_with_separate_objectives();
        assert!(needs_objective_singleton_composition(&model));

        let decision = try_solve_certified(&model, None).expect("certified composed route");
        let CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision
        else {
            panic!("expected certified network optimum")
        };
        assert_eq!(value, integer(10));
        assert_eq!(
            model_values,
            vec![
                integer(1),
                integer(1),
                integer(5),
                integer(5),
                integer(1),
                integer(1),
            ]
        );
        assert!(matches!(
            &certificate.proof,
            NetworkDesignOptimalityProof::PatternCount(_)
        ));
        verify_optimality_certificate(&model, &value, &certificate)
            .expect("source-frame singleton delta and pattern PB value replay exactly");
    }

    #[test]
    fn certified_qnet_composition_rebuilds_reduction_and_source_value() {
        let model = multi_objective_arc_model(1.0);
        let decision = try_solve_certified(&model, None).expect("certified composed route");
        let CertifiedNetworkDesignDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision
        else {
            panic!("expected certified composed optimum")
        };
        assert_eq!(value, rational(97, 10));
        assert_eq!(
            model_values,
            vec![integer(1), rational(31, 5), rational(16, 5), integer(1)]
        );
        verify_optimality_certificate(&model, &value, &certificate)
            .expect("composite artifact replays from source");

        let mut wrong_value = certificate.clone();
        wrong_value.value += integer(1);
        assert!(verify_optimality_certificate(&model, &value, &wrong_value).is_err());

        let mut tampered_source = model.clone();
        tampered_source.record_inexact_obj_offset(rational(1, 5));
        assert!(verify_optimality_certificate(&tampered_source, &value, &certificate).is_err());
    }

    #[test]
    fn certified_route_rebuilds_and_replays_network_infeasibility() {
        let model = one_arc_model(0.0);
        let decision = try_solve_certified(&model, None).expect("certified network route");
        let CertifiedNetworkDesignDecision::Infeasible(certificate) = decision else {
            panic!("expected certified network infeasibility")
        };
        verify_infeasibility_certificate(&model, &certificate)
            .expect("empty Hoffman master replays");

        let mut corrupted = certificate.clone();
        match &mut corrupted.proof {
            NetworkDesignPbRefutation::SingleRow(proof) => proof.format.push_str("-tampered"),
            NetworkDesignPbRefutation::MultiRow(proof) => proof.format.push_str("-tampered"),
        }
        assert!(verify_infeasibility_certificate(&model, &corrupted).is_err());
    }

    #[test]
    fn certified_qnet_composition_replays_infeasibility_from_source() {
        let model = multi_objective_arc_model(0.0);
        let decision = try_solve_certified(&model, None).expect("certified composed route");
        let CertifiedNetworkDesignDecision::Infeasible(certificate) = decision else {
            panic!("expected certified composed infeasibility")
        };
        verify_infeasibility_certificate(&model, &certificate)
            .expect("composite refutation replays from source");
    }

    #[test]
    fn full_session_keeps_verified_network_artifacts() {
        let opts = SolveOpts::default().with_require_certificates(true);

        let mut optimal = BabSession::new(one_arc_model(1.0), &opts).expect("optimal session");
        assert!(matches!(
            optimal.check().expect("certified optimum"),
            Outcome::Optimal { .. }
        ));
        assert!(optimal.network_design_optimality_certificate().is_some());
        assert!(
            optimal.block_angular_optimality_certificate().is_none(),
            "the specialized network route must retain ownership ahead of the broader block route"
        );

        let mut infeasible =
            BabSession::new(one_arc_model(0.0), &opts).expect("infeasible session");
        assert!(matches!(
            infeasible.check().expect("certified infeasibility"),
            Outcome::Infeasible { .. }
        ));
        assert!(infeasible
            .network_design_infeasibility_certificate()
            .is_some());
        assert!(infeasible.block_angular_optimality_certificate().is_none());
    }

    #[test]
    fn session_adopts_checked_network_optimum_and_carries_evidence() {
        let model = one_arc_model(1.0);
        let mut session = BabSession::new(model.clone(), &SolveOpts::default()).expect("session");
        let outcome = session.check().expect("network-routed session");
        let Outcome::Optimal {
            value,
            model_values,
            ..
        } = outcome
        else {
            panic!("expected exact network optimum")
        };
        assert_eq!(value, integer(5));
        assert_eq!(model_values, vec![integer(1), integer(5), integer(1)]);
        model
            .check_point(&model_values)
            .expect("the adopted point must satisfy the original model");

        // The certified network route now runs in BOTH postures, so the default
        // posture gets the typed optimality artifact rather than the unbacked
        // `network-design-projection-optimal` claim string this test used to
        // assert. That is the evidence upgrade, not a loss — but a routed
        // optimum must still carry SOMETHING, so pin the disjunction and
        // independently replay the artifact when it is the one present.
        if let Some(certificate) = session.network_design_optimality_certificate() {
            crate::verify_network_design_optimality_certificate(&model, &value, certificate)
                .expect("the published optimality artifact must replay");
        } else {
            assert!(
                session
                    .replay_claims()
                    .iter()
                    .any(|claim| claim.claim == "network-design-projection-optimal"),
                "a routed optimum with neither a typed artifact nor a replay \
                 claim is unattributable: {:?}",
                session.replay_claims()
            );
        }
    }

    #[test]
    fn unrelated_model_declines_and_trial_keeps_fallback_budget() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.add_row(0.0, 1.0, &[(x, 1.0)]);
        assert!(try_solve(&model, None).is_none());

        let now = Instant::now();
        let outer = now + Duration::from_secs(10);
        let trial = trial_deadline(Some(outer), now).expect("trial slice");
        assert_eq!(trial.duration_since(now), Duration::from_secs(2));

        let short = now + Duration::from_secs(1);
        let trial = trial_deadline(Some(short), now).expect("short trial slice");
        assert_eq!(trial.duration_since(now), Duration::from_millis(200));
    }

    #[test]
    fn certificate_generation_reserves_half_the_deadline_for_final_replay() {
        let now = Instant::now();
        let final_deadline = now + Duration::from_secs(10);
        let generation = certificate_generation_deadline(final_deadline, now)
            .expect("a live certificate phase splits its budget");
        assert_eq!(generation.duration_since(now), Duration::from_secs(5));
        assert_eq!(
            final_deadline.duration_since(generation),
            Duration::from_secs(5)
        );
        assert!(generation <= final_deadline);

        let expired = now
            .checked_sub(Duration::from_nanos(1))
            .expect("instant supports a one-nanosecond lookback");
        assert!(certificate_generation_deadline(expired, now).is_none());
        assert!(certificate_generation_deadline(now, now).is_none());
        assert!(certificate_generation_deadline(now + Duration::from_nanos(1), now).is_none());

        let odd_final_deadline = now + Duration::from_nanos(3);
        let odd_generation = certificate_generation_deadline(odd_final_deadline, now)
            .expect("a nonzero half-share remains usable");
        assert!(odd_generation <= odd_final_deadline);
    }

    #[test]
    fn replay_fallback_refreshes_an_admitted_augmentation_only() {
        let now = Instant::now();
        let expired_initial = now
            .checked_sub(Duration::from_millis(1))
            .expect("instant supports a one-millisecond lookback");
        let outer = now + Duration::from_secs(10);
        let admitted = VerifiedBlockSymmetryAttempt::Admitted(None);

        let fallback = replay_fallback_deadline(&admitted, Some(outer), expired_initial, now)
            .expect("live outer clock grants a fresh fallback phase");
        assert_eq!(fallback.duration_since(now), MAX_NETWORK_PB_TRIAL);
        assert!(fallback <= outer);

        let unbounded = replay_fallback_deadline(&admitted, None, expired_initial, now)
            .expect("an unbounded caller still gets the local phase cap");
        assert_eq!(unbounded.duration_since(now), MAX_NETWORK_PB_TRIAL);
    }

    #[test]
    fn structural_symmetry_decline_keeps_its_original_deadline() {
        let now = Instant::now();
        let initial = now + Duration::from_millis(73);
        let outer = now + Duration::from_secs(10);
        let declined = VerifiedBlockSymmetryAttempt::Declined;
        assert_eq!(
            replay_fallback_deadline(&declined, Some(outer), initial, now),
            Some(initial)
        );

        let expired_initial = now
            .checked_sub(Duration::from_millis(1))
            .expect("instant supports a one-millisecond lookback");
        assert_eq!(
            replay_fallback_deadline(&declined, Some(outer), expired_initial, now),
            None
        );
    }

    #[test]
    fn certified_replay_handoff_separates_conclusive_from_incumbent() {
        assert!(matches!(
            replay_handoff(Some(PbRouteDecision::Infeasible)),
            CertifiedNetworkDesignAttempt::ReadyReplay(PbRouteDecision::Infeasible)
        ));
        let incumbent = PbRouteDecision::Feasible {
            model_values: vec![integer(0)],
            incumbent_only: true,
        };
        assert!(matches!(
            replay_handoff(Some(incumbent)),
            CertifiedNetworkDesignAttempt::LazyOnly(Some(PbRouteDecision::Feasible { .. }))
        ));
    }

    #[test]
    fn conclusive_master_result_survives_a_deadline_failed_lift() {
        let model = one_arc_model(1.0);
        let projection = project_network_design(&model, None).expect("network projection");
        let master_values = vec![integer(1)];
        projection
            .master
            .check_point(&master_values)
            .expect("known master point");
        let master_decision = PbRouteDecision::Optimal {
            value: integer(5),
            model_values: master_values,
        };

        assert!(
            lift_network_decision(&model, &projection, &master_decision, Instant::now(),).is_none()
        );
        let lifted = lift_network_decision(
            &model,
            &projection,
            &master_decision,
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the retained master result lifts under the fresh fallback clock");
        assert!(matches!(lifted, PbRouteDecision::Optimal { .. }));
    }

    #[test]
    fn route_combiner_prefers_proofs_then_the_better_exact_incumbent() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.set_objective(&[(x, 1.0)], Sense::Minimize);

        let worse = PbRouteDecision::Feasible {
            model_values: vec![integer(1)],
            incumbent_only: true,
        };
        let better = PbRouteDecision::Feasible {
            model_values: vec![integer(0)],
            incumbent_only: true,
        };
        let selected = prefer_pb_route_decision(&model, Some(worse), Some(better))
            .expect("one feasible point survives");
        let PbRouteDecision::Feasible { model_values, .. } = selected else {
            panic!("expected the better feasible point")
        };
        assert_eq!(model_values, vec![integer(0)]);

        let incumbent = PbRouteDecision::Feasible {
            model_values: vec![integer(0)],
            incumbent_only: true,
        };
        let optimum = PbRouteDecision::Optimal {
            value: integer(0),
            model_values: vec![integer(0)],
        };
        assert!(matches!(
            prefer_pb_route_decision(&model, Some(incumbent), Some(optimum)),
            Some(PbRouteDecision::Optimal { .. })
        ));
    }

    #[test]
    fn route_combiner_is_order_independent_and_fail_closed_for_both_senses() {
        for sense in [Sense::Minimize, Sense::Maximize] {
            let mut model = Model::new();
            let x = model.add_binary_col();
            model.set_objective(&[(x, 1.0)], sense);
            let (better, worse) = match sense {
                Sense::Minimize => (0, 1),
                Sense::Maximize => (1, 0),
            };
            let point = |value: i64| vec![integer(value)];
            let feasible = |value: i64, incumbent_only: bool| PbRouteDecision::Feasible {
                model_values: point(value),
                incumbent_only,
            };
            let optimal = |value: i64| PbRouteDecision::Optimal {
                value: integer(value),
                model_values: point(value),
            };

            let assert_feasible = |decision: Option<PbRouteDecision>, expected: i64| {
                let Some(PbRouteDecision::Feasible {
                    model_values,
                    incumbent_only,
                }) = decision
                else {
                    panic!("expected a fail-closed feasible result")
                };
                assert_eq!(model_values, point(expected));
                assert!(incumbent_only);
            };
            let assert_optimal = |decision: Option<PbRouteDecision>, expected: i64| {
                let Some(PbRouteDecision::Optimal {
                    value,
                    model_values,
                }) = decision
                else {
                    panic!("expected a compatible optimum")
                };
                assert_eq!(value, integer(expected));
                assert_eq!(model_values, point(expected));
            };

            // Feasible/feasible retains the better checked witness.
            for reverse in [false, true] {
                let pair = if reverse {
                    (feasible(worse, true), feasible(better, true))
                } else {
                    (feasible(better, true), feasible(worse, true))
                };
                assert_feasible(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // A compatible optimum may close over a worse incumbent.
            for reverse in [false, true] {
                let pair = if reverse {
                    (feasible(worse, true), optimal(better))
                } else {
                    (optimal(better), feasible(worse, true))
                };
                assert_optimal(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // A claimed optimum worse than a checked incumbent loses terminal
            // authority and becomes the better anytime witness.
            for reverse in [false, true] {
                let pair = if reverse {
                    (optimal(worse), feasible(better, true))
                } else {
                    (feasible(better, true), optimal(worse))
                };
                assert_feasible(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // A checked witness is a direct counterexample to infeasibility.
            for reverse in [false, true] {
                let pair = if reverse {
                    (PbRouteDecision::Infeasible, feasible(better, true))
                } else {
                    (feasible(better, true), PbRouteDecision::Infeasible)
                };
                assert_feasible(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // Optimal versus infeasible is a contradictory terminal pair; the
            // optimal point remains valid only as a feasible incumbent.
            for reverse in [false, true] {
                let pair = if reverse {
                    (PbRouteDecision::Infeasible, optimal(better))
                } else {
                    (optimal(better), PbRouteDecision::Infeasible)
                };
                assert_feasible(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // Distinct optimum claims cannot both be terminal. Keep the better
            // point, but only as a feasible incumbent.
            for reverse in [false, true] {
                let pair = if reverse {
                    (optimal(worse), optimal(better))
                } else {
                    (optimal(better), optimal(worse))
                };
                assert_feasible(
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                    better,
                );
            }

            // Identical independently checked optimum claims are compatible.
            assert_optimal(
                prefer_pb_route_decision(&model, Some(optimal(better)), Some(optimal(better))),
                better,
            );

            // Equal feasible points retain the non-anytime posture regardless
            // of argument order.
            for reverse in [false, true] {
                let pair = if reverse {
                    (feasible(better, false), feasible(better, true))
                } else {
                    (feasible(better, true), feasible(better, false))
                };
                let Some(PbRouteDecision::Feasible { incumbent_only, .. }) =
                    prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1))
                else {
                    panic!("expected equal feasible points to remain feasible")
                };
                assert!(!incumbent_only);
            }
        }
    }

    #[test]
    fn route_combiner_retains_a_typed_refutation_over_bare_exhaustion() {
        let model = Model::new();
        let certified = || PbRouteDecision::CertifiedMultiRowInfeasible {
            certificate: MultiRowBddInfeasibilityCertificate {
                format: "selection-only-test".to_owned(),
                variable_order: Vec::new(),
                proof: ay_pb_core::MultiRowBddInfeasibilityProof::RootContradiction,
            },
        };
        for reverse in [false, true] {
            let pair = if reverse {
                (certified(), PbRouteDecision::Infeasible)
            } else {
                (PbRouteDecision::Infeasible, certified())
            };
            assert!(matches!(
                prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)),
                Some(PbRouteDecision::CertifiedMultiRowInfeasible { .. })
            ));
        }
    }

    #[test]
    fn route_combiner_rechecks_witnesses_before_resolving_conflicts() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        model.set_objective(&[(x, 1.0)], Sense::Minimize);
        let invalid = || PbRouteDecision::Feasible {
            model_values: vec![integer(2)],
            incumbent_only: true,
        };

        for reverse in [false, true] {
            let pair = if reverse {
                (PbRouteDecision::Infeasible, invalid())
            } else {
                (invalid(), PbRouteDecision::Infeasible)
            };
            assert!(prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1)).is_none());
        }

        let valid_optimum = || PbRouteDecision::Optimal {
            value: integer(0),
            model_values: vec![integer(0)],
        };
        let invalid_optimum = || PbRouteDecision::Optimal {
            value: integer(2),
            model_values: vec![integer(2)],
        };
        for reverse in [false, true] {
            let pair = if reverse {
                (invalid_optimum(), valid_optimum())
            } else {
                (valid_optimum(), invalid_optimum())
            };
            let Some(PbRouteDecision::Feasible { model_values, .. }) =
                prefer_pb_route_decision(&model, Some(pair.0), Some(pair.1))
            else {
                panic!("the independently valid witness should survive")
            };
            assert_eq!(model_values, vec![integer(0)]);
        }
    }

    #[test]
    fn multi_objective_non_singleton_model_still_declines() {
        let mut model = Model::new();
        let first = model.add_col(0.0, 1.0);
        let second = model.add_col(0.0, 1.0);
        model.add_row(0.0, 0.0, &[(first, 1.0)]);
        model.add_row(0.0, 0.0, &[(second, 1.0)]);
        model.add_row(0.0, 0.0, &[(first, 1.0), (second, 1.0)]);
        model.set_objective(&[(first, 1.0), (second, 1.0)], Sense::Minimize);

        assert!(try_solve(&model, None).is_none());
        assert!(try_solve_certified(&model, None).is_none());
        assert!(matches!(
            try_solve_certified_attempt(&model, None),
            // Neither objective column is a substitutable singleton, so no
            // network projection/search began and the complete default route
            // remains authorized to make its ordinary cheap decline.
            CertifiedNetworkDesignAttempt::NotApplicable
        ));
    }

    #[test]
    fn block_symmetry_precheck_requires_a_repeated_component_shape() {
        use crate::network_design_pb::ProjectedNetworkComponent;

        let component = |balances: usize, flows: usize| ProjectedNetworkComponent {
            balance_rows: (0..balances).collect(),
            flow_columns: (0..flows).collect(),
            retained_flows: false,
        };
        assert!(!has_repeated_network_component_shape(&[
            component(3, 8),
            component(4, 8),
        ]));
        assert!(has_repeated_network_component_shape(&[
            component(3, 8),
            component(3, 8),
        ]));
    }

    #[test]
    fn expired_deadline_declines() {
        let model = one_arc_model(1.0);
        assert!(try_solve(&model, Some(Instant::now())).is_none());
    }

    // Compile-time guard that the test's expected column order remains the
    // public model insertion order used by exact lifting.
    const _: fn(Col) -> usize = Col::index;
}
