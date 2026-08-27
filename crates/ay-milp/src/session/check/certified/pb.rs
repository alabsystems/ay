// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed PB and hybrid infeasibility proofs.
//!
//! A single-row structural pass supplies the model-derived cost unit for the
//! heavier BDD and hybrid probes. All lanes remain bounded by the same absolute
//! proof deadline, and the lifted hybrid is attempted only when the direct
//! hybrid declines structurally.

use std::time::Duration;

use super::super::*;

struct ProbeBudget {
    deadline: Option<Instant>,
    single_row_cost: Duration,
}

enum SingleRowProbe {
    Finished(Outcome),
    Declined(ProbeBudget),
}

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let budget = match try_single_row(session, state) {
        SingleRowProbe::Finished(outcome) => return RouteOutcome::finish(outcome),
        SingleRowProbe::Declined(budget) => budget,
    };
    for route in [try_multi_row, try_open_domain, try_hybrid] {
        let result = route(session, state, &budget);
        if matches!(result, RouteOutcome::Finished(_)) {
            return result;
        }
    }
    RouteOutcome::Continue
}

fn try_single_row(session: &mut BabSession, state: &mut CheckState) -> SingleRowProbe {
    let deadline = pb_portfolio_trial_deadline(session.opts.deadline, Instant::now());
    let started = Instant::now();
    let cpu_started = probe_clock();
    let decision = deadline.and_then(|trial_deadline| {
        crate::pb_route::try_prove_single_row_infeasibility(&session.model, trial_deadline)
    });
    if structure_trace_enabled() {
        eprintln!(
            "--trace infeasibility-probe single_row={:.6}s hit={}",
            started.elapsed().as_secs_f64(),
            decision.is_some(),
        );
    }
    if let Some(crate::pb_route::PbRouteDecision::CertifiedSingleRowInfeasible { certificate }) =
        decision
    {
        session.single_row_dp_infeasibility_certificate = Some(certificate);
        return SingleRowProbe::Finished(finish_infeasible(
            session,
            state,
            SupplementalProof::VerifiedSingleRowDpInfeasibility,
        ));
    }
    // The single-row probe just declined this model; its cost is the
    // model-derived unit that bounds the heavier BDD and hybrid arms. See
    // `probe_scaled_deadline`. Read on the probe clock (thread CPU time): a
    // preemption stall — or, measured on khb05250, the cold page-faulting of
    // a first pass, 1.1 ms wall for 0.36 ms CPU — during the cheap pass is
    // not a property of the model and must not inflate the slices derived
    // from it.
    SingleRowProbe::Declined(ProbeBudget {
        deadline,
        single_row_cost: probe_clock().saturating_sub(cpu_started),
    })
}

fn try_multi_row(
    session: &mut BabSession,
    state: &mut CheckState,
    budget: &ProbeBudget,
) -> RouteOutcome {
    let started = Instant::now();
    let decision = probe_arm(
        "multi_row",
        budget.single_row_cost,
        budget.deadline,
        |deadline| crate::pb_route::try_prove_multi_row_infeasibility(&session.model, deadline),
    );
    if structure_trace_enabled() {
        eprintln!(
            "--trace infeasibility-probe multi_row={:.6}s hit={}",
            started.elapsed().as_secs_f64(),
            decision.is_some(),
        );
    }
    let Some(crate::pb_route::PbRouteDecision::CertifiedMultiRowInfeasible { certificate }) =
        decision
    else {
        return RouteOutcome::Continue;
    };
    session.multi_row_bdd_infeasibility_certificate = Some(certificate);
    RouteOutcome::finish(finish_infeasible(
        session,
        state,
        SupplementalProof::VerifiedMultiRowBddInfeasibility,
    ))
}

fn try_open_domain(
    session: &mut BabSession,
    state: &mut CheckState,
    budget: &ProbeBudget,
) -> RouteOutcome {
    let started = Instant::now();
    let decision = budget.deadline.and_then(|deadline| {
        crate::open_domain_route::try_prove_infeasibility(&session.model, deadline)
    });
    if structure_trace_enabled() {
        eprintln!(
            "--trace infeasibility-probe open_domain={:.6}s hit={}",
            started.elapsed().as_secs_f64(),
            decision.is_some(),
        );
    }
    let proof = match decision {
        Some(crate::open_domain_route::OpenDomainRouteDecision::CertifiedSingleRowInfeasible {
            certificate,
        }) => {
            session.open_domain_single_row_dp_infeasibility_certificate = Some(certificate);
            SupplementalProof::VerifiedOpenDomainSingleRowDpInfeasibility
        }
        Some(crate::open_domain_route::OpenDomainRouteDecision::CertifiedMultiRowInfeasible {
            certificate,
        }) => {
            session.open_domain_multi_row_bdd_infeasibility_certificate = Some(certificate);
            SupplementalProof::VerifiedOpenDomainMultiRowBddInfeasibility
        }
        Some(crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridPbLpInfeasible {
            certificate,
        }) => {
            session.open_domain_hybrid_pb_lp_infeasibility_certificate = Some(certificate);
            SupplementalProof::VerifiedOpenDomainHybridPbLpInfeasibility
        }
        Some(
            crate::open_domain_route::OpenDomainRouteDecision::CertifiedHybridIntegerLiftInfeasible {
                certificate,
            },
        ) => {
            session.open_domain_hybrid_integer_lift_infeasibility_certificate = Some(certificate);
            SupplementalProof::VerifiedOpenDomainHybridIntegerLiftInfeasibility
        }
        _ => return RouteOutcome::Continue,
    };
    RouteOutcome::finish(finish_infeasible(session, state, proof))
}

fn try_hybrid(
    session: &mut BabSession,
    state: &mut CheckState,
    budget: &ProbeBudget,
) -> RouteOutcome {
    // Same unit as the BDD arm above: the cheap single-row structural pass
    // already declined this model. See `probe_arm`.
    let started = Instant::now();
    let direct = probe_arm(
        "hybrid_pb_lp",
        budget.single_row_cost,
        budget.deadline,
        |deadline| crate::hybrid_pb_lp::try_solve_certified(&session.model, Some(deadline)),
    );
    if structure_trace_enabled() {
        eprintln!(
            "--trace infeasibility-probe hybrid_pb_lp={:.6}s hit={}",
            started.elapsed().as_secs_f64(),
            direct.is_some(),
        );
    }
    match direct {
        Some(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(certificate)) => {
            session.hybrid_pb_lp_infeasibility_certificate = Some(certificate);
            RouteOutcome::finish(finish_infeasible(
                session,
                state,
                SupplementalProof::VerifiedHybridPbLpInfeasibility,
            ))
        }
        Some(_) => RouteOutcome::Continue,
        None => try_lifted_hybrid(session, state, budget),
    }
}

fn try_lifted_hybrid(
    session: &mut BabSession,
    state: &mut CheckState,
    budget: &ProbeBudget,
) -> RouteOutcome {
    let started = Instant::now();
    let decision = probe_arm(
        "hybrid_integer_lift",
        budget.single_row_cost,
        budget.deadline,
        |deadline| crate::hybrid_integer_lift::try_solve_certified(&session.model, Some(deadline)),
    );
    if structure_trace_enabled() {
        eprintln!(
            "--trace infeasibility-probe hybrid_integer_lift={:.6}s hit={}",
            started.elapsed().as_secs_f64(),
            decision.is_some(),
        );
    }
    let Some(crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(
        certificate,
    )) = decision
    else {
        return RouteOutcome::Continue;
    };
    session.hybrid_integer_lift_infeasibility_certificate = Some(certificate);
    RouteOutcome::finish(finish_infeasible(
        session,
        state,
        SupplementalProof::VerifiedHybridIntegerLiftInfeasibility,
    ))
}

fn finish_infeasible(
    session: &BabSession,
    state: &mut CheckState,
    proof: SupplementalProof,
) -> Outcome {
    let solved = state.take_solved(session);
    finish_exact_reduction_with_supplemental_proof(
        Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        },
        &session.model,
        &solved,
        &session.opts,
        proof,
    )
}
