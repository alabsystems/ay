// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-bearing structural routes that precede the general portfolio.
//!
//! These lanes run only for an ordinary native check and keep their historical
//! source order. A checked point or model-bound proof may finish the solve;
//! advice-only results seed the later anchor without acquiring verdict authority.

use super::*;

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    for route in [try_sat_relu_proof, try_parity, try_scheduling] {
        let result = route(session, state);
        if matches!(result, RouteOutcome::Finished(_)) {
            return result;
        }
    }
    RouteOutcome::Continue
}

/// Run the one bounded proof-enabled SAT/ReLU pass.
///
/// A decline retains the recognized plan only when the caller supplied no
/// memory envelope; the unmetered legacy fallback then runs later, after every
/// typed proof route has had first refusal.
fn try_sat_relu_proof(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let Some(plan) = crate::sat_relu::prepare_with_memory_budget(
        &session.model,
        session.opts.deadline,
        session.opts.memory_budget,
    ) else {
        return RouteOutcome::Continue;
    };
    let fallback_allowed = session.opts.memory_budget.is_none();
    let proof_deadline = sat_relu_proof_trial_deadline(session.opts.deadline, Instant::now());
    let lane_frame = crate::claim::LaneFrame::enter();
    let decision = proof_deadline.and_then(|deadline| {
        plan.try_solve_with_proof(&session.model, Some(deadline), session.opts.memory_budget)
    });

    let outcome = match decision {
        Some(crate::sat_relu::SatReluProofDecision::Sat(checked)) => {
            #[cfg(test)]
            crate::sat_relu::test_wait_before_session_finish();
            let solved = state.solved_for_deferral(session);
            let outcome = finish_checked_sat_point(
                checked,
                state.has_objective,
                &session.model,
                &solved,
                &session.opts,
            );
            let claims = lane_frame.take_lane_claims();
            session.admit_or_defer(
                &crate::claim::SAT_RELU_PROOF,
                outcome,
                &solved,
                claims,
                Finisher::AlreadyFinished,
            )
        }
        Some(crate::sat_relu::SatReluProofDecision::Unsat(certificate)) => {
            session.sat_relu_infeasibility_certificate = Some(certificate);
            let solved = state.solved_for_deferral(session);
            let outcome = finish_exact_reduction_with_supplemental_proof(
                Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                },
                &session.model,
                &solved,
                &session.opts,
                SupplementalProof::VerifiedSatReluInfeasibility,
            );
            let claims = lane_frame.take_lane_claims();
            session.admit_or_defer(
                &crate::claim::SAT_RELU_PROOF,
                outcome,
                &solved,
                claims,
                Finisher::AlreadyFinished,
            )
        }
        None => {
            drop(lane_frame);
            if fallback_allowed {
                state.pending_sat_relu_fallback = Some(plan);
            }
            return RouteOutcome::Continue;
        }
    };
    outcome.map_or(RouteOutcome::Continue, RouteOutcome::finish)
}

/// Admit only a source-verified parity refutation as typed authority.
///
/// Parity optima do not yet carry an optimality artifact. Under full policy
/// they remain incumbent advice and the proof-producing anchor continues.
fn try_parity(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(outcome) = crate::parity::try_solve(&session.model, session.opts.deadline) else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let certificate = crate::parity::take_pending_infeasibility_certificate();
    match outcome {
        infeasible @ Outcome::Infeasible { .. } => {
            let Some(certificate) = certificate.filter(|certificate| {
                crate::verify_parity_infeasibility_certificate(&session.model, certificate).is_ok()
            }) else {
                drop(lane_frame);
                return RouteOutcome::Continue;
            };
            drop(lane_frame);
            session.parity_infeasibility_certificate = Some(certificate);
            let solved = state.take_solved(session);
            RouteOutcome::finish(finish_exact_reduction_with_supplemental_proof(
                infeasible,
                &session.model,
                &solved,
                &session.opts,
                SupplementalProof::VerifiedParityInfeasibility,
            ))
        }
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            seed_if_absent(session, &model_values);
            if !state.has_objective {
                drop(lane_frame);
                let solved = state.take_solved(session);
                return RouteOutcome::finish(finish_exact_reduction(
                    Outcome::Feasible {
                        model_values,
                        incumbent_only: false,
                        dual_bound: None,
                    },
                    &session.model,
                    &solved,
                    &session.opts,
                ));
            }
            let solved = state.solved_for_deferral(session);
            let cert = cert.or_else(|| zero_cost_optimality_certificate(&solved));
            let outcome = Outcome::Optimal {
                value,
                model_values,
                cert,
            };
            if matches!(outcome, Outcome::Optimal { cert: Some(_), .. }) {
                drop(lane_frame);
                return RouteOutcome::finish(finish_exact_reduction(
                    outcome,
                    &session.model,
                    &solved,
                    &session.opts,
                ));
            }
            record_parity_optimum();
            let claims = lane_frame.take_lane_claims();
            session
                .admit_or_defer(
                    &crate::claim::PARITY_OPTIMUM_REPLAY,
                    outcome,
                    &solved,
                    claims,
                    Finisher::ExactReduction,
                )
                .map_or(RouteOutcome::Continue, RouteOutcome::finish)
        }
        Outcome::Feasible {
            model_values,
            incumbent_only,
            ..
        } if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            drop(lane_frame);
            seed_if_absent(session, &model_values);
            RouteOutcome::Continue
        }
        outcome => {
            drop(lane_frame);
            let solved = state.take_solved(session);
            RouteOutcome::finish(finish_exact_reduction(
                outcome,
                &session.model,
                &solved,
                &session.opts,
            ))
        }
    }
}

fn record_parity_optimum() {
    crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
        claim: "parity-enumeration-optimal".to_owned(),
        device: "gf2-parity-enumeration".to_owned(),
        method: "exact-source-row-parity+complete-assignment-enumeration".to_owned(),
        arithmetic: "exact-gf2+rational".to_owned(),
        nodes_visited: None,
        node_budget: 0,
        outcome: "exhausted".to_owned(),
        nondeterminism: Vec::new(),
        reproduce: "ay-milp solve <model> --require none".to_owned(),
        tcb: "ay-milp/src/parity.rs".to_owned(),
    });
}

fn seed_if_absent(session: &mut BabSession, values: &[BigRational]) {
    if session.incumbent_seed.is_none() {
        session.incumbent_seed = exact_point_to_f64_seed(values);
    }
}

/// Run the complete exact scheduling DP and retain its model-bound certificate.
fn try_scheduling(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let Some(decision) =
        crate::scheduling_route::try_solve_certified(&session.model, session.opts.deadline)
    else {
        return RouteOutcome::Continue;
    };
    let crate::scheduling_route::SingleMachineSchedulingDecision::Optimal {
        value,
        model_values,
        certificate,
    } = decision;
    session.single_machine_scheduling_optimality_certificate = Some(certificate);
    let solved = state.take_solved(session);
    RouteOutcome::finish(finish_exact_reduction_with_supplemental_proof(
        Outcome::Optimal {
            value,
            model_values,
            cert: None,
        },
        &session.model,
        &solved,
        &session.opts,
        SupplementalProof::VerifiedSingleMachineSchedulingOptimality,
    ))
}
