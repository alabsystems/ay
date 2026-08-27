// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Replay-backed structural routes below the typed-proof frontier.
//!
//! Work is posture-independent. Verdicts without model-bound proof objects
//! pass through the evidence floor, so a weaker certificate policy cannot
//! preempt a stronger anchor result.

use super::*;

mod extended;
mod pb;
mod structural;

pub(super) fn run_sat_relu_fallback(
    session: &mut BabSession,
    state: &mut CheckState,
) -> RouteOutcome {
    let Some(plan) = state.pending_sat_relu_fallback.take() else {
        return RouteOutcome::Continue;
    };
    crate::sat_relu::trace_ordinary_fallback();
    let lane_frame = crate::claim::LaneFrame::enter();
    match plan.solve(&session.model, session.opts.deadline) {
        Some(crate::sat_relu::SatReluDecision::Sat(checked)) => {
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
            session
                .admit_or_defer(
                    &crate::claim::SAT_RELU_FALLBACK,
                    outcome,
                    &solved,
                    claims,
                    Finisher::AlreadyFinished,
                )
                .map_or(RouteOutcome::Continue, RouteOutcome::finish)
        }
        Some(crate::sat_relu::SatReluDecision::Unsat) => {
            record_sat_relu_refutation();
            let claims = lane_frame.take_lane_claims();
            let solved = state.solved_for_deferral(session);
            session
                .admit_or_defer(
                    &crate::claim::SAT_RELU_FALLBACK,
                    Outcome::Infeasible {
                        cert: None,
                        tree_cert: None,
                    },
                    &solved,
                    claims,
                    Finisher::ExactReduction,
                )
                .map_or(RouteOutcome::Continue, RouteOutcome::finish)
        }
        None => {
            drop(lane_frame);
            RouteOutcome::Continue
        }
    }
}

fn record_sat_relu_refutation() {
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
}

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    for route in [structural::try_direct_cnf, structural::try_network_design] {
        let result = route(session, state);
        if matches!(result, RouteOutcome::Finished(_)) {
            return result;
        }
    }
    let pb = pb::run(session, state);
    if matches!(pb, RouteOutcome::Finished(_)) {
        return pb;
    }
    extended::run(session, state)
}

/// Exercise the production one-shot handoff continuation without rerunning
/// unrelated route families.
#[cfg(test)]
pub(super) fn run_network_design_handoff_for_test(
    session: &mut BabSession,
    state: &mut CheckState,
) -> RouteOutcome {
    structural::try_network_design(session, state)
}
