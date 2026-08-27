// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct-CNF and one-shot network replay reductions.

use super::super::*;

pub(super) fn try_direct_cnf(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(decision) = crate::direct_cnf::try_solve(&session.model, session.opts.deadline) else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let outcome = match decision {
        crate::sat_route::SatDecision::Sat(checked) => {
            let has_objective = state.has_objective;
            let solved = state.take_solved(session);
            return RouteOutcome::finish(finish_checked_sat_point(
                checked,
                has_objective,
                &session.model,
                &solved,
                &session.opts,
            ));
        }
        crate::sat_route::SatDecision::Unsat => {
            record_direct_cnf_refutation();
            Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            }
        }
    };
    let claims = lane_frame.take_lane_claims();
    let solved = state.solved_for_deferral(session);
    session
        .admit_or_defer(
            &crate::claim::DIRECT_CNF,
            outcome,
            &solved,
            claims,
            Finisher::ExactReduction,
        )
        .map_or(RouteOutcome::Continue, RouteOutcome::finish)
}

fn record_direct_cnf_refutation() {
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
        tcb: "ay-milp/src/direct_cnf.rs+ay-milp/src/sat_route.rs+ay-sat".to_owned(),
    });
}

pub(super) fn try_network_design(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let lane_frame = crate::claim::LaneFrame::enter();
    let handoff = session.take_pending_network_design_replay();
    let source = match &handoff {
        Some(_) => NetworkReplaySource::CertifiedHandoff,
        None => NetworkReplaySource::FreshRecognition,
    };
    let decision = match handoff {
        Some(NetworkDesignReplayHandoff::ReadyReplay(decision)) => Some(decision),
        Some(NetworkDesignReplayHandoff::LazyOnly(incumbent)) => {
            crate::network_design_route::try_solve_lazy_only(
                &session.model,
                session.opts.deadline,
                incumbent,
            )
        }
        None => crate::network_design_route::try_solve(&session.model, session.opts.deadline),
    };
    let Some(decision) = decision else {
        drop(lane_frame);
        return continue_after_network(session, state, source);
    };
    let Some(outcome) = map_network_replay(session, state, decision) else {
        drop(lane_frame);
        return continue_after_network(session, state, source);
    };
    let claims = lane_frame.take_lane_claims();
    let solved = state.solved_for_deferral(session);
    match session.admit_or_defer(
        &crate::claim::NETWORK_DESIGN_REPLAY,
        outcome,
        &solved,
        claims,
        Finisher::ExactReduction,
    ) {
        Some(outcome) => RouteOutcome::finish(outcome),
        None => continue_after_network(session, state, source),
    }
}

#[derive(Clone, Copy)]
enum NetworkReplaySource {
    /// The certified attempt retained checked work for this exact replay.
    CertifiedHandoff,
    /// No checked handoff existed, so the replay route recognized from scratch.
    FreshRecognition,
}

/// A handoff owns replay priority, but a decline or below-floor conclusion
/// must not permanently suppress the typed block proof it postponed. A fresh
/// replay has already had that block opportunity in the certified phase.
fn continue_after_network(
    session: &mut BabSession,
    state: &CheckState,
    source: NetworkReplaySource,
) -> RouteOutcome {
    match source {
        NetworkReplaySource::CertifiedHandoff => {
            certified::run_block_angular_after_network_handoff(session, state)
        }
        NetworkReplaySource::FreshRecognition => RouteOutcome::Continue,
    }
}

fn map_network_replay(
    session: &mut BabSession,
    state: &CheckState,
    decision: crate::pb_route::PbRouteDecision,
) -> Option<Outcome> {
    use crate::pb_route::PbRouteDecision as Decision;
    match decision {
        Decision::Feasible {
            model_values,
            incumbent_only,
        } if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            if session.incumbent_seed.is_none() {
                session.incumbent_seed = exact_point_to_f64_seed(&model_values);
            }
            None
        }
        Decision::Feasible {
            model_values,
            incumbent_only,
        } => Some(Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: None,
        }),
        Decision::Infeasible
        | Decision::CertifiedSingleRowInfeasible { .. }
        | Decision::CertifiedMultiRowInfeasible { .. } => {
            // These certificates refute the reconstructed network master, not
            // the caller model. They therefore remain replay evidence.
            record_network_replay("network-design-projection-infeasible");
            Some(Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            })
        }
        Decision::Optimal {
            value,
            model_values,
        } => {
            record_network_replay("network-design-projection-optimal");
            Some(Outcome::Optimal {
                value,
                model_values,
                cert: None,
            })
        }
    }
}

fn record_network_replay(claim: &'static str) {
    let method = if claim.ends_with("optimal") {
        "exact-hoffman-projection+bounded-pb-exhaustion+rational-transshipment"
    } else {
        "exact-hoffman-projection+bounded-pb-exhaustion"
    };
    crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
        claim: claim.to_owned(),
        device: "hoffman-network-pb-projection".to_owned(),
        method: method.to_owned(),
        arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
        nodes_visited: None,
        node_budget: 0,
        outcome: "exhausted".to_owned(),
        nondeterminism: Vec::new(),
        reproduce: "ay-milp solve <model> --require none".to_owned(),
        tcb: "ay-milp/src/presolve.rs+ay-milp/src/network_design_pb.rs+\
              ay-milp/src/network_design_route.rs+ay-milp/src/pb_translate.rs+ay-pb-core"
            .to_owned(),
    });
}
