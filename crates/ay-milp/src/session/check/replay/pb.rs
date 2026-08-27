// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded exact PB reductions and their evidence boundary.

use super::super::*;

#[derive(Clone, Copy)]
enum PbRoute {
    Specialized,
    Portfolio,
}

enum ReplayFloor {
    Specialized,
    Portfolio,
}

enum MappedDecision {
    Continue,
    Checked(Outcome),
    Certified {
        outcome: Outcome,
        proof: SupplementalProof,
    },
    Replay {
        outcome: Outcome,
        floor: ReplayFloor,
    },
}

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let specialized = try_specialized(session, state);
    if matches!(specialized, RouteOutcome::Finished(_)) {
        return specialized;
    }
    try_portfolio(session, state)
}

fn try_specialized(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(decision) =
        crate::pb_route::try_solve_specialized(&session.model, session.opts.deadline)
    else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let mapped = map_decision(session, state, decision, PbRoute::Specialized);
    finish_mapped(session, state, lane_frame, mapped)
}

fn try_portfolio(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let workers = (!session.opts.determinism)
        .then(|| NonZeroUsize::new(session.opts.threads as usize))
        .flatten()
        .filter(|workers| workers.get() > 1);
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(decision) = crate::pb_route::try_solve_production_portfolio(
        &session.model,
        session.opts.deadline,
        workers,
    ) else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let mapped = map_decision(session, state, decision, PbRoute::Portfolio);
    finish_mapped(session, state, lane_frame, mapped)
}

fn map_decision(
    session: &mut BabSession,
    state: &CheckState,
    decision: crate::pb_route::PbRouteDecision,
    route: PbRoute,
) -> MappedDecision {
    use crate::pb_route::PbRouteDecision as Decision;
    match decision {
        Decision::Feasible {
            model_values,
            incumbent_only,
        } if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            if session.incumbent_seed.is_none() {
                session.incumbent_seed = exact_point_to_f64_seed(&model_values);
            }
            MappedDecision::Continue
        }
        Decision::Feasible {
            model_values,
            incumbent_only,
        } => MappedDecision::Checked(Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: None,
        }),
        Decision::CertifiedSingleRowInfeasible { certificate } => {
            session.single_row_dp_infeasibility_certificate = Some(certificate);
            MappedDecision::Certified {
                outcome: infeasible_outcome(),
                proof: SupplementalProof::VerifiedSingleRowDpInfeasibility,
            }
        }
        Decision::CertifiedMultiRowInfeasible { certificate } => {
            session.multi_row_bdd_infeasibility_certificate = Some(certificate);
            MappedDecision::Certified {
                outcome: infeasible_outcome(),
                proof: SupplementalProof::VerifiedMultiRowBddInfeasibility,
            }
        }
        Decision::Infeasible => {
            record_pb_replay(route, PbReplayClaim::Infeasible);
            MappedDecision::Replay {
                outcome: infeasible_outcome(),
                floor: match route {
                    PbRoute::Specialized => ReplayFloor::Specialized,
                    PbRoute::Portfolio => ReplayFloor::Portfolio,
                },
            }
        }
        Decision::Optimal {
            value,
            model_values,
        } => {
            record_pb_replay(route, PbReplayClaim::Optimal);
            MappedDecision::Replay {
                outcome: Outcome::Optimal {
                    value,
                    model_values,
                    cert: None,
                },
                floor: match route {
                    PbRoute::Specialized => ReplayFloor::Specialized,
                    PbRoute::Portfolio => ReplayFloor::Portfolio,
                },
            }
        }
    }
}

fn finish_mapped(
    session: &mut BabSession,
    state: &mut CheckState,
    lane_frame: crate::claim::LaneFrame,
    mapped: MappedDecision,
) -> RouteOutcome {
    match mapped {
        MappedDecision::Continue => {
            drop(lane_frame);
            RouteOutcome::Continue
        }
        MappedDecision::Checked(outcome) => {
            restore_claims(lane_frame.take_lane_claims());
            let solved = state.take_solved(session);
            RouteOutcome::finish(finish_exact_reduction(
                outcome,
                &session.model,
                &solved,
                &session.opts,
            ))
        }
        MappedDecision::Certified { outcome, proof } => {
            restore_claims(lane_frame.take_lane_claims());
            let solved = state.take_solved(session);
            RouteOutcome::finish(finish_exact_reduction_with_supplemental_proof(
                outcome,
                &session.model,
                &solved,
                &session.opts,
                proof,
            ))
        }
        MappedDecision::Replay { outcome, floor } => {
            let claims = lane_frame.take_lane_claims();
            let solved = state.solved_for_deferral(session);
            let floor = match floor {
                ReplayFloor::Specialized => &crate::claim::SPECIALIZED_PB_REPLAY,
                ReplayFloor::Portfolio => &crate::claim::PB_PORTFOLIO,
            };
            session
                .admit_or_defer(floor, outcome, &solved, claims, Finisher::ExactReduction)
                .map_or(RouteOutcome::Continue, RouteOutcome::finish)
        }
    }
}

fn restore_claims(claims: Vec<crate::cert_io::ReplayClaim>) {
    for claim in claims {
        crate::cert_io::ledger::record(claim);
    }
}

fn infeasible_outcome() -> Outcome {
    Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    }
}

#[derive(Clone, Copy)]
enum PbReplayClaim {
    Infeasible,
    Optimal,
}

fn record_pb_replay(route: PbRoute, claim: PbReplayClaim) {
    let (claim, device, method) = match (route, claim) {
        (PbRoute::Specialized, PbReplayClaim::Infeasible) => (
            "pb-projection-infeasible",
            "milp-to-pb-reduction",
            "exact-rational-boolean-projection+redundant-single-row-dp",
        ),
        (PbRoute::Specialized, PbReplayClaim::Optimal) => (
            "pb-projection-optimal",
            "milp-to-pb-reduction",
            "exact-rational-boolean-projection+redundant-single-row-dp",
        ),
        (PbRoute::Portfolio, PbReplayClaim::Infeasible) => (
            "pb-portfolio-projection-infeasible",
            "bounded-milp-to-pb-portfolio",
            "exact-rational-bounded-integer-projection+pb-exhaustion",
        ),
        (PbRoute::Portfolio, PbReplayClaim::Optimal) => (
            "pb-portfolio-projection-optimal",
            "bounded-milp-to-pb-portfolio",
            "exact-rational-bounded-integer-projection+pb-exhaustion",
        ),
    };
    crate::cert_io::ledger::record(crate::cert_io::ReplayClaim {
        claim: claim.to_owned(),
        device: device.to_owned(),
        method: method.to_owned(),
        arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
        nodes_visited: None,
        node_budget: 0,
        outcome: "exhausted".to_owned(),
        nondeterminism: Vec::new(),
        reproduce: "ay-milp solve <model> --require none".to_owned(),
        tcb: "ay-milp/src/pb_translate.rs+ay-milp/src/pb_route.rs+ay-pb-core".to_owned(),
    });
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;

    fn state_for(model: Model) -> (BabSession, CheckState) {
        let session = BabSession::new(model, &SolveOpts::new()).expect("valid PB floor fixture");
        let state = CheckState::begin(
            &session,
            &CheckRequest {
                shared_binary_prefix: &[],
                proof_first_workers: None,
                margin_mode: MarginMode::Auto,
                target_fsb_prefix: None,
            },
        );
        (session, state)
    }

    fn assert_specialized_replay_is_deferred(
        model: Model,
        decision: crate::pb_route::PbRouteDecision,
        failing_claim: &'static str,
        replay_claim: &str,
    ) {
        let _ = crate::cert_io::ledger::take();
        let (mut session, mut state) = state_for(model);
        let lane_frame = crate::claim::LaneFrame::enter();
        let mapped = map_decision(&mut session, &state, decision, PbRoute::Specialized);
        assert!(matches!(
            finish_mapped(&mut session, &mut state, lane_frame, mapped),
            RouteOutcome::Continue
        ));
        assert_eq!(
            session.deferred_lane(),
            Some(("specialized-pb", failing_claim))
        );
        let deferred = session
            .deferred_claim
            .as_ref()
            .expect("below-floor specialized decision must be retained");
        assert!(deferred
            .replay_claims
            .iter()
            .any(|claim| claim.claim == replay_claim));
    }

    /// The decision seam isolates route identity from PB certificate-export
    /// resource limits. Production `try_specialized` feeds the same mapping
    /// and floor join after its exact solver returns either bare decision.
    #[test]
    fn specialized_bare_decisions_cross_the_specialized_floor() {
        let mut infeasible = Model::new();
        let x = infeasible.add_binary_col();
        infeasible.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        infeasible.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        assert_specialized_replay_is_deferred(
            infeasible,
            crate::pb_route::PbRouteDecision::Infeasible,
            "infeasible",
            "pb-projection-infeasible",
        );

        let mut optimal = Model::new();
        let x = optimal.add_binary_col();
        optimal.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert_specialized_replay_is_deferred(
            optimal,
            crate::pb_route::PbRouteDecision::Optimal {
                value: BigRational::from_integer(BigInt::from(0)),
                model_values: vec![BigRational::from_integer(BigInt::from(0))],
            },
            "no-better-than",
            "pb-projection-optimal",
        );
    }
}
