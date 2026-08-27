// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Open-domain and opt-in hybrid exact reductions.

use super::super::*;

enum MappedDecision {
    Continue,
    Checked(Outcome),
    Certified {
        outcome: Outcome,
        proof: SupplementalProof,
    },
    Replay {
        outcome: Outcome,
        floor: &'static crate::claim::LaneFloor,
    },
}

enum HybridDecision {
    Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision),
    IntegerLift(crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision),
}

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let open_domain = try_open_domain(session, state);
    if matches!(open_domain, RouteOutcome::Finished(_)) {
        return open_domain;
    }
    try_hybrid(session, state)
}

fn try_open_domain(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(decision) = crate::open_domain_route::try_solve(&session.model, session.opts.deadline)
    else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let mapped = map_open_domain(session, state, decision);
    finish_mapped(session, state, lane_frame, mapped)
}

fn map_open_domain(
    session: &mut BabSession,
    state: &CheckState,
    decision: crate::open_domain_route::OpenDomainRouteDecision,
) -> MappedDecision {
    use crate::open_domain_route::OpenDomainRouteDecision as Decision;
    match decision {
        Decision::Feasible {
            model_values,
            incumbent_only,
        } if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            seed_if_absent(session, &model_values);
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
            session.open_domain_single_row_dp_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedOpenDomainSingleRowDpInfeasibility)
        }
        Decision::CertifiedMultiRowInfeasible { certificate } => {
            session.open_domain_multi_row_bdd_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedOpenDomainMultiRowBddInfeasibility)
        }
        Decision::CertifiedHybridPbLpInfeasible { certificate } => {
            session.open_domain_hybrid_pb_lp_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedOpenDomainHybridPbLpInfeasibility)
        }
        Decision::CertifiedHybridIntegerLiftInfeasible { certificate } => {
            session.open_domain_hybrid_integer_lift_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedOpenDomainHybridIntegerLiftInfeasibility)
        }
        Decision::Infeasible => {
            record_open_domain_replay(OpenDomainReplayClaim::Infeasible);
            MappedDecision::Replay {
                outcome: infeasible_outcome(),
                floor: &crate::claim::OPEN_DOMAIN_REPLAY,
            }
        }
        Decision::Optimal {
            value,
            model_values,
        } => {
            record_open_domain_replay(OpenDomainReplayClaim::Optimal);
            MappedDecision::Replay {
                outcome: Outcome::Optimal {
                    value,
                    model_values,
                    cert: None,
                },
                floor: &crate::claim::OPEN_DOMAIN_REPLAY,
            }
        }
    }
}

fn try_hybrid(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let enabled = crate::tune::caller_flag(crate::tune::Knob::HybridPbLp) == Some(true);
    let lane_frame = crate::claim::LaneFrame::enter();
    let decision = hybrid_pb_lp_trial_deadline(enabled, session.opts.deadline, Instant::now())
        .and_then(|deadline| {
            crate::hybrid_pb_lp::try_solve_certified(&session.model, Some(deadline))
                .map(HybridDecision::Direct)
                .or_else(|| {
                    crate::hybrid_integer_lift::try_solve_certified(&session.model, Some(deadline))
                        .map(HybridDecision::IntegerLift)
                })
        });
    let Some(decision) = decision else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let mapped = map_hybrid(session, state, decision);
    finish_mapped(session, state, lane_frame, mapped)
}

fn map_hybrid(
    session: &mut BabSession,
    state: &CheckState,
    decision: HybridDecision,
) -> MappedDecision {
    match decision {
        HybridDecision::Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible {
            model_values,
            incumbent_only,
        })
        | HybridDecision::IntegerLift(
            crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
                model_values,
                incumbent_only,
            },
        ) if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            seed_if_absent(session, &model_values);
            MappedDecision::Continue
        }
        HybridDecision::Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible {
            model_values,
            incumbent_only,
        })
        | HybridDecision::IntegerLift(
            crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
                model_values,
                incumbent_only,
            },
        ) => MappedDecision::Checked(Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound: None,
        }),
        HybridDecision::Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Infeasible(
            certificate,
        )) => {
            session.hybrid_pb_lp_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedHybridPbLpInfeasibility)
        }
        HybridDecision::IntegerLift(
            crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Infeasible(certificate),
        ) => {
            session.hybrid_integer_lift_infeasibility_certificate = Some(certificate);
            certified(SupplementalProof::VerifiedHybridIntegerLiftInfeasibility)
        }
        HybridDecision::Direct(crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Optimal {
            value,
            model_values,
        })
        | HybridDecision::IntegerLift(
            crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Optimal {
                value,
                model_values,
            },
        ) => {
            record_hybrid_optimum();
            MappedDecision::Replay {
                outcome: Outcome::Optimal {
                    value,
                    model_values,
                    cert: None,
                },
                floor: &crate::claim::HYBRID_REPLAY,
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
            session
                .admit_or_defer(floor, outcome, &solved, claims, Finisher::ExactReduction)
                .map_or(RouteOutcome::Continue, RouteOutcome::finish)
        }
    }
}

fn certified(proof: SupplementalProof) -> MappedDecision {
    MappedDecision::Certified {
        outcome: infeasible_outcome(),
        proof,
    }
}

fn infeasible_outcome() -> Outcome {
    Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    }
}

fn seed_if_absent(session: &mut BabSession, model_values: &[BigRational]) {
    if session.incumbent_seed.is_none() {
        session.incumbent_seed = exact_point_to_f64_seed(model_values);
    }
}

fn restore_claims(claims: Vec<crate::cert_io::ReplayClaim>) {
    for claim in claims {
        crate::cert_io::ledger::record(claim);
    }
}

#[derive(Clone, Copy)]
enum OpenDomainReplayClaim {
    Infeasible,
    Optimal,
}

fn record_open_domain_replay(claim: OpenDomainReplayClaim) {
    let (claim, device, method) = match claim {
        OpenDomainReplayClaim::Infeasible => (
            "open-domain-projection-infeasible",
            "monotone-open-domain-projection",
            "exact-monotone-projection+bounded-exact-exhaustion",
        ),
        OpenDomainReplayClaim::Optimal => (
            "open-domain-cap-optimal",
            "bounded-open-domain-objective-cap",
            "exact-monotone-projection+inclusive-objective-cap+bounded-exact-optimization",
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
        tcb: "ay-milp/src/open_domain.rs+ay-milp/src/open_domain_route.rs+\
              ay-milp/src/pb_translate.rs+ay-milp/src/hybrid_pb_lp.rs+ay-pb-core"
            .to_owned(),
    });
}

fn record_hybrid_optimum() {
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
        tcb: "ay-milp/src/hybrid_integer_lift.rs+ay-milp/src/hybrid_pb_lp.rs+\
              ay-milp/src/cert.rs+ay-milp/src/exact.rs+ay-pb-core"
            .to_owned(),
    });
}
