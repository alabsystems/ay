// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified network-design and block-angular routes.

use super::super::*;

pub(super) fn run(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let network = try_network_design(session, state);
    if matches!(network, RouteOutcome::Finished(_)) {
        return network;
    }
    try_block_angular(session, state)
}

/// Attempt the model-bound network proof without repeating eager work later.
fn try_network_design(session: &mut BabSession, state: &mut CheckState) -> RouteOutcome {
    let started = Instant::now();
    let attempt = crate::network_design_route::try_solve_certified_attempt(
        &session.model,
        session.opts.deadline,
    );
    if structure_trace_enabled() {
        eprintln!(
            "--trace network-design-attempt t={:.6}s applicable={}",
            started.elapsed().as_secs_f64(),
            !matches!(
                attempt,
                crate::network_design_route::CertifiedNetworkDesignAttempt::NotApplicable
            ),
        );
    }
    let decision = match attempt {
        crate::network_design_route::CertifiedNetworkDesignAttempt::NotApplicable => None,
        crate::network_design_route::CertifiedNetworkDesignAttempt::Decided(decision) => {
            Some(decision)
        }
        crate::network_design_route::CertifiedNetworkDesignAttempt::ReadyReplay(decision) => {
            session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::ReadyReplay(
                decision,
            ));
            None
        }
        crate::network_design_route::CertifiedNetworkDesignAttempt::LazyOnly(incumbent) => {
            session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::LazyOnly(
                incumbent,
            ));
            None
        }
    };
    decision.map_or(RouteOutcome::Continue, |decision| {
        map_network_decision(session, state, decision)
    })
}

fn map_network_decision(
    session: &mut BabSession,
    state: &mut CheckState,
    decision: crate::network_design_route::CertifiedNetworkDesignDecision,
) -> RouteOutcome {
    use crate::network_design_route::CertifiedNetworkDesignDecision as Decision;
    match decision {
        Decision::Feasible {
            model_values,
            incumbent_only,
        } if exact_reduction_feasible_must_continue_native(state.has_objective, incumbent_only) => {
            if session.incumbent_seed.is_none() {
                session.incumbent_seed = exact_point_to_f64_seed(&model_values);
            }
            session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::LazyOnly(
                Some(crate::pb_route::PbRouteDecision::Feasible {
                    model_values,
                    incumbent_only,
                }),
            ));
            RouteOutcome::Continue
        }
        Decision::Feasible {
            model_values,
            incumbent_only,
        } => finish_terminal(
            session,
            state,
            Outcome::Feasible {
                model_values,
                incumbent_only,
                dual_bound: None,
            },
            SupplementalProof::None,
        ),
        Decision::Infeasible(certificate) => {
            session.network_design_infeasibility_certificate = Some(certificate);
            finish_terminal(
                session,
                state,
                Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                },
                SupplementalProof::VerifiedNetworkDesignInfeasibility,
            )
        }
        Decision::Optimal {
            value,
            model_values,
            certificate,
        } => {
            session.network_design_optimality_certificate = Some(certificate);
            finish_terminal(
                session,
                state,
                Outcome::Optimal {
                    value,
                    model_values,
                    cert: None,
                },
                SupplementalProof::VerifiedNetworkDesignOptimality,
            )
        }
    }
}

fn finish_terminal(
    session: &BabSession,
    state: &mut CheckState,
    outcome: Outcome,
    proof: SupplementalProof,
) -> RouteOutcome {
    let solved = state.take_solved(session);
    let outcome = if matches!(proof, SupplementalProof::None) {
        finish_exact_reduction(outcome, &session.model, &solved, &session.opts)
    } else {
        finish_exact_reduction_with_supplemental_proof(
            outcome,
            &session.model,
            &solved,
            &session.opts,
            proof,
        )
    };
    RouteOutcome::finish(outcome)
}

/// A block-angular optimum still passes through the common evidence floor.
/// Its verified side artifact currently ties or exceeds every anchor claim;
/// keeping the gate here makes that authority explicit and regression-tested.
pub(super) fn try_block_angular(session: &mut BabSession, state: &CheckState) -> RouteOutcome {
    if !session.may_offer_block_angular_before_network_replay()
        || !crate::block_angular_route::is_coarse_block_angular_candidate(&session.model)
    {
        return RouteOutcome::Continue;
    }
    let lane_frame = crate::claim::LaneFrame::enter();
    let Some(decision) = crate::block_angular_route::try_solve_certified(
        &session.model,
        session.opts.deadline,
        session.opts.memory_budget,
    ) else {
        drop(lane_frame);
        return RouteOutcome::Continue;
    };
    let crate::block_angular_route::BlockAngularDecision {
        value,
        model_values,
        certificate,
    } = decision;
    session.block_angular_optimality_certificate = Some(certificate);
    let solved = state.solved_for_deferral(session);
    let outcome = finish_exact_reduction_with_supplemental_proof(
        Outcome::Optimal {
            value,
            model_values,
            cert: None,
        },
        &session.model,
        &solved,
        &session.opts,
        SupplementalProof::VerifiedBlockAngularOptimality,
    );
    let claims = lane_frame.take_lane_claims();
    session
        .admit_or_defer(
            &crate::claim::BLOCK_ANGULAR,
            outcome,
            &solved,
            claims,
            Finisher::AlreadyFinished,
        )
        .map_or(RouteOutcome::Continue, RouteOutcome::finish)
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use num_rational::BigRational;

    use super::*;

    fn network_handoff_block_model() -> Model {
        let mut model = Model::new();
        let root_one = model.add_binary_col();
        let state_one = model.add_binary_col();
        let exit_one = model.add_binary_col();
        let root_two = model.add_binary_col();
        let state_two = model.add_binary_col();
        let exit_two = model.add_binary_col();

        model.add_row(0.0, 0.0, &[(root_one, 1.0), (state_one, -1.0)]);
        model.add_row(0.0, 0.0, &[(state_one, 1.0), (exit_one, -1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(root_one, 1.0)]);
        model.add_row(0.0, 0.0, &[(root_two, 1.0), (state_two, -1.0)]);
        model.add_row(0.0, 0.0, &[(state_two, 1.0), (exit_two, -1.0)]);
        model.add_row(f64::NEG_INFINITY, 1.0, &[(root_two, 1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(state_one, 1.0), (state_two, 1.0)]);
        model.set_objective(&[(exit_one, 1.0), (exit_two, 2.0)], Sense::Minimize);
        model
    }

    #[test]
    fn consumed_network_handoff_cannot_suppress_typed_block_proof() {
        let opts = SolveOpts::new()
            .with_deadline(Instant::now() + Duration::from_secs(20))
            .with_require_certificates(true);
        let mut session = BabSession::new(network_handoff_block_model(), &opts)
            .expect("valid block-angular session");
        let request = CheckRequest {
            shared_binary_prefix: &[],
            proof_first_workers: None,
            margin_mode: MarginMode::Auto,
            target_fsb_prefix: None,
        };
        let mut state = CheckState::begin(&session, &request);
        let one = BigRational::from_integer(1.into());
        let zero = BigRational::from_integer(0.into());
        session.install_network_design_replay_handoff(NetworkDesignReplayHandoff::ReadyReplay(
            crate::pb_route::PbRouteDecision::Optimal {
                value: one.clone(),
                model_values: vec![
                    one.clone(),
                    one.clone(),
                    one.clone(),
                    zero.clone(),
                    zero.clone(),
                    zero,
                ],
            },
        ));

        let value = match replay::run_network_design_handoff_for_test(&mut session, &mut state)
            .finished()
        {
            Some(Outcome::Optimal { value, .. }) => value,
            Some(other) => {
                panic!("typed block proof did not close after replay: {other:?}")
            }
            None => panic!("typed block proof declined after replay handoff"),
        };
        assert_eq!(value, BigRational::from_integer(1.into()));
        assert_eq!(
            session.deferred_lane(),
            Some(("network-design-replay", "no-better-than")),
            "the one-shot network handoff must run before the block proof"
        );
        let deferred = session
            .deferred_claim
            .as_ref()
            .expect("network replay remains held behind the typed proof");
        assert!(deferred
            .replay_claims
            .iter()
            .any(|claim| claim.claim == "network-design-projection-optimal"));
        assert!(session.pending_network_design_replay.is_none());

        let certificate = session
            .block_angular_optimality_certificate()
            .expect("typed block proof retained");
        crate::block_angular_route::verify_optimality_certificate(
            session.model(),
            &value,
            certificate,
        )
        .expect("typed block proof verifies against the source model");
    }
}
