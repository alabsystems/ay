// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Margin dispatch and the final native, SMT, or exact anchor.

use super::*;

mod anchor;
mod exact;
mod margin;

#[derive(Clone, Copy)]
enum LaneKind {
    Native,
    #[cfg(feature = "smt")]
    Smt,
    Exact,
}

pub(super) fn run(
    session: &mut BabSession,
    mut state: CheckState,
    request: CheckRequest<'_, '_, '_>,
) -> Result<Outcome, MilpError> {
    let CheckRequest {
        shared_binary_prefix,
        proof_first_workers,
        margin_mode,
        target_fsb_prefix,
    } = request;
    let margin = margin::prepare(
        session,
        &mut state,
        margin_mode,
        shared_binary_prefix,
        target_fsb_prefix,
    )?;
    let margin_proof_target = match margin {
        margin::Dispatch::Finished(outcome) => {
            session.replay_claims = crate::cert_io::ledger::take();
            return Ok(outcome);
        }
        margin::Dispatch::Anchor(target) => target,
    };

    let lane = match &session.lane {
        MilpLane::Native => LaneKind::Native,
        #[cfg(feature = "smt")]
        MilpLane::Smt(_) => LaneKind::Smt,
        MilpLane::Exact => LaneKind::Exact,
    };
    let outcome = match lane {
        LaneKind::Native => anchor::solve(
            session,
            &state,
            anchor::Request {
                shared_binary_prefix,
                proof_first_workers,
                target_fsb_prefix,
                margin_proof_target: margin_proof_target.as_ref(),
            },
        )?,
        #[cfg(feature = "smt")]
        LaneKind::Smt => anchor::solve_smt(session, &state)?,
        LaneKind::Exact => exact::solve(session, &state),
    };
    let out = finish_anchor(session, &mut state, outcome, margin_proof_target.as_ref());
    session.replay_claims = crate::cert_io::ledger::take();
    Ok(out)
}

fn finish_anchor(
    session: &mut BabSession,
    state: &mut CheckState,
    outcome: Outcome,
    margin_proof_target: Option<&crate::margin::MarginProofTarget<'_>>,
) -> Outcome {
    let original_margin_tree_verified = match (margin_proof_target, &outcome) {
        (
            Some(target),
            Outcome::Infeasible {
                tree_cert: Some(tree),
                ..
            },
        ) => tree.verify(target.proof_model()).is_ok(),
        _ => false,
    };
    let parity_infeasibility_verified = outcome.is_infeasible()
        && session
            .parity_infeasibility_certificate
            .as_ref()
            .is_some_and(|certificate| {
                crate::verify_parity_infeasibility_certificate(&session.model, certificate).is_ok()
            });
    if outcome.is_infeasible() && !parity_infeasibility_verified {
        session.parity_infeasibility_certificate = None;
    }
    let solved = state.take_solved(session);
    affine::finish_native_outcome(
        outcome,
        &session.model,
        &solved,
        &session.opts,
        original_margin_tree_verified,
        parity_infeasibility_verified,
        session.affine_aggregation_verification,
    )
}
