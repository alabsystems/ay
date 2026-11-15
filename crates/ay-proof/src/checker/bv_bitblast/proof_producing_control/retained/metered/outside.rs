// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-authenticated outside-frame pair. The exact free-offset theorem is
//! proved/replayed before local facts enter the lowerer; its returned final
//! clause is independently checked second. Role tags are transport only.

use super::*;
use std::cell::RefCell;

pub(super) fn capture(
    terms: &TermStore,
    clause: &[TermId],
    shape: outside_frame::Shape,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    control: &mut Control<'_>,
) -> Result<Metered<Vec<u8>>, MeteredBridgeError> {
    validate_operands(terms, clause, control)?;
    let end = control.deadline();
    let shared = RefCell::new(control);
    expression::chain(
        proof,
        gates,
        wire,
        allowance,
        &mut || shared.borrow_mut().poll().is_ok(),
        |chain| {
            let mut limits = proof.clone();
            let mut prerequisite = None;
            let source = lower(
                terms,
                shape,
                &mut limits,
                end,
                &shared,
                &mut |lhs, rhs, proof, gates| {
                    prerequisite = Some(chain.capture_one(lhs, rhs, proof, gates)?);
                    Ok(())
                },
            )?;
            let prerequisite =
                prerequisite.ok_or(WireError::InvalidPayload("missing outside prerequisite"))?;
            let truth = BvExpr::const_val(1, 1);
            let replay = super::super::super::super::producer_limits::proof_replay_limits(&limits);
            let final_clause = chain.capture_one(&source, &truth, &limits, &replay)?;
            drop(source);
            drop(truth);
            chain.pack_pair([&prerequisite, &final_clause])
        },
    )
    .map_err(MeteredBridgeError::from)
}

pub(super) fn replay(
    terms: &TermStore,
    clause: &[TermId],
    shape: outside_frame::Shape,
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    control: &mut Control<'_>,
) -> Result<Metered<()>, MeteredBridgeError> {
    validate_operands(terms, clause, control)?;
    let end = control.deadline();
    let shared = RefCell::new(control);
    expression::chain(
        proof,
        gates,
        wire,
        allowance,
        &mut || shared.borrow_mut().poll().is_ok(),
        |chain| {
            let [prerequisite, final_clause] = chain.split_pair(bytes)?;
            let mut limits = proof.clone();
            let source = lower(
                terms,
                shape,
                &mut limits,
                end,
                &shared,
                &mut |lhs, rhs, proof, gates| {
                    chain.replay_one(lhs, rhs, prerequisite, proof, gates)
                },
            )?;
            let truth = BvExpr::const_val(1, 1);
            let replay = super::super::super::super::producer_limits::proof_replay_limits(&limits);
            chain.replay_one(&source, &truth, final_clause, &limits, &replay)
        },
    )
    .map_err(MeteredBridgeError::from)
}

pub(super) fn validate_operands(
    terms: &TermStore,
    clause: &[TermId],
    control: &mut Control<'_>,
) -> Result<(), MeteredBridgeError> {
    // Match native outside-only lowering: validate the entire ordinary source
    // before proving a conditional fact, including overwritten operands.
    let ordinary = lower_clause_as(
        terms,
        clause,
        control.deadline(),
        Route::default(),
        &mut || control.poll().is_ok(),
    )
    .map_err(|failure| match failure {
        Failure::Cancelled => BridgeError::Cancelled,
        Failure::Stopped(_) => BridgeError::Deadline,
        Failure::Rejected(message) => BridgeError::Source(message),
    })?;
    drop(ordinary);
    control.poll()?;
    Ok(())
}

fn lower(
    terms: &TermStore,
    shape: outside_frame::Shape,
    limits: &mut BvExprProofLimits,
    end: Instant,
    shared: &RefCell<&mut Control<'_>>,
    prove: &mut dyn FnMut(
        &BvExpr,
        &BvExpr,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
    ) -> Result<(), MeteredError>,
) -> Result<BvExpr, MeteredError> {
    let mut calls = 0;
    let mut failure = None;
    let source = outside_frame::lower_with_disjoint_and_prover(
        terms,
        shape,
        limits,
        end,
        &mut || {
            shared
                .borrow_mut()
                .poll()
                .map_err(|_| crate::ProofCheckError::ResourceLimit)
        },
        None,
        &mut |lhs, rhs, proof, gates, poll| {
            // Release the lowering callback's borrow before entering Chain,
            // whose independent polls borrow the same sticky source control.
            if !poll() {
                return Err(BvExprExportError::Cancelled);
            }
            let result = if calls == 0 {
                calls += 1;
                prove(lhs, rhs, proof, gates)
            } else {
                Err(WireError::InvalidPayload("repeated outside prerequisite").into())
            };
            if let Err(error) = result {
                // A fixed shim unwinds the legacy callback; the original typed
                // error is returned below. It is never parsed or downgraded.
                failure = Some(error);
                return Err(BvExprExportError::Cancelled);
            }
            if !poll() {
                return Err(BvExprExportError::Cancelled);
            }
            Ok(())
        },
    );
    if let Some(error) = failure {
        return Err(error);
    }
    let source = source.map_err(|error| match error {
        Failure::Cancelled => MeteredError::Proof(BvExprExportError::Cancelled),
        Failure::Stopped(_) => WorkError::Deadline.into(),
        Failure::Rejected(message) => {
            MeteredError::Proof(BvExprExportError::RefutationNotSurfaceable(message))
        }
    })?;
    if calls != 1 {
        return Err(WireError::InvalidPayload("missing outside prerequisite").into());
    }
    Ok(source)
}
