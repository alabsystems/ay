// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-derived disjoint and combined prerequisite chains. Every theorem is
//! independently checked before native lowering can install its local facts.
//! Ordered wire roles describe the chain; they never supply source expressions.

use super::*;
use crate::bv_blast_solver::retained::wire::pair::FrameSet;
use crate::checker::bv_bitblast::{
    disjoint::Shape, producer_limits::proof_replay_limits,
    proof_producing_control::disjoint as native_disjoint,
};
use std::cell::RefCell;

#[expect(
    clippy::too_many_arguments,
    reason = "source, shape, three independent limit owners, allowance, and control stay explicit"
)]
pub(super) fn capture(
    terms: &TermStore,
    clause: &[TermId],
    shape: Shape,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    control: &mut Control<'_>,
) -> Result<Metered<Vec<u8>>, MeteredBridgeError> {
    let plan = source_plan(terms, clause, &shape, control)?;
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
            let mut prerequisites: [Option<Vec<u8>>; 2] = [None, None];
            let source = lower(
                terms,
                shape,
                plan,
                &mut limits,
                end,
                &shared,
                &mut |index, lhs, rhs, proof, gates| {
                    let slot = prerequisites
                        .get_mut(index)
                        .ok_or(WireError::InvalidPayload("too many disjoint prerequisites"))?;
                    *slot = Some(chain.capture_one(lhs, rhs, proof, gates)?);
                    Ok(())
                },
            )?;
            let first = prerequisites[0]
                .as_deref()
                .ok_or(WireError::InvalidPayload("missing disjoint prerequisite"))?;
            let truth = BvExpr::const_val(1, 1);
            let replay = proof_replay_limits(&limits);
            let final_clause = chain.capture_one(&source, &truth, &limits, &replay)?;
            drop(source);
            drop(truth);
            match plan {
                FrameSet::Disjoint => chain.pack_frames(plan, &[first, &final_clause]),
                FrameSet::Combined => {
                    let second = prerequisites[1]
                        .as_deref()
                        .ok_or(WireError::InvalidPayload(
                            "missing combined outside prerequisite",
                        ))?;
                    chain.pack_frames(plan, &[first, second, &final_clause])
                }
                FrameSet::Outside => {
                    Err(WireError::InvalidPayload("invalid disjoint source plan").into())
                }
            }
        },
    )
    .map_err(MeteredBridgeError::from)
}

#[expect(
    clippy::too_many_arguments,
    reason = "source, wire, three independent limit owners, allowance, and control stay explicit"
)]
pub(super) fn replay(
    terms: &TermStore,
    clause: &[TermId],
    shape: Shape,
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    control: &mut Control<'_>,
) -> Result<Metered<()>, MeteredBridgeError> {
    let plan = source_plan(terms, clause, &shape, control)?;
    let end = control.deadline();
    let shared = RefCell::new(control);
    expression::chain(
        proof,
        gates,
        wire,
        allowance,
        &mut || shared.borrow_mut().poll().is_ok(),
        |chain| {
            // The live source fixes cardinality and order before either
            // prerequisite is read. A missing frame never invokes search.
            let frames = chain.split_frames(plan, bytes)?;
            let mut limits = proof.clone();
            let source = lower(
                terms,
                shape,
                plan,
                &mut limits,
                end,
                &shared,
                &mut |index, lhs, rhs, proof, gates| {
                    let frame = frames
                        .get(index)
                        .ok_or(WireError::InvalidPayload("missing disjoint prerequisite"))?;
                    chain.replay_one(lhs, rhs, frame, proof, gates)
                },
            )?;
            let truth = BvExpr::const_val(1, 1);
            let replay = proof_replay_limits(&limits);
            let final_index = prerequisite_count(plan)?;
            chain.replay_one(&source, &truth, frames[final_index], &limits, &replay)
        },
    )
    .map_err(MeteredBridgeError::from)
}

fn source_plan(
    terms: &TermStore,
    clause: &[TermId],
    shape: &Shape,
    control: &mut Control<'_>,
) -> Result<FrameSet, MeteredBridgeError> {
    control.poll()?;
    let combined = outside_frame::Shape::recognize_root(terms, shape.root).is_some();
    control.poll()?;
    if combined {
        // Preserve the native combined route's bounded sparse operand checks.
        // Ordinary full read-mux expansion would discard that supported lane.
        Ok(FrameSet::Combined)
    } else {
        outside::validate_operands(terms, clause, control)?;
        Ok(FrameSet::Disjoint)
    }
}

fn prerequisite_count(plan: FrameSet) -> Result<usize, MeteredError> {
    match plan {
        FrameSet::Disjoint => Ok(1),
        FrameSet::Combined => Ok(2),
        FrameSet::Outside => Err(WireError::InvalidPayload("invalid disjoint source plan").into()),
    }
}

#[expect(
    clippy::type_complexity,
    reason = "the callback signature is the exact indexed prerequisite proof schema"
)]
fn lower(
    terms: &TermStore,
    shape: Shape,
    plan: FrameSet,
    limits: &mut BvExprProofLimits,
    end: Instant,
    shared: &RefCell<&mut Control<'_>>,
    prove: &mut dyn FnMut(
        usize,
        &BvExpr,
        &BvExpr,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
    ) -> Result<(), MeteredError>,
) -> Result<BvExpr, MeteredError> {
    let expected = prerequisite_count(plan)?;
    let mut calls = 0;
    let mut failure = None;
    let source = native_disjoint::lower_with_prover(
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
        &mut |lhs, rhs, proof, gates, poll| {
            // Never hold the shared control borrow while entering Chain: its
            // own callback polls the same sticky owner.
            if !poll() {
                return Err(BvExprExportError::Cancelled);
            }
            let result = if calls < expected {
                let index = calls;
                calls += 1;
                prove(index, lhs, rhs, proof, gates)
            } else {
                Err(WireError::InvalidPayload("repeated disjoint prerequisite").into())
            };
            if let Err(error) = result {
                failure = Some(error);
                return Err(BvExprExportError::Cancelled);
            }
            if !poll() {
                return Err(BvExprExportError::Cancelled);
            }
            Ok(())
        },
    );
    // The cancellation-shaped legacy shim is not the error's identity.
    // Preserve work/wire/replay errors without parsing their display strings.
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
    if calls != expected {
        return Err(WireError::InvalidPayload("missing disjoint prerequisite").into());
    }
    Ok(source)
}
