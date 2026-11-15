// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Live-source lowering around one consumed retained-work credit. Outside-frame
//! clauses retain an ordered prerequisite/final pair; combined disjoint/outside
//! clauses retain two prerequisites followed by the final clause.
//! Caller-owned whole-proof/source admission remains mandatory. The reported
//! counter covers the retained primitive's phases, not source lowering or SAT
//! search. This is not an outer bundle reader or an allocator/RSS guarantee.

use super::*;
use crate::bv_blast_solver::retained::{
    metered as expression,
    wire::{WireError, WireLimits},
    work::{Metered, MeteredError, WorkAllowance, WorkError},
};

mod disjoint;
mod outside;
mod pricing;
pub(crate) use pricing::price_clause;

#[derive(Debug, thiserror::Error)]
pub(crate) enum MeteredBridgeError {
    #[error(transparent)]
    Bridge(#[from] BridgeError),
    #[error(transparent)]
    Retained(MeteredError),
}

impl From<MeteredError> for MeteredBridgeError {
    fn from(error: MeteredError) -> Self {
        match error {
            MeteredError::Proof(BvExprExportError::Cancelled)
            | MeteredError::Wire(WireError::Cancelled) => BridgeError::Cancelled.into(),
            MeteredError::Work(WorkError::Deadline) | MeteredError::Wire(WireError::Deadline) => {
                BridgeError::Deadline.into()
            }
            other => Self::Retained(other),
        }
    }
}

impl control::ControlError for MeteredBridgeError {
    fn bridge_error(&self) -> Option<&BridgeError> {
        match self {
            Self::Bridge(error) => Some(error),
            Self::Retained(_) => None,
        }
    }
}

/// Capture and encode THIS live clause, consuming one prepaid credit.
/// No acceptance/refusal memo or compatibility producer is consulted.
pub(crate) fn capture_clause(
    terms: &TermStore,
    clause: &[TermId],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Metered<Vec<u8>>, MeteredBridgeError> {
    run(
        proof,
        gates,
        wire,
        allowance,
        poll,
        |control, proof, gates, wire, allowance| {
            if proof.resolution.max_conflicts.is_none() || proof.resolution.max_decisions.is_none()
            {
                return Err(BridgeError::MissingSearchBounds.into());
            }
            match source_route(terms, clause, control)? {
                SourceRoute::Outside(shape) => {
                    return outside::capture(
                        terms, clause, shape, proof, gates, wire, allowance, control,
                    )
                }
                SourceRoute::Disjoint(shape) => {
                    return disjoint::capture(
                        terms, clause, shape, proof, gates, wire, allowance, control,
                    )
                }
                SourceRoute::Ordinary => {}
            }
            with_lowered_clause(terms, clause, control, |source, truth, control| {
                expression::capture(source, truth, proof, gates, wire, allowance, &mut || {
                    control.poll().is_ok()
                })
                .map_err(MeteredBridgeError::from)
            })
        },
    )
}

/// Decode and independently replay THIS live clause. Empty, corrupt,
/// missing or source-mismatched wire never selects SAT search or a memo.
pub(crate) fn replay_clause(
    terms: &TermStore,
    clause: &[TermId],
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Metered<()>, MeteredBridgeError> {
    run(
        proof,
        gates,
        wire,
        allowance,
        poll,
        |control, proof, gates, wire, allowance| {
            match source_route(terms, clause, control)? {
                SourceRoute::Outside(shape) => {
                    return outside::replay(
                        terms, clause, shape, bytes, proof, gates, wire, allowance, control,
                    )
                }
                SourceRoute::Disjoint(shape) => {
                    return disjoint::replay(
                        terms, clause, shape, bytes, proof, gates, wire, allowance, control,
                    )
                }
                SourceRoute::Ordinary => {}
            }
            with_lowered_clause(terms, clause, control, |source, truth, control| {
                expression::replay(
                    source,
                    truth,
                    bytes,
                    proof,
                    gates,
                    wire,
                    allowance,
                    &mut || control.poll().is_ok(),
                )
                .map_err(MeteredBridgeError::from)
            })
        },
    )
}

fn run<T>(
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
    operation: impl FnOnce(
        &mut Control<'_>,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
        &WireLimits,
        WorkAllowance,
    ) -> Result<T, MeteredBridgeError>,
) -> Result<T, MeteredBridgeError> {
    // Intersect BEFORE even the first callback or source walk. In particular,
    // a shorter wire/credit deadline must also constrain ordinary lowering.
    let end = [
        proof.resolution.deadline,
        proof.resolution.validation.deadline,
        gates.deadline,
    ]
    .into_iter()
    .flatten()
    .fold(allowance.deadline().min(wire.deadline), Instant::min);
    Control::new(end, poll).run_typed(|control| {
        let (proof, gates) = effective_limits(proof, gates, control)?;
        let mut wire = *wire;
        wire.deadline = control.deadline();
        operation(control, &proof, &gates, &wire, allowance)
    })
}
