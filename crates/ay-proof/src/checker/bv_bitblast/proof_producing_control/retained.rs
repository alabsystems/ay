// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private ordinary-source bridge, not a proof-bundle admission boundary.
//!
//! The caller must authenticate the live clause's source kind, Boolean/BV and
//! gate structure, and pay the whole-proof expensive-BV reservation BEFORE
//! using this bridge. The supplied numeric grants must already be prepaid;
//! this module neither allocates new allowances nor refunds opaque replay
//! costs. Payloads remain untrusted and confer no proof-step/source authority.
//!
//! The single-refutation API supports only ordinary lowering; only tests use
//! it. The metered API, which the retained session uses, additionally retains
//! the source-derived outside/disjoint prerequisites and final clause. Matching uses bounded recognizers with control polls
//! around them; their internal walks, individual allocation and destruction
//! remain opaque intervals, not hard cancellation-latency or RSS guarantees.

use super::{lower_clause_as, outside_frame, BvExpr, Failure, Instant, Route, TermId, TermStore};
use crate::bv_blast_export::BvBlastValidateLimits;
#[cfg(test)]
use crate::bv_blast_solver::retained::{
    capture_bv_expr_refutation, replay_bv_expr_refutation, RetainedBvRefutation,
};
use crate::bv_blast_solver::{BvExprExportError, BvExprProofLimits};

mod control;
use control::Control;
pub(crate) mod metered;

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpecializedRoute {
    Disjoint,
    OutsideFrame,
}

enum SourceRoute {
    Ordinary,
    Outside(outside_frame::Shape),
    Disjoint(super::super::disjoint::Shape),
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum BridgeError {
    #[error("retained clause operation cancelled")]
    Cancelled,
    #[error("retained clause deadline expired")]
    Deadline,
    #[error("retained clause operation requires an absolute proof deadline")]
    MissingDeadline,
    #[error("retained capture requires finite conflict and decision grants")]
    MissingSearchBounds,
    #[error("retained clause must be nonempty and within the ordinary clause bound")]
    ClauseBound,
    #[cfg(test)]
    #[error("retained clause does not support conditional {0:?} lowering")]
    Specialized(SpecializedRoute),
    #[error("retained clause source lowering refused: {0}")]
    Source(String),
    #[cfg(test)]
    #[error("retained clause refutation refused: {0}")]
    Refutation(BvExprExportError),
}

/// Capture an untrusted refutation of THIS ordinary live clause.
#[cfg(test)]
pub(crate) fn capture_clause(
    terms: &TermStore,
    clause: &[TermId],
    deadline: Instant,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<RetainedBvRefutation, BridgeError> {
    Control::new(deadline, keep_going).run(|control| {
        let (proof, gates) = effective_limits(proof, gates, control)?;
        if proof.resolution.max_conflicts.is_none() || proof.resolution.max_decisions.is_none() {
            return Err(BridgeError::MissingSearchBounds);
        }
        with_ordinary_clause(terms, clause, control, |source, truth, control| {
            capture_bv_expr_refutation(source, truth, &proof, &gates, &mut || {
                control.poll().is_ok()
            })
            .map_err(refutation_error)
        })
    })
}

/// Replay only: reconstruct from THIS live source, without SAT search or any
/// semantic acceptance/refusal memo. Missing/corrupt payloads never fall back.
#[cfg(test)]
pub(crate) fn replay_clause(
    terms: &TermStore,
    clause: &[TermId],
    payload: Option<&RetainedBvRefutation>,
    deadline: Instant,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), BridgeError> {
    Control::new(deadline, keep_going).run(|control| {
        let (proof, gates) = effective_limits(proof, gates, control)?;
        with_ordinary_clause(terms, clause, control, |source, truth, control| {
            replay_bv_expr_refutation(source, truth, payload, &proof, &gates, &mut || {
                control.poll().is_ok()
            })
            .map_err(refutation_error)
        })
    })
}

fn effective_limits(
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    control: &mut Control<'_>,
) -> Result<(BvExprProofLimits, BvBlastValidateLimits), BridgeError> {
    let mut deadline = proof
        .resolution
        .deadline
        .ok_or(BridgeError::MissingDeadline)?;
    for other in [proof.resolution.validation.deadline, gates.deadline]
        .into_iter()
        .flatten()
    {
        deadline = deadline.min(other);
    }
    control.tighten(deadline)?;
    let mut proof = proof.clone();
    let mut gates = *gates;
    proof.resolution.deadline = Some(control.deadline());
    proof.resolution.validation.deadline = Some(control.deadline());
    gates.deadline = Some(control.deadline());
    Ok((proof, gates))
}

#[cfg(test)]
fn with_ordinary_clause<T, E: From<BridgeError>>(
    terms: &TermStore,
    clause: &[TermId],
    control: &mut Control<'_>,
    operation: impl FnOnce(&BvExpr, &BvExpr, &mut Control<'_>) -> Result<T, E>,
) -> Result<T, E> {
    match source_route(terms, clause, control)? {
        SourceRoute::Ordinary => {}
        SourceRoute::Outside(_) => {
            return Err(BridgeError::Specialized(SpecializedRoute::OutsideFrame).into());
        }
        SourceRoute::Disjoint(_) => {
            return Err(BridgeError::Specialized(SpecializedRoute::Disjoint).into());
        }
    }
    with_lowered_clause(terms, clause, control, operation)
}

fn source_route(
    terms: &TermStore,
    clause: &[TermId],
    control: &mut Control<'_>,
) -> Result<SourceRoute, BridgeError> {
    control.poll()?;
    if clause.is_empty() || clause.len() > super::MAX_PROOF_PRODUCING_CLAUSE_LITERALS {
        return Err(BridgeError::ClauseBound);
    }
    // Existing recognition is bounded: disjoint's branch walk admits at most
    // 32 pending/visited terms and conjunction arity 128; outside-frame admits
    // at most 1024 distinct Boolean terms, arity 128 and address depth/work 64.
    // These recognizers grant no facts; poll after their temporary owners drop.
    let disjoint = super::super::disjoint::Shape::recognize(terms, clause);
    control.poll()?;
    if let Some(shape) = disjoint {
        return Ok(SourceRoute::Disjoint(shape));
    }
    let outside = outside_frame::Shape::recognize(terms, clause);
    control.poll()?;
    Ok(outside.map_or(SourceRoute::Ordinary, SourceRoute::Outside))
}

fn with_lowered_clause<T, E: From<BridgeError>>(
    terms: &TermStore,
    clause: &[TermId],
    control: &mut Control<'_>,
    operation: impl FnOnce(&BvExpr, &BvExpr, &mut Control<'_>) -> Result<T, E>,
) -> Result<T, E> {
    let source = lower_clause_as(
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
    let truth = BvExpr::const_val(1, 1);
    let result = control
        .poll()
        .map_err(E::from)
        .and_then(|()| operation(&source, &truth, control));
    drop(source);
    drop(truth);
    // The outer Control::run observes the final boundary only after these
    // expression owners and every lower-level proof temporary have dropped.
    result
}

#[cfg(test)]
fn refutation_error(error: BvExprExportError) -> BridgeError {
    match error {
        BvExprExportError::Cancelled => BridgeError::Cancelled,
        other => BridgeError::Refutation(other),
    }
}

#[cfg(test)]
mod tests;
