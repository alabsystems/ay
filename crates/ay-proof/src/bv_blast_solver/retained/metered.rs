// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture/encode and decode/replay share one consumed work allowance. Source
//! construction and SAT search retain their distinct limits. This adds no
//! proof-bundle authority or whole-operation allocator/RSS guarantee.

use super::*;
use crate::bv_blast_export::BvBlastValidateError;
use work::{Ledger, Metered, MeteredError, Phase, WorkAllowance};

mod chain;
pub(crate) use chain::run as chain;

pub(crate) fn capture(
    lhs: &BvExpr,
    rhs: &BvExpr,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &wire::WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Metered<Vec<u8>>, MeteredError> {
    chain(proof, gates, wire, allowance, poll, |chain| {
        chain.capture_one(lhs, rhs, proof, gates)
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "source terms, three independent limit owners, allowance, and poll stay explicit"
)]
pub(crate) fn replay(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &wire::WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Metered<()>, MeteredError> {
    chain(proof, gates, wire, allowance, poll, |chain| {
        chain.replay_one(lhs, rhs, bytes, proof, gates)
    })
}

fn capture_payload(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    ledger: &mut Ledger,
    poll: &mut dyn FnMut() -> bool,
) -> Result<(RetainedBvRefutation, Shape), MeteredError> {
    if limits.resolution.max_conflicts.is_none() || limits.resolution.max_decisions.is_none() {
        return Err(malformed("metered capture requires finite search limits").into());
    }
    let proof = ledger.phase(
        Phase::Producer,
        limits.resolution.validation.max_work,
        |grant| {
            let mut limits = limits.clone();
            limits.resolution.validation.max_work = grant;
            let preflight = preflight_bv_equality(lhs, rhs, &limits, poll)?;
            let (proof, measured) =
                build_bv_expr_refutation_reporting(lhs, rhs, Some((&limits, preflight)), poll)?;
            let used = measured.ok_or_else(|| malformed("missing producer validation work"))?;
            Ok((proof, u128::from(used)))
        },
    )?;
    let (payload, reduced, shape) = ledger.phase(
        Phase::Prefix,
        limits.resolution.validation.max_work,
        |grant| {
            let mut prefix_limits = limits.clone();
            prefix_limits.resolution.validation.max_work = grant;
            let mut control = Control::new(&prefix_limits);
            let graph_bytes = control.graph(&proof.graph, poll)?;
            let shape = control.dag(&proof.dag, poll)?;
            let payload = codec::encode(&proof.dag, shape, &mut control, poll)?;
            let payload_bytes = control.payload_bytes(&payload, poll)?;
            let reduced = control.replay_limits(&proof.graph, graph_bytes, payload_bytes, poll)?;
            Ok(((payload, reduced, shape), u128::from(control.work)))
        },
    )?;
    validate(&proof, &reduced, gates, ledger, poll)?;
    drop(proof);
    finish_expr_export(Some(limits), poll)?;
    Ok((payload, shape))
}

fn replay_payload(
    lhs: &BvExpr,
    rhs: &BvExpr,
    payload: &RetainedBvRefutation,
    limits: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    ledger: &mut Ledger,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Shape, MeteredError> {
    let (proof, reduced, shape) = ledger.phase(
        Phase::Prefix,
        limits.resolution.validation.max_work,
        |grant| {
            let mut prefix_limits = limits.clone();
            prefix_limits.resolution.validation.max_work = grant;
            let mut control = Control::new(&prefix_limits);
            control.charge(1, poll)?;
            if payload.version != VERSION {
                return Err(malformed("unsupported retained BV refutation version").into());
            }
            let shape = control.payload(payload, poll)?;
            let payload_bytes = control.bytes;
            let mut construction = prefix_limits.clone();
            construction.max_construction_bytes =
                construction
                    .max_construction_bytes
                    .min(control.remaining_bytes(
                        size_of::<BvBlastProof>() + "(not (= <lhs-expr> <rhs-expr>))".len(),
                    )?);
            let graph = cnf::build_bv_expr_cnf(lhs, rhs, &construction, poll)?.into_graph();
            let graph_bytes = control.graph(&graph, poll)?;
            let dag = codec::decode(payload, shape, &graph, &mut control, poll)?;
            let reduced = control.replay_limits(&graph, graph_bytes, payload_bytes, poll)?;
            Ok((
                (compact::ExprRefutation { graph, dag }, reduced, shape),
                u128::from(control.work),
            ))
        },
    )?;
    validate(&proof, &reduced, gates, ledger, poll)?;
    drop(proof);
    finish_expr_export(Some(limits), poll)?;
    Ok(shape)
}

fn validate(
    proof: &compact::ExprRefutation,
    limits: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    ledger: &mut Ledger,
    poll: &mut dyn FnMut() -> bool,
) -> Result<(), MeteredError> {
    // Binding visits were included in the retained prefix before this call.
    proof.bind(poll)?;
    ledger.phase(Phase::Gates, gates.max_work, |grant| {
        let mut gates = *gates;
        gates.max_work = grant;
        let work = proof
            .graph
            .validate_cnf_with_limits_and_cancellation_work(&gates, poll)
            .map_err(|error| match error {
                BvBlastValidateError::Cancelled => BvExprExportError::Cancelled,
                other => BvExprExportError::RefutationNotSurfaceable(format!(
                    "compact CNF replay: {other}"
                )),
            })?;
        Ok(((), u128::from(work)))
    })?;
    ledger.phase(Phase::Dag, limits.resolution.validation.max_work, |grant| {
        let mut validation = limits.resolution.validation.clone();
        validation.max_work = grant;
        let work = proof
            .dag
            .validate_with_limits_and_cancellation_work(&validation, poll)
            .map_err(|error| {
                map_bounded_resolution_error(
                    ResolutionProofError::Validation(error),
                    &limits.resolution,
                )
            })?;
        Ok(((), u128::from(work)))
    })?;
    finish_expr_export(Some(limits), poll)?;
    Ok(())
}

#[cfg(test)]
mod tests;
