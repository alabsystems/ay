// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private, untrusted transport for ordinary expression refutations.
//! This is not part of any proof-bundle schema or a checked admission token.
//! Source construction, gate replay and the producer's internal SAT validation
//! retain their distinct existing limits. Added transport/binding work shares
//! a cumulative prefix with the final DAG replay. The separate `metered` path
//! additionally shares reported producer, gate, DAG and wire work within one
//! consumed allowance; compatibility entry points retain their old limits.

use super::*;
use crate::bv_blast_export::BvBlastValidateLimits;
use serde::{Deserialize, Serialize};

mod accounting;
mod codec;
pub(crate) mod metered;
pub(crate) mod pricing;
#[cfg(test)]
pub(crate) mod producer_test_counter;
pub(crate) mod wire;
pub(crate) mod work;

use accounting::{Control, Shape};

const VERSION: u32 = 1;

/// Untrusted plain data. Deserializing this type is NOT allocation-bounded by
/// the in-memory capture/replay APIs; a future wire reader must bound input and
/// decoding before allocating it. Original clauses and variable counts are
/// intentionally absent: only a fresh live-source reconstruction supplies them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RetainedBvRefutation {
    pub(crate) version: u32,
    pub(crate) rows: Vec<RetainedRupRow>,
    pub(crate) empty_clause_id: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RetainedRupRow {
    pub(crate) id: u64,
    /// Version 1: 2 * zero-based variable + negation bit (not DIMACS).
    pub(crate) literals: Vec<u32>,
    pub(crate) hints: Vec<u64>,
}

/// Produce and independently validate, then retain only untrusted RUP rows.
/// A later reader must reconstruct the source and earn acceptance again.
#[cfg(test)]
pub(crate) fn capture_bv_expr_refutation(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<RetainedBvRefutation, BvExprExportError> {
    let (limits, replay) = effective_limits(limits, replay)?;
    cancellation::run(keep_going, |poll| {
        let preflight = preflight_bv_equality(lhs, rhs, &limits, poll)?;
        let proof = build_bv_expr_refutation(lhs, rhs, Some((&limits, preflight)), poll)?;
        let mut control = Control::new(&limits);
        let graph_bytes = control.graph(&proof.graph, poll)?;
        let shape = control.dag(&proof.dag, poll)?;
        let payload = codec::encode(&proof.dag, shape, &mut control, poll)?;
        let payload_bytes = control.payload_bytes(&payload, poll)?;
        let reduced = control.replay_limits(&proof.graph, graph_bytes, payload_bytes, poll)?;
        let result = proof.validate(&reduced, &replay, poll);
        drop(proof);
        result?;
        // The success boundary is after all temporary graph/DAG owners drop.
        finish_expr_export(Some(&limits), poll)?;
        Ok(payload)
    })
}

/// Read one declared retained payload without any SAT-search fallback. Missing,
/// unsupported or corrupt data refuses even if fresh proof search might work.
#[cfg(test)]
pub(crate) fn replay_bv_expr_refutation(
    lhs: &BvExpr,
    rhs: &BvExpr,
    payload: Option<&RetainedBvRefutation>,
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), BvExprExportError> {
    let (limits, replay) = effective_limits(limits, replay)?;
    cancellation::run(keep_going, |poll| {
        let mut control = Control::new(&limits);
        control.charge(1, poll)?;
        let payload = payload.ok_or_else(|| malformed("missing retained BV refutation"))?;
        if payload.version != VERSION {
            return Err(malformed("unsupported retained BV refutation version"));
        }
        let shape = control.payload(payload, poll)?;
        let payload_bytes = control.bytes;
        // The caller-owned payload stays live during construction. Do not let
        // the existing construction reservation exceed the remaining codec
        // envelope; allocator/destructor transients still need an RSS guard.
        let mut construction = limits.clone();
        construction.max_construction_bytes = construction.max_construction_bytes.min(
            // The shared CNF graph wrapper adds this fixed diagnostic string.
            control.remaining_bytes(
                size_of::<BvBlastProof>() + "(not (= <lhs-expr> <rhs-expr>))".len(),
            )?,
        );
        let graph = cnf::build_bv_expr_cnf(lhs, rhs, &construction, poll)?.into_graph();
        let graph_bytes = control.graph(&graph, poll)?;
        let dag = codec::decode(payload, shape, &graph, &mut control, poll)?;
        let reduced = control.replay_limits(&graph, graph_bytes, payload_bytes, poll)?;
        let proof = compact::ExprRefutation { graph, dag };
        let result = proof.validate(&reduced, &replay, poll);
        drop(proof);
        result?;
        finish_expr_export(Some(&limits), poll)
    })
}

fn effective_limits(
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
) -> Result<(BvExprProofLimits, BvBlastValidateLimits), BvExprExportError> {
    let mut limits = limits.clone();
    let mut replay = *replay;
    let mut deadline = limits
        .resolution
        .deadline
        .ok_or_else(|| malformed("bounded proof limits require an absolute deadline"))?;
    for other in [limits.resolution.validation.deadline, replay.deadline]
        .into_iter()
        .flatten()
    {
        deadline = deadline.min(other);
    }
    limits.resolution.deadline = Some(deadline);
    limits.resolution.validation.deadline = Some(deadline);
    replay.deadline = Some(deadline);
    Ok((limits, replay))
}

fn malformed(message: &str) -> BvExprExportError {
    BvExprExportError::Malformed(message.to_owned())
}

#[cfg(test)]
mod tests;
