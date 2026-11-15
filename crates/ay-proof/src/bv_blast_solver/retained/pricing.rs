// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked downward prices for ordinary, non-premised no-search replay.
//! A price is neither validation nor original-source authority. The planner
//! itself is paid on the original owner; every later reader still reconstructs
//! source, checks all gates and independently replays every RUP row.
//! Byte envelopes are logical coexistence, not physical allocator/RSS bounds.

use super::*;
use crate::bv_blast_export::BvBlastValidateLimits;
use ay_sat::{conservative_rup_validation_work_bound, ConservativeRupSourceShape};

mod source;
use source::{source_bound, SourceBound};
#[cfg(test)]
mod tests;

/// Downward limits owned by the same single-use ordinary credit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReplayPrice {
    pub(crate) work: usize,
    pub(crate) bytes: usize,
    native_work: usize,
    construction: usize,
    codec: usize,
    validation: usize,
    wire_storage: usize,
}

impl ReplayPrice {
    /// Native work remains reserved externally; never lends expression credit.
    pub(crate) fn with_native_work(mut self, native: usize) -> Option<Self> {
        self.work = self.work.checked_add(native)?;
        self.native_work = self.native_work.checked_add(native)?;
        Some(self)
    }

    pub(crate) fn expression_work(self) -> Option<usize> {
        self.work.checked_sub(self.native_work)
    }

    pub(crate) fn tighten(self, proof: &mut BvExprProofLimits, wire: &mut wire::WireLimits) {
        proof.max_construction_bytes = proof.max_construction_bytes.min(self.construction);
        proof.resolution.max_codec_bytes = proof.resolution.max_codec_bytes.min(self.codec);
        proof.resolution.validation.max_bytes =
            proof.resolution.validation.max_bytes.min(self.validation);
        wire.max_storage_bytes = wire.max_storage_bytes.min(self.wire_storage);
        // The consumed WorkAllowance bounds all additive work phases. Their
        // independent original counted ceilings stay unchanged.
    }
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum PriceError {
    #[error("retained replay pricing accounting overflow")]
    Overflow,
    #[error(transparent)]
    Source(#[from] BvExprExportError),
    #[error(transparent)]
    Wire(#[from] wire::WireError),
    #[error(transparent)]
    Resolution(#[from] ay_sat::ResolutionValidationError),
}

fn add(a: usize, b: usize) -> Result<usize, PriceError> {
    a.checked_add(b).ok_or(PriceError::Overflow)
}

fn mul(a: usize, b: usize) -> Result<usize, PriceError> {
    a.checked_mul(b).ok_or(PriceError::Overflow)
}

/// Prepay one complete decode before parsing; callers must not debit telemetry
/// afterward or refund this conservative reservation. No payload is trusted.
pub(crate) fn wire_bounds(bytes: usize) -> Result<(usize, usize), PriceError> {
    // Lexical +16 parser passes +number/items +geometric copies and shape
    // visits fit24 passes. Each row/number requires an actual input byte;
    // geometric capacities and old/new overlap fit256 bytes per input byte.
    Ok((
        add(mul(bytes, 24)?, 16 * 1024 + 64)?,
        add(mul(bytes, 256)?, 16 * 1024 + 256)?,
    ))
}

/// Only ordinary source enters. Decode and source preflight are separately
/// prepaid by the bridge before entry, including callbacks/EOF and scratch.
/// The source is the actual lowered clause, not dimensions supplied by wire.
pub(crate) fn price(
    lhs: &BvExpr,
    rhs: &BvExpr,
    bytes: &[u8],
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &wire::WireLimits,
    poll: &mut dyn FnMut() -> bool,
) -> Result<ReplayPrice, PriceError> {
    let (decode_work, decode_bytes) = wire_bounds(bytes.len())?;
    let mut narrow = *wire;
    narrow.max_work = narrow
        .max_work
        .min(u64::try_from(decode_work).map_err(|_| PriceError::Overflow)?);
    narrow.max_storage_bytes = narrow.max_storage_bytes.min(decode_bytes);
    let decoded = wire::decode(bytes, &narrow, proof, gates, poll).result?;
    let source = source_bound(lhs, rhs, proof, poll)?;
    let result = from_dimensions(
        &source,
        &decoded,
        backing_capacity,
        proof,
        decode_work,
        decode_bytes,
        poll,
    );
    drop(decoded);
    drop(source);
    finish_expr_export(Some(proof), poll)?;
    result
}

fn from_dimensions(
    source: &SourceBound,
    payload: &RetainedBvRefutation,
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    decode_work: usize,
    decode_bytes: usize,
    poll: &mut dyn FnMut() -> bool,
) -> Result<ReplayPrice, PriceError> {
    let (rows, literals, hints) = dimensions(payload, poll)?;
    let shape = ConservativeRupSourceShape {
        num_vars: source.gates,
        original_clauses: source.clauses,
        original_literals: source.literals,
        max_original_width: source.width.max(4),
    };
    // A loose upper price must not widen or prematurely replace the old cap:
    // retain its count/deadline controls, then intersect the returned work.
    let mut pricing_limits = proof.resolution.validation.clone();
    pricing_limits.max_work = u64::MAX;
    let rup = conservative_rup_validation_work_bound(
        shape,
        payload
            .rows
            .iter()
            .map(|row| (row.literals.len(), row.hints.len())),
        0,
        &pricing_limits,
        poll,
    )?;
    let row_records = add(32, mul(rows, 8)?)?;
    let source_visits = add(
        source.gates,
        add(mul(source.clauses, 7)?, mul(source.literals, 2)?)?,
    )?;
    let prefix = add(row_records, add(add(literals, hints)?, source_visits)?)?;
    // Definitions<=4G; variable/equality<=G+2W; canonical-clause meter
    // <=1+literal width+8*(4+4)<=65+literal width per source clause.
    let gate_work = add(
        mul(source.gates, 5)?,
        add(
            mul(source.clauses, 65)?,
            add(source.literals, mul(source.width, 2)?)?,
        )?,
    )?;
    let work = add(
        add(decode_work, source.construction_work)?,
        add(
            prefix,
            add(
                gate_work,
                usize::try_from(rup).map_err(|_| PriceError::Overflow)?,
            )?,
        )?,
    )?;
    storage_price(
        source,
        rows,
        literals,
        hints,
        backing_capacity,
        proof,
        work,
        decode_bytes,
    )
}

fn dimensions(
    payload: &RetainedBvRefutation,
    poll: &mut dyn FnMut() -> bool,
) -> Result<(usize, usize, usize), PriceError> {
    let (mut rows, mut literals, mut hints) = (0, 0, 0);
    for row in &payload.rows {
        poll_export(poll)?;
        rows = add(rows, 1)?;
        literals = add(literals, row.literals.len())?;
        hints = add(hints, row.hints.len())?;
    }
    Ok((rows, literals, hints))
}

fn storage_price(
    source: &SourceBound,
    rows: usize,
    literals: usize,
    hints: usize,
    backing_capacity: usize,
    proof: &BvExprProofLimits,
    work: usize,
    decode_bytes: usize,
) -> Result<ReplayPrice, PriceError> {
    // Owned DAG records plus exact-reserve capacity slack, source-original
    // literals and derived rows/hints. Actual capacities are STILL checked by
    // the unchanged codec and validator against these downward caps.
    let record_bytes = mul(add(source.clauses, rows)?, 128)?;
    let literal_bytes = mul(add(source.literals, literals)?, 8)?;
    let hint_bytes = mul(hints, 16)?;
    let dag = add(1024, add(record_bytes, add(literal_bytes, hint_bytes)?)?)?;
    let construction = proof.max_construction_bytes.min(source.construction_bytes);
    let wire_storage = decode_bytes
        .min(proof.resolution.max_codec_bytes)
        .min(proof.resolution.validation.max_bytes);
    let codec = proof
        .resolution
        .max_codec_bytes
        .min(add(construction, add(wire_storage, dag)?)?);
    let scratch = add(
        mul(add(source.clauses, rows)?, 128)?,
        add(
            mul(source.gates, size_of::<Option<bool>>() + size_of::<usize>())?,
            1024,
        )?,
    )?;
    let validation = proof
        .resolution
        .validation
        .max_bytes
        .min(add(codec, scratch)?);
    let gate_scratch = add(
        mul(source.gates, size_of::<bool>() + size_of::<Option<u32>>())?,
        add(
            mul(source.clauses, size_of::<usize>())?,
            mul(source.width.max(4), 256)?,
        )?,
    )?;
    let active = add(construction, wire_storage)?.max(add(validation, gate_scratch)?);
    // The lowered tree remains borrowed for all phases. Its unchanged
    // 100k-node/cell/term/arity bounds fit the existing source-phase envelope.
    // Allocator bookkeeping and opaque hash/destructor latency remain open.
    let bytes = add(proof.max_construction_bytes, add(backing_capacity, active)?)?;
    Ok(ReplayPrice {
        work,
        bytes,
        native_work: 0,
        construction,
        codec,
        validation,
        wire_storage,
    })
}
