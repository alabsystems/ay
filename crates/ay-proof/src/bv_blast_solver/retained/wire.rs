// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded JSON for untrusted retained rows, not an outer proof-bundle format.
//!
//! Byte admission and a token/depth census precede serde. Collection requests
//! are admitted before allocation, including old/new buffer overlap; actual
//! capacities are checked afterward. The opaque parser/error reserve is a
//! conservative logical allowance, NOT an allocator-exact RSS measurement.
//! Allocator bookkeeping, allocation/destruction latency and physical slack
//! still require the caller's process/tree RSS backstop.
//!
//! Serde reads a borrowed slice through a 256-byte grant adapter. Even long
//! whitespace runs poll before each grant; stream positions are incremental,
//! not whole-input error rescans. String/number tokens and container depth are
//! separately bounded. Allocation, small parser/error spans and destruction
//! remain opaque: this is not a hard per-callback wall-time guarantee.

use super::*;

mod control;
mod decode;
mod encode;
mod lexical;
pub(crate) mod pair;
mod shape;

use control::Control;

/// Explicit private wire grants. JSON bytes are distinct from the existing
/// logical fixed-width `max_proof_output_bytes` accounting.
#[derive(Clone, Copy, Debug)]
pub(crate) struct WireLimits {
    pub(crate) max_json_bytes: usize,
    pub(crate) max_rows: usize,
    pub(crate) max_literals: usize,
    pub(crate) max_hints: usize,
    pub(crate) max_work: u64,
    pub(crate) max_storage_bytes: usize,
    pub(crate) deadline: Instant,
}

/// Charges, including conservative reservations, remain visible on refusal.
/// A future caller must debit work once before granting independent replay.
/// Peak storage is coexistence accounting, not an additional cumulative debit;
/// returned storage identifies the owner that survives this operation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct WireUsage {
    pub(crate) charged_work: u128,
    pub(crate) peak_storage_bytes: usize,
    pub(crate) returned_owned_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum WireError {
    #[error("retained wire cancelled")]
    Cancelled,
    #[error("retained wire deadline exceeded")]
    Deadline,
    #[error("retained wire requires an absolute proof deadline")]
    MissingDeadline,
    #[error("invalid retained wire JSON")]
    InvalidJson,
    #[error("invalid retained wire payload: {0}")]
    InvalidPayload(&'static str),
    #[error("retained wire {resource} limit {limit} exceeded by {actual}")]
    Limit {
        resource: &'static str,
        limit: u128,
        actual: u128,
    },
    #[error("retained wire accounting overflow")]
    Overflow,
    #[error("retained wire allocation refused")]
    Allocation,
}

#[derive(Debug)]
pub(crate) struct WireOutcome<T> {
    pub(crate) result: Result<T, WireError>,
    pub(crate) usage: WireUsage,
}

pub(crate) fn decode(
    bytes: &[u8],
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<RetainedBvRefutation> {
    run(wire, proof, gates, poll, |control| {
        decode::read(bytes, control)
    })
}

pub(crate) fn encode(
    payload: &RetainedBvRefutation,
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
) -> WireOutcome<Vec<u8>> {
    run(wire, proof, gates, poll, |control| {
        encode::write(payload, control)
    })
}

fn run<T>(
    wire: &WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    poll: &mut dyn FnMut() -> bool,
    operation: impl FnOnce(&mut Control<'_>) -> Result<T, WireError>,
) -> WireOutcome<T> {
    let limits = match effective_limits(*wire, proof, gates) {
        Ok(limits) => limits,
        Err(error) => {
            return WireOutcome {
                result: Err(error),
                usage: WireUsage::default(),
            }
        }
    };
    let mut control = Control::new(limits, poll);
    let result = control.poll().and_then(|()| operation(&mut control));
    let result = finish(result, &mut control);
    WireOutcome {
        result,
        usage: control.usage,
    }
}

fn finish<T>(result: Result<T, WireError>, control: &mut Control<'_>) -> Result<T, WireError> {
    match result {
        Err(error) => {
            // The operation has already dropped partial payloads, parser,
            // serializer and their error/scratch owners before returning Err.
            let _ = control.fail::<()>(error);
            control.usage.returned_owned_bytes = 0;
            match control.finish() {
                Err(error) => Err(error),
                Ok(()) => Err(error),
            }
        }
        Ok(value) => match control.finish() {
            Ok(()) => Ok(value),
            Err(error) => {
                drop(value);
                control.usage.returned_owned_bytes = 0;
                // This observed stop is sticky: cleanup cannot revive it.
                match control.finish() {
                    Err(error) => Err(error),
                    Ok(()) => Err(error),
                }
            }
        },
    }
}

fn effective_limits(
    mut wire: WireLimits,
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
) -> Result<WireLimits, WireError> {
    let resolution = &proof.resolution;
    let validation = &resolution.validation;
    wire.deadline = wire
        .deadline
        .min(resolution.deadline.ok_or(WireError::MissingDeadline)?);
    for deadline in [validation.deadline, gates.deadline].into_iter().flatten() {
        wire.deadline = wire.deadline.min(deadline);
    }
    wire.max_rows = wire
        .max_rows
        .min(resolution.max_derived_steps)
        .min(validation.max_derived_steps);
    wire.max_literals = wire
        .max_literals
        .min(resolution.max_derived_literals)
        .min(validation.max_derived_literals);
    wire.max_hints = wire
        .max_hints
        .min(resolution.max_hints)
        .min(validation.max_hints);
    wire.max_work = wire.max_work.min(validation.max_work);
    wire.max_storage_bytes = wire
        .max_storage_bytes
        .min(resolution.max_codec_bytes)
        .min(validation.max_bytes);
    Ok(wire)
}

#[cfg(test)]
mod tests;
