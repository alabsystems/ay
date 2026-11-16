// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private retained evidence path through full snapshot rechecking.
//!
//! The legacy v5 snapshot and this separate untrusted inventory are NOT a new
//! wire format. The separate `retained::replay_bundle` entry owns and admits a
//! complete v6 document before entering this checker. External problem binding
//! and exporter/CHC/sealed-reader adoption
//! remain required before this can replace a consumer path.
//! Public legacy serde/read APIs deliberately remain unchanged.
//! The private v6 in-memory entry preserves its actual schema and mandatory
//! inventory; direct in-memory callers must still admit those owners themselves.

use super::*;
use crate::bv_blast_solver::retained::wire::WireLimits;
use crate::checker::bv_bitblast::retained_session::{RetainedOperation, RetainedStepPayload};
use crate::quality::retained::{with_control, Request};
use ay_core::time::Instant;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

/// Capture untrusted retained bytes only after full independent snapshot,
/// declaration, proof and terminal checks. Own no source-side solver state.
pub(crate) fn capture(
    bundle: &SerializableProofBundle,
    deadline: Instant,
    progress: Progress<'_>,
) -> Result<(BundleReCheck, Vec<RetainedStepPayload>), ProofCheckError> {
    with_control(deadline, progress, |progress| {
        cancellation::reconstruct_and_check_with_retained(
            bundle,
            Some(Request {
                operation: RetainedOperation::Capture,
                wire_limits: None,
                deadline,
            }),
            progress,
        )
    })
}

/// Each independent read reconstructs a fresh TermStore and authenticates the
/// exact snapshot/context before binding and replaying every required payload.
/// It never produces replacement payloads or falls back to proof search.
#[cfg(test)]
pub(crate) fn replay(
    bundle: &SerializableProofBundle,
    payloads: &[RetainedStepPayload],
    deadline: Instant,
    progress: Progress<'_>,
) -> Result<BundleReCheck, ProofCheckError> {
    with_control(deadline, progress, |progress| {
        let (checked, output) = cancellation::reconstruct_and_check_with_retained(
            bundle,
            Some(Request {
                operation: RetainedOperation::Replay(payloads),
                wire_limits: None,
                deadline,
            }),
            progress,
        )?;
        debug_assert_eq!(output, []);
        Ok(checked)
    })
}

/// Independently replay a private owning v6 envelope without normalization to
/// v5, proof-search fallback or replacement evidence. Input owners must already
/// be admitted by the caller; this is not a JSON decoder. Reconstruction,
/// context authentication, retained replay and temporary-owner cleanup share
/// the original deadline and cumulative caller callback. Success still needs
/// binding to the intended external problem, just like the public v5 reader.
#[cfg(test)]
pub(super) fn replay_versioned(
    envelope: &retained::RetainedBundle,
    deadline: Instant,
    progress: Progress<'_>,
) -> Result<BundleReCheck, ProofCheckError> {
    replay_versioned_with_wire_limits(envelope, None, deadline, progress)
}

/// Caller ceilings can tighten, but never enlarge, the source-counted limits.
pub(super) fn replay_versioned_with_wire_limits(
    envelope: &retained::RetainedBundle,
    wire_limits: Option<WireLimits>,
    deadline: Instant,
    progress: Progress<'_>,
) -> Result<BundleReCheck, ProofCheckError> {
    let deadline = wire_limits.map_or(deadline, |wire| deadline.min(wire.deadline));
    with_control(deadline, progress, |progress| {
        cancellation::reconstruct_and_replay_versioned(envelope, wire_limits, deadline, progress)
    })
}

#[cfg(test)]
mod tests;
