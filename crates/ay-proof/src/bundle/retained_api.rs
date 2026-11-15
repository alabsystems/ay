// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opaque retained proof ownership, not external-query authority.
//!
//! Capture and consuming finalization preserve the two independent strict
//! exporter checks. The caller must bind the immutable first report to its
//! live exact-query source and full declarations BEFORE finalization. Internal
//! first-use inventory equality does not authenticate that external source.
//! Every subsequent read is independently checked without replacement proof
//! production or legacy fallback.
//!
//! One caller-owned sticky cumulative callback must cover source construction,
//! capture, narrowing, replay, encoding and later same-request admission. These
//! APIs cannot enforce callback identity or prevent a caller resetting its own
//! ledger. Per-operation ceilings are not aggregate work grants. Admitted costs
//! are never refunded when owners are dropped. Existing source-counted checker
//! and codec ceilings remain finite and may only be tightened.
//!
//! The original producer deadline survives all operations on its opaque owner.
//! A separately transported byte document may enter the distinct offline-reader
//! API under a new consumer request's original deadline. Borrowed byte input and
//! already-owned source snapshots must be admitted separately by their caller.
//! Logical accounting is not allocator-exact RSS or a hard latency guarantee:
//! individual arithmetic, allocation, serde leaf and destruction intervals
//! remain opaque, with terminal admission after operation-local cleanup.

use super::{retained, retained_reader, BundleReCheck, SerializableProofBundle};
use crate::bv_blast_solver::retained::wire::WireLimits;
use crate::checker::bv_bitblast::retained_session::{transport_wire_limits, RetainedStepPayload};
use crate::ProofCheckError;
use ay_core::{time::Instant, TermId};

mod control;
mod diagnostics;
mod finish;
mod transport;
use control::Control;
pub use diagnostics::{
    RetainedReadDiagnostics, RetainedReadErrorClass, RetainedReadFailure, RetainedReadRefusal,
    RetainedReadStage, RetainedReadTerminal,
};
pub use transport::{
    re_check_retained_bundle_strict_with_resource_control,
    read_retained_proof_bundle_with_resource_control,
    read_retained_proof_bundle_with_resource_control_and_diagnostics,
};

/// Actual retained-envelope schema, including mandatory namespace identities.
pub const RETAINED_PROOF_BUNDLE_SCHEMA: &str = retained::RETAINED_SCHEMA;

/// Explicit per-document ceilings, never a fresh cumulative caller allowance.
/// The retained codec intersects these with its existing source-counted limits.
#[derive(Debug, Clone, Copy)]
pub struct RetainedProofTransportLimits {
    /// Complete JSON output/input ceiling, including the legacy snapshot.
    pub max_json_bytes: usize,
    /// Accounted new transport allocations and conservative parser scratch.
    pub max_storage_bytes: usize,
    /// Additional transport work ceiling; all debits still reach the caller.
    pub max_work: u64,
}

/// First independently checked snapshot plus privately captured evidence.
/// Neither this owner nor its report authenticates an external query. There is
/// deliberately no serialization, cloning, raw snapshot or mutable accessor.
pub struct RetainedProofCapture {
    snapshot: SerializableProofBundle,
    payloads: Vec<RetainedStepPayload>,
    first: BundleReCheck,
    deadline: Instant,
}

/// Actual v6 owner after mandatory independent second retained replay.
/// No raw-v5 conversion or mutable access can detach its required inventory.
/// It is proof/context validity, not a reusable external-query proof permit.
pub struct RetainedProofBundle {
    envelope: retained::RetainedBundle,
    deadline: Instant,
    wire: WireLimits,
}

// Debug must not become an uncontrolled payload/snapshot serialization escape.
impl std::fmt::Debug for RetainedProofCapture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RetainedProofCapture")
            .finish_non_exhaustive()
    }
}

impl std::fmt::Debug for RetainedProofBundle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RetainedProofBundle")
            .finish_non_exhaustive()
    }
}

/// Capture exactly one full strict pass, retaining its ordinary/conditional BV
/// evidence. The already-owned snapshot must have been separately admitted.
/// Any incomplete proof, resource refusal or late cancellation publishes no
/// pending owner. This does not execute a legacy strict pass beforehand.
pub fn capture_strict_retained_bundle_with_resource_control(
    snapshot: SerializableProofBundle,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<RetainedProofCapture, ProofCheckError> {
    control::run(deadline, progress, move |control| {
        let (first, payloads) =
            retained_reader::capture(&snapshot, deadline, &mut |work, bytes| {
                control.charge(work, bytes).is_ok()
            })?;
        if !first.quality.is_complete() {
            return Err(control.malformed("retained capture proof is incomplete")?);
        }
        Ok(RetainedProofCapture {
            snapshot,
            payloads,
            first,
            deadline,
        })
    })
}

impl RetainedProofCapture {
    /// Borrow the authentic first report for LIVE source/declaration binding.
    /// Mutating a detached report cannot change this pending owner's inventory.
    pub fn first_check(&self) -> &BundleReCheck {
        &self.first
    }
}

impl RetainedProofBundle {
    /// Actual immutable wire schema, not proof authority.
    pub fn schema(&self) -> &str {
        &self.envelope.parts().0.schema
    }

    /// Exact nonempty first-use assumption inventory of this checked snapshot.
    /// Its IDs are not meaningful against a different arena or external source.
    pub fn obligation_assertions(&self) -> &[TermId] {
        &self.envelope.parts().0.obligation_assertions
    }

    /// Independently replay this owner without search, replacement evidence or
    /// legacy fallback. The caller retains the same cumulative ledger. The
    /// requested deadline only tightens the owner's original request deadline.
    pub fn replay_exact_with_resource_control(
        &self,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<BundleReCheck, ProofCheckError> {
        let deadline = self.deadline.min(deadline);
        control::run(deadline, progress, |control| self.replay(deadline, control))
    }

    fn replay(
        &self,
        deadline: Instant,
        control: &mut Control<'_>,
    ) -> Result<BundleReCheck, ProofCheckError> {
        let checked = retained_reader::replay_versioned_with_wire_limits(
            &self.envelope,
            Some(self.wire),
            deadline,
            &mut |work, bytes| control.charge(work, bytes).is_ok(),
        )?;
        control.exact_inventory(&checked, self.obligation_assertions())?;
        Ok(checked)
    }
}

#[cfg(test)]
mod tests;
