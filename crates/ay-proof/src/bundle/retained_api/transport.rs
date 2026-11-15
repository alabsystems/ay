// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn limits(
    requested: RetainedProofTransportLimits,
    mut wire: WireLimits,
    deadline: Instant,
) -> (retained::BundleLimits, WireLimits) {
    wire.deadline = wire.deadline.min(deadline);
    wire.max_json_bytes = wire.max_json_bytes.min(requested.max_json_bytes);
    wire.max_storage_bytes = wire.max_storage_bytes.min(requested.max_storage_bytes);
    wire.max_work = wire.max_work.min(requested.max_work);
    let bundle = retained::BundleLimits {
        max_json_bytes: requested.max_json_bytes,
        max_storage_bytes: requested.max_storage_bytes,
        max_work: requested.max_work,
        deadline: wire.deadline,
    };
    (bundle, wire)
}

fn transport_error(error: retained::TransportError, control: &mut Control<'_>) -> ProofCheckError {
    match error {
        retained::TransportError::Deadline => ProofCheckError::Cancelled,
        retained::TransportError::Refused
        | retained::TransportError::Overflow
        | retained::TransportError::Allocation
        | retained::TransportError::Limit { .. } => ProofCheckError::ResourceLimit,
        _ => {
            match control.malformed("invalid retained proof document or schema/inventory presence")
            {
                Ok(error) | Err(error) => error,
            }
        }
    }
}

impl RetainedProofBundle {
    /// Serialize the complete actual-v6 envelope without cloning payloads,
    /// escaping them into strings or shedding the mandatory retained field.
    /// This is controlled transport, not fresh proof or external-source authority.
    /// The original request deadline and cumulative caller ledger remain active.
    pub fn encode_with_resource_control(
        &self,
        requested: RetainedProofTransportLimits,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Vec<u8>, ProofCheckError> {
        let deadline = self.deadline.min(deadline);
        control::run(deadline, progress, |control| {
            let (bundle, wire) = limits(requested, self.wire, deadline);
            retained::encode_versioned_bundle(
                &self.envelope,
                &bundle,
                &wire,
                deadline,
                &mut |work, bytes| control.charge(work, bytes).is_ok(),
            )
            .result
            .map_err(|error| transport_error(error, control))
        })
    }
}

/// Decode and independently replay an externally transported actual-v6
/// document under a NEW consumer request's original deadline. That deadline is
/// not copied from untrusted wire metadata, nor does this renew a producer's
/// opaque owner. Decoder allocations, replay and exact inventory comparison
/// debit the same caller callback; input ownership must be admitted separately.
/// No legacy fallback, replacement evidence or external-query binding occurs.
pub fn read_retained_proof_bundle_with_resource_control(
    bytes: &[u8],
    requested: RetainedProofTransportLimits,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(RetainedProofBundle, BundleReCheck), ProofCheckError> {
    control::run(deadline, progress, |control| {
        let (limits, wire) = limits(requested, transport_wire_limits(deadline), deadline);
        let envelope =
            retained::decode_bundle(bytes, &limits, &wire, deadline, &mut |work, bytes| {
                control.charge(work, bytes).is_ok()
            })
            .result
            .map_err(|error| transport_error(error, control))?;
        let bundle = RetainedProofBundle {
            envelope,
            wire,
            deadline,
        };
        let checked = bundle.replay(deadline, control)?;
        Ok((bundle, checked))
    })
}

/// The exact same reader transaction with fixed-size first/terminal observations.
/// The unchanged error and caller callback remain authoritative; observations
/// neither authorize a report nor renew a decoder ceiling or original owner.
/// This header is cleared at entry, including entry refusal. Panic/unwind may
/// leave it incomplete and cannot be interpreted as a completed transaction.
pub fn read_retained_proof_bundle_with_resource_control_and_diagnostics(
    bytes: &[u8],
    requested: RetainedProofTransportLimits,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
    diagnostics: &mut RetainedReadDiagnostics,
) -> Result<(RetainedProofBundle, BundleReCheck), ProofCheckError> {
    *diagnostics = RetainedReadDiagnostics::default();
    let (mut first, mut terminal) = (None, None);
    let mut stage = RetainedReadStage::Entry;
    let result = control::run_observed(deadline, progress, &mut terminal, |control| {
        stage = RetainedReadStage::Decode;
        let (limits, wire) = limits(requested, transport_wire_limits(deadline), deadline);
        let mut decode_first = None;
        let decoded = retained::decode_bundle_observed(
            bytes,
            &limits,
            &wire,
            deadline,
            &mut |work, bytes| control.charge(work, bytes).is_ok(),
            &mut decode_first,
        );
        if let Some(error) = decode_first {
            diagnostics::transport(&mut first, error);
        }
        let envelope = decoded
            .result
            .map_err(|error| transport_error(error, control))?;
        let bundle = RetainedProofBundle {
            envelope,
            wire,
            deadline,
        };
        stage = RetainedReadStage::StrictReplay;
        let checked = bundle.replay(deadline, control).map_err(|error| {
            diagnostics::proof(&mut first, stage, &error);
            error
        })?;
        stage = RetainedReadStage::FinalControl;
        Ok((bundle, checked))
    });
    let reported = result.as_ref().err().map(RetainedReadErrorClass::of);
    if let Err(error) = &result {
        diagnostics::proof(&mut first, stage, error);
    }
    *diagnostics = RetainedReadDiagnostics {
        first,
        terminal,
        reported,
    };
    result
}

/// Independently recheck a transported v6 document, dropping its complete
/// decoded owner before final admission of the report. This fresh-reader entry
/// authenticates internal proof/context and exact first-use inventory only;
/// the consumer must still bind external assertions and complete declarations.
pub fn re_check_retained_bundle_strict_with_resource_control(
    bytes: &[u8],
    requested: RetainedProofTransportLimits,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<BundleReCheck, ProofCheckError> {
    control::run(deadline, progress, |control| {
        let (bundle, checked) = read_retained_proof_bundle_with_resource_control(
            bytes,
            requested,
            deadline,
            &mut |work, bytes| control.charge(work, bytes).is_ok(),
        )?;
        drop(bundle);
        Ok(checked)
    })
}
