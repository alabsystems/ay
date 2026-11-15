// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::producer_limits::counted_limits_until;
use super::*;
use crate::bv_blast_solver::BvExprProofLimits;
use std::mem::size_of;

pub(super) fn wire_limits(limits: &BvExprProofLimits, deadline: Instant) -> WireLimits {
    let resolution = &limits.resolution;
    let validation = &resolution.validation;
    WireLimits {
        // JSON transport is bounded separately from the LRAT output byte cap.
        max_json_bytes: resolution.max_codec_bytes,
        max_rows: resolution
            .max_derived_steps
            .min(validation.max_derived_steps),
        max_literals: resolution
            .max_derived_literals
            .min(validation.max_derived_literals),
        max_hints: resolution.max_hints.min(validation.max_hints),
        max_work: validation.max_work,
        max_storage_bytes: resolution.max_codec_bytes.min(validation.max_bytes),
        deadline,
    }
}

pub(super) fn effective_wire_limits(
    deadline: Instant,
    requested: Option<WireLimits>,
) -> WireLimits {
    let mut wire = wire_limits(&counted_limits_until(deadline), deadline);
    if let Some(requested) = requested {
        wire.max_json_bytes = wire.max_json_bytes.min(requested.max_json_bytes);
        wire.max_rows = wire.max_rows.min(requested.max_rows);
        wire.max_literals = wire.max_literals.min(requested.max_literals);
        wire.max_hints = wire.max_hints.min(requested.max_hints);
        wire.max_work = wire.max_work.min(requested.max_work);
        wire.max_storage_bytes = wire.max_storage_bytes.min(requested.max_storage_bytes);
        wire.deadline = wire.deadline.min(requested.deadline);
    }
    wire
}

pub(super) fn admit(
    credits: &PrepaidBvCredits<'_>,
    operation: &RetainedOperation<'_>,
    wire: &WireLimits,
    control: &mut Control<'_>,
) -> Result<(), ProofCheckError> {
    control.charge(1, 0)?;
    if credits.ordinary_count() > MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
        return Err(ProofCheckError::ResourceLimit);
    }
    let RetainedOperation::Replay(payloads) = operation else {
        return Ok(());
    };
    if payloads.len() != credits.ordinary_count() {
        return Err(invalid(
            ProofId(0),
            "retained payload inventory is incomplete or excessive",
        ));
    }
    for (id, payload) in credits.ordinary_ids().zip(payloads.iter()) {
        control.charge(1, 0)?;
        if id.0 != payload.step {
            return Err(invalid(
                id,
                "retained payload IDs do not match source order",
            ));
        }
        // Account the actual backing owner, not only its borrowed used slice.
        // Its reservation is already part of the held per-lemma prepayment.
        if payload.payload.len() > wire.max_json_bytes
            || payload.payload.capacity() > wire.max_storage_bytes
        {
            return Err(ProofCheckError::ResourceLimit);
        }
    }
    Ok(())
}

pub(super) fn output(
    operation: &RetainedOperation<'_>,
    control: &mut Control<'_>,
) -> Result<Vec<RetainedStepPayload>, ProofCheckError> {
    let mut output = Vec::new();
    if matches!(operation, RetainedOperation::Capture) {
        let bytes = size_of::<RetainedStepPayload>()
            .checked_mul(MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF)
            .and_then(|slots| slots.checked_add(size_of::<Vec<RetainedStepPayload>>()))
            .ok_or(ProofCheckError::ResourceLimit)?;
        control.charge(MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF, bytes)?;
        output
            .try_reserve_exact(MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        if output.capacity() > MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
            return Err(ProofCheckError::ResourceLimit);
        }
        control.poll()?;
    }
    Ok(output)
}
