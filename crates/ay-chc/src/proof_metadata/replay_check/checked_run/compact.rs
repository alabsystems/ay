// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcValidatedCompactGroundDerivation;

impl SealedReplayObligationPayload {
    pub(in crate::proof_metadata::replay_check) fn try_new_compact_ground_derivation(
        obligation: &ChcCheckedReplayObligation,
        validated: &ChcValidatedCompactGroundDerivation,
        artifact_bytes: Vec<u8>,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcResult<Self> {
        poll_payload_progress(progress)?;
        if obligation.payload_format != ChcReplayPayloadFormat::CompactGroundDerivationV1
            || validated.artifact_schema() != crate::CHC_COMPACT_GROUND_DERIVATION_SCHEMA
            || validated.artifact_role() != obligation.query.role
            || validated.artifact_sha256() != obligation.query.sha256
            || u64::try_from(validated.artifact_bytes()).ok() != Some(obligation.query.bytes)
        {
            return Err(verification_error(
                "compact ground capability descriptor mismatch",
            ));
        }
        let payload = Self::GroundDerivation {
            obligation_identity_sha256: obligation.identity_sha256(),
            artifact_bytes,
        };
        payload.validate_with_progress(obligation, progress)?;
        poll_payload_progress(progress)?;
        Ok(payload)
    }
}

pub(super) fn recheck(
    problem: &crate::ChcProblem,
    obligation: &ChcCheckedReplayObligation,
    artifact_bytes: &[u8],
    control: FreshRecheckControl<'_>,
    now: &mut dyn FnMut() -> Instant,
) -> ChcResult<()> {
    if obligation.payload_format != ChcReplayPayloadFormat::CompactGroundDerivationV1
        || obligation.kind != ChcReplayObligationKind::TraceValidity
        || obligation.strict_cert.is_some()
    {
        return Err(verification_error("invalid compact ground recheck row"));
    }
    let checked = crate::validate_chc_compact_ground_derivation_artifact_with_progress(
        problem,
        artifact_bytes,
        &mut || control.allows(now),
    )
    .map_err(|error| verification_error(format!("compact ground recheck: {error}")))?;
    drop(checked);
    // Include destruction before accepting the original whole-recheck owner.
    if !control.allows(now) {
        return Err(verification_error(
            "compact ground recheck stopped during cleanup",
        ));
    }
    Ok(())
}
