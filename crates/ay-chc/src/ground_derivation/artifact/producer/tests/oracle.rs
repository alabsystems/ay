// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Pre-progress producer orchestration, retained only as a compatibility oracle.
//! The unchanged parent envelope wrappers use the separately tested legacy
//! codec/hash entry points. Oversize diagnostics intentionally differ now that
//! output stops at the byte cap instead of computing an unbounded full length.

use super::*;

fn bytes<T: Serialize>(envelope: &T) -> Result<Vec<u8>, ChcGroundDerivationArtifactError> {
    let bytes = serde_json::to_vec(envelope).map_err(|serialization_error| {
        error(
            ChcGroundDerivationArtifactErrorReason::SerializationFailed,
            serialization_error.to_string(),
        )
    })?;
    if bytes.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::ArtifactTooLarge,
            format!(
                "artifact has {} bytes, maximum is {}",
                bytes.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES,
            ),
        ));
    }
    Ok(bytes)
}

pub(super) fn encode_v1(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    validate_problem_bounds(problem)?;
    let envelope = envelope_for_derivation(problem, derivation)?;
    validate_ground_derivation(problem, derivation).map_err(map_derivation_error)?;
    let bytes = bytes(&envelope)?;
    let _validated = validate_chc_ground_derivation_artifact(problem, &bytes)?;
    Ok(ChcProofRunArtifact::new(
        CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA,
        CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
        bytes,
    ))
}

pub(super) fn encode_v2(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    validate_problem_bounds(problem)?;
    validate_ground_derivation(problem, derivation).map_err(map_v2_derivation_error)?;
    let envelope = envelope_v2_for_derivation(problem, derivation)?;
    let bytes = bytes(&envelope)?;
    let _validated = validate_chc_ground_derivation_artifact_v2(problem, &bytes)?;
    Ok(ChcProofRunArtifact::new(
        CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
        CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
        bytes,
    ))
}
