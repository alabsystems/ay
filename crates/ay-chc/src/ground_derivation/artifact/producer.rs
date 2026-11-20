// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperatively export ground evidence under one call-local cancellation state.
//!
//! Source walks, typed encoding, JSON output, independent consumer replay and
//! final digest sealing share the same sticky control. This does not bound
//! wall-clock latency: individual sorts, normalization/sorting, numeric
//! arithmetic/formatting, serde internals, allocations and destructors remain
//! opaque between polls. No authority or partial artifact is returned on refusal.

use super::*;
/// The source's normalized-input schema and hash, and its clause-sequence hash.
type SourceHashes = (&'static str, String, String);

fn source_hashes(
    problem: &ChcProblem,
    mut budget: Option<usize>,
    control: &mut GroundValidationControl<'_>,
) -> Result<SourceHashes, ChcGroundDerivationArtifactError> {
    let (schema, normalized) = rebuild::normalized_source(problem, &mut budget, control)?;
    let ordered = rebuild::ordered_source(problem, &mut budget, control)?;
    control.poll().map_err(interruption_error)?;
    Ok((schema, normalized, ordered))
}

fn seal(
    schema: &'static str,
    role: &'static str,
    bytes: Vec<u8>,
    control: &mut GroundValidationControl<'_>,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    let artifact =
        ChcProofRunArtifact::new_with_progress(schema, role, bytes, &mut || control.poll().is_ok())
            .map_err(|_| interruption_error(GroundValidationInterrupted))?;
    control.poll().map_err(interruption_error)?;
    Ok(artifact)
}

pub(super) fn encode_v1_with_control(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &mut GroundValidationControl<'_>,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let budget = validate_wire_problem(problem, control)?;
    // V1 must classify strict wire errors before native proof errors, just as
    // the legacy exporter did (notably opaque/private/mis-sorted bindings).
    let (steps, counts) = wire_steps_from_derivation_with_control(problem, derivation, control)?;
    let (schema, normalized, ordered) = source_hashes(problem, budget, control)?;
    let envelope = GroundDerivationEnvelope::from_parts(
        steps,
        counts,
        derivation.query_step,
        schema,
        normalized,
        ordered,
    )?;
    let checked = validate_ground_derivation_with_control(problem, derivation, control);
    control.poll().map_err(interruption_error)?;
    checked.map_err(map_derivation_error)?;
    let bytes = transport::serialize_envelope(&envelope, control)?;
    drop(envelope);
    control.poll().map_err(interruption_error)?;
    let checked = validate_ground_artifact_with_control(problem, &bytes, control)?;
    drop(checked);
    control.poll().map_err(interruption_error)?;
    seal(
        CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA,
        CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
        bytes,
        control,
    )
}

pub(super) fn encode_v2_with_control(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &mut GroundValidationControl<'_>,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let budget = validate_wire_problem(problem, control)?;
    // V2 authenticates native types/resources before wire encoding can
    // evaluate ordinary UF arguments or clone their observed values.
    let checked = validate_ground_derivation_with_control(problem, derivation, control);
    control.poll().map_err(interruption_error)?;
    checked.map_err(map_v2_derivation_error)?;
    let (steps, counts) = wire_steps_v2_from_derivation_with_control(problem, derivation, control)?;
    let (schema, normalized, ordered) = source_hashes(problem, budget, control)?;
    let envelope = GroundDerivationEnvelopeV2::from_parts(
        steps,
        counts,
        derivation.query_step,
        schema,
        normalized,
        ordered,
    )?;
    let bytes = transport::serialize_envelope(&envelope, control)?;
    drop(envelope);
    control.poll().map_err(interruption_error)?;
    let checked = validate_ground_artifact_v2_with_control(problem, &bytes, control)?;
    drop(checked);
    control.poll().map_err(interruption_error)?;
    seal(
        CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
        CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
        bytes,
        control,
    )
}

fn counterexample_derivation<'a>(
    counterexample: &'a Counterexample,
    control: &mut GroundValidationControl<'_>,
) -> Result<&'a GroundDerivation, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    counterexample.ground_derivation.as_ref().ok_or_else(|| {
        error(
            ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation,
            "counterexample carries no fully-ground derivation",
        )
    })
}

impl Counterexample {
    /// Export canonical v1 ground evidence with cooperative cancellation.
    ///
    /// Returning `false` from `progress` permanently interrupts this call with
    /// [`ChcGroundDerivationArtifactErrorReason::Interrupted`], including before
    /// checking whether evidence is present. No partial artifact is returned.
    /// Source checks, wire encoding, JSON, independent replay and digest sealing
    /// share one control; there is no retry or automatic format fallback.
    ///
    /// Individual sorts, sorting/normalization, arithmetic/formatting, serde
    /// internals, allocation and destruction remain opaque between polls. This
    /// is not a hard deadline or a 100 ms cancellation-latency guarantee.
    pub fn ground_derivation_artifact_with_progress(
        &self,
        problem: &ChcProblem,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        let mut control = GroundValidationControl::new(progress);
        let derivation = counterexample_derivation(self, &mut control)?;
        encode_v1_with_control(problem, derivation, &mut control)
    }

    /// Export canonical source-authenticated finite-UF evidence with cancellation.
    ///
    /// Uses the same sticky, cooperative contract and opaque-interval limits as
    /// [`Self::ground_derivation_artifact_with_progress`], but preserves v2's
    /// native-validation-before-wire-encoding order. No v1 retry is attempted.
    pub fn ground_derivation_artifact_v2_with_progress(
        &self,
        problem: &ChcProblem,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        let mut control = GroundValidationControl::new(progress);
        let derivation = counterexample_derivation(self, &mut control)?;
        encode_v2_with_control(problem, derivation, &mut control)
    }
}

impl ChcPdrProofRun {
    /// Export deciding v1 Unsafe bytes with typed cooperative interruption.
    ///
    /// Safe/Unknown runs or absent ground evidence return `Ok(None)` only after
    /// entry and completion polls. Present but invalid evidence is an error,
    /// not absence. Interruption is terminal, not a reason to try v2 or SMT.
    /// See [`Counterexample::ground_derivation_artifact_with_progress`] for
    /// the shared-control contract and remaining opaque-interval limitations.
    pub fn unsafe_ground_derivation_artifact_bytes_with_progress(
        &self,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Option<Vec<u8>>, ChcGroundDerivationArtifactError> {
        let mut control = GroundValidationControl::new(progress);
        control.poll().map_err(interruption_error)?;
        let bytes = if let VerifiedChcResult::Unsafe(verified) = self.result() {
            match counterexample_derivation(verified.counterexample(), &mut control) {
                Ok(derivation) => Some(
                    encode_v1_with_control(self.problem(), derivation, &mut control)?.into_bytes(),
                ),
                Err(error)
                    if error.reason
                        == ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation =>
                {
                    None
                }
                Err(error) => return Err(error),
            }
        } else {
            None
        };
        control.poll().map_err(interruption_error)?;
        Ok(bytes)
    }

    /// Export deciding v2 Unsafe bytes with typed cooperative interruption.
    ///
    /// This has the same absence, sticky-refusal and opaque-interval contract
    /// as [`Self::unsafe_ground_derivation_artifact_bytes_with_progress`], with
    /// source-authenticated finite-UF evidence and no automatic format fallback.
    pub fn unsafe_ground_derivation_artifact_v2_bytes_with_progress(
        &self,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Option<Vec<u8>>, ChcGroundDerivationArtifactError> {
        let mut control = GroundValidationControl::new(progress);
        control.poll().map_err(interruption_error)?;
        let bytes = if let VerifiedChcResult::Unsafe(verified) = self.result() {
            match counterexample_derivation(verified.counterexample(), &mut control) {
                Ok(derivation) => Some(
                    encode_v2_with_control(self.problem(), derivation, &mut control)?.into_bytes(),
                ),
                Err(error)
                    if error.reason
                        == ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation =>
                {
                    None
                }
                Err(error) => return Err(error),
            }
        } else {
            None
        };
        control.poll().map_err(interruption_error)?;
        Ok(bytes)
    }
}

#[cfg(test)]
mod tests;
