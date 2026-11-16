// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-bound compact evidence. Wired as a child of `artifact` so the
//! existing canonical transport and identity authentication remain authoritative.
//! Deserialization is never validation; every input runs the original-clause
//! compact checker. No expanded `SmtValue` or legacy tree-priced replay is used.

use super::{
    error, interruption_error, rebuild::AuthenticatedSource, transport,
    ChcGroundDerivationArtifactError, ChcGroundDerivationArtifactErrorReason as Reason,
    GroundValidationControl, CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES,
};
use crate::ground_derivation::compact::{self, CompactDerivation, Error as CompactError, Owner};
use crate::{ChcProblem, ChcProofRunArtifact};

#[path = "compact_artifact/decode.rs"]
mod decode;
#[path = "compact_artifact/producer.rs"]
mod producer;
#[path = "compact_artifact/source.rs"]
mod source;
#[path = "compact_artifact/view.rs"]
mod view;
#[path = "compact_artifact/wire.rs"]
mod wire;

pub use view::{ChcCompactGroundStepView, ChcCompactValueId, ChcCompactValueView};

/// A distinct format: DAG child indices are not legacy recursive value fields.
pub const CHC_COMPACT_GROUND_DERIVATION_SCHEMA: &str = "ay.chc-compact-ground-derivation/v1";
/// Deciding original-source Unsafe evidence, not a model or unchecked trace.
pub const CHC_COMPACT_GROUND_DERIVATION_ROLE: &str = "unsafe-compact-ground-derivation";

type Result<T> = std::result::Result<T, ChcGroundDerivationArtifactError>;

/// Opaque result of fresh source-bound replay. No deserialize or public constructor.
#[derive(Debug)]
#[must_use = "compact evidence is bound to its authenticated original source"]
pub struct ChcValidatedCompactGroundDerivation {
    derivation: CompactDerivation,
    artifact_sha256: String,
    artifact_bytes: usize,
    normalized_input_schema: String,
    normalized_input_sha256: String,
    source_clause_sequence_sha256: String,
}

fn native_error(failure: CompactError) -> ChcGroundDerivationArtifactError {
    let reason = match failure {
        CompactError::Stopped => Reason::Interrupted,
        CompactError::Resource => Reason::SourceWorkLimitExceeded,
        CompactError::InvalidSource => Reason::InvalidSourceProblem,
        CompactError::InvalidValue => Reason::InvalidValue,
        CompactError::InvalidDerivation | CompactError::Unsupported => Reason::DerivationRejected,
    };
    error(
        reason,
        format!("compact ground evidence refused: {failure:?}"),
    )
}

fn admit(owner: &mut Owner<'_>, work: usize, bytes: usize) -> Result<()> {
    owner.admit(work, bytes).map_err(native_error)
}

fn refused<T>(owner: &mut Owner<'_>) -> Result<T> {
    owner.refuse(CompactError::Resource).map_err(native_error)
}

/// Existing byte transport borrows this owner; it never captures a new grant.
fn controlled<T>(
    owner: &mut Owner<'_>,
    body: impl FnOnce(&mut GroundValidationControl<'_>) -> Result<T>,
) -> Result<T> {
    let result = {
        let mut progress = || owner.admit(1, 0).is_ok();
        let mut control = GroundValidationControl::new(&mut progress);
        let result = body(&mut control);
        match control.poll().map_err(interruption_error) {
            Ok(()) => result,
            Err(stopped) => Err(stopped),
        }
    };
    owner.poll().map_err(native_error)?;
    result
}

/// Decode bounded canonical bytes and freshly decide every original clause.
/// Captures existing callback/Guard/deadline/memory authority, never a new grant.
/// Opaque serde and source-normalization intervals are not a hard latency claim.
pub fn validate_chc_compact_ground_derivation_artifact(
    problem: &ChcProblem,
    bytes: &[u8],
) -> Result<ChcValidatedCompactGroundDerivation> {
    validate_chc_compact_ground_derivation_artifact_with_progress(problem, bytes, &mut || true)
}

/// Fresh source-bound replay with one sticky, borrowed continuation callback.
///
/// A false callback or panic refuses this invocation. Original ambient controls
/// and every controlled decoding/replay debit also remain in force. Individual
/// numeric, serde, normalization and allocator operations remain opaque; this
/// is not an asynchronous interruption or hard return-latency guarantee.
pub fn validate_chc_compact_ground_derivation_artifact_with_progress(
    problem: &ChcProblem,
    bytes: &[u8],
    progress: &mut dyn FnMut() -> bool,
) -> Result<ChcValidatedCompactGroundDerivation> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let owner = Owner::capture().map_err(native_error)?;
        let mut continuation = owner.with_progress(progress);
        let result = validate_with_owner(problem, bytes, &mut continuation);
        // The decoder's envelope, scratch storage and temporary scopes have
        // now been destroyed. Refuse a stop during that cleanup before giving
        // the caller a source-bound validated capability.
        continuation.poll().map_err(native_error)?;
        result
    }))
    .unwrap_or_else(|_| Err(native_error(CompactError::Stopped)))
}

pub(crate) fn validate_with_owner(
    problem: &ChcProblem,
    bytes: &[u8],
    owner: &mut Owner<'_>,
) -> Result<ChcValidatedCompactGroundDerivation> {
    let _scope = owner.enter();
    owner.poll().map_err(native_error)?;
    if bytes.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES {
        return Err(error(
            Reason::ArtifactTooLarge,
            "compact artifact exceeds byte bound",
        ));
    }
    // Price both serde's flat envelope and rebuilding before either allocates.
    // This is a conservative logical allocation envelope, not process RSS.
    let Some(storage) = bytes.len().checked_mul(64) else {
        return refused(owner);
    };
    let Some(work) = bytes.len().checked_mul(8) else {
        return refused(owner);
    };
    admit(owner, work, storage)?;
    let envelope: wire::Envelope = controlled(owner, |control| {
        transport::validate_json_surface(bytes, control)?;
        let envelope = transport::parse_envelope(bytes, control)?;
        transport::check_canonical_json(
            &envelope,
            bytes,
            "noncanonical compact evidence",
            control,
        )?;
        Ok(envelope)
    })?;
    envelope.check_header(owner)?;
    source::admit_identity(problem, owner)?;
    controlled(owner, |control| {
        AuthenticatedSource::check(
            problem,
            &envelope.normalized_input_schema,
            &envelope.normalized_input_sha256,
            &envelope.source_clause_sequence_sha256,
            "compact artifact",
            control,
        )
        .map(|_| ())
    })?;
    let derivation = decode::derivation(&envelope, owner)?;
    compact::validate(problem, &derivation, owner).map_err(native_error)?;
    let digest = controlled(owner, |control| transport::sha256_hex(bytes, control))?;
    let validated = ChcValidatedCompactGroundDerivation {
        derivation,
        artifact_sha256: digest,
        artifact_bytes: bytes.len(),
        normalized_input_schema: envelope.normalized_input_schema,
        normalized_input_sha256: envelope.normalized_input_sha256,
        source_clause_sequence_sha256: envelope.source_clause_sequence_sha256,
    };
    owner.poll().map_err(native_error)?;
    Ok(validated)
}

/// Producer continuation: original owner spans fresh replay, construction,
/// canonical output, independent decoding/replay, and final digest sealing.
pub(crate) fn encode_with_owner(
    problem: &ChcProblem,
    derivation: &CompactDerivation,
    owner: &mut Owner<'_>,
) -> Result<ChcProofRunArtifact> {
    let _scope = owner.enter();
    compact::validate(problem, derivation, owner).map_err(native_error)?;
    let identity = source::hashes(problem, owner)?;
    let envelope = wire::Envelope::from_derivation(derivation, identity, owner)?;
    let bytes = controlled(owner, |control| {
        transport::serialize_envelope(&envelope, control)
    })?;
    drop(envelope);
    let checked = validate_with_owner(problem, &bytes, owner)?;
    drop(checked);
    let artifact = controlled(owner, |control| {
        ChcProofRunArtifact::new_with_progress(
            CHC_COMPACT_GROUND_DERIVATION_SCHEMA,
            CHC_COMPACT_GROUND_DERIVATION_ROLE,
            bytes,
            &mut || control.poll().is_ok(),
        )
        .map_err(|_| interruption_error(super::GroundValidationInterrupted))
    })?;
    owner.poll().map_err(native_error)?;
    Ok(artifact)
}

#[cfg(test)]
#[path = "compact_artifact/tests.rs"]
mod tests;
