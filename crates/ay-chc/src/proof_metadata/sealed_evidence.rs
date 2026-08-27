// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only views over solver-owned CHC evidence containers.

use super::*;

/// Immutable transcript metadata access.
///
/// Metadata is intentionally not caller-editable:
///
/// ```compile_fail
/// use ay_chc::ChcProofTranscriptMetadata;
///
/// fn relabel(metadata: &mut ChcProofTranscriptMetadata) {
///     metadata.engine = "different-engine".to_string();
/// }
/// ```
impl ChcProofTranscriptMetadata {
    /// Return the transcript metadata schema.
    pub fn schema(&self) -> &'static str {
        self.schema
    }

    /// Return the normalized-input schema.
    pub fn normalized_input_schema(&self) -> &'static str {
        self.normalized_input_schema
    }

    /// Return the normalized-input SHA-256 digest.
    pub fn normalized_input_sha256(&self) -> &str {
        &self.normalized_input_sha256
    }

    /// Alias used by PDR replay consumers for the normalized-input digest.
    pub fn pdr_input_sha256(&self) -> &str {
        self.normalized_input_sha256()
    }

    /// Return the normalized-input byte length.
    pub fn normalized_input_bytes(&self) -> u64 {
        self.normalized_input_bytes
    }

    /// Return the solving engine family.
    pub fn engine(&self) -> &str {
        &self.engine
    }

    /// Return the semantic result code.
    pub fn result(&self) -> &str {
        &self.result
    }

    /// Return the proof classification.
    pub fn proof_status(&self) -> &str {
        &self.proof_status
    }

    /// Return whether the solver result is proof-grade Safe/Unsafe evidence.
    pub fn accepted_as_proof(&self) -> bool {
        self.accepted_as_proof
    }

    /// Return the replay material classification.
    pub fn replay_status(&self) -> &str {
        &self.replay_status
    }

    /// Return the transcript material classification.
    pub fn transcript_status(&self) -> &str {
        &self.transcript_status
    }

    /// Whether this transcript can be admitted to the Trust full verifier.
    ///
    /// This derives fail-closed from the private checked-replay digest set.
    /// JSON parsing never populates that set, so a deserialized copy is never
    /// admissible even when its reporting flag says otherwise.
    pub fn trust_full_verifier_admissible(&self) -> bool {
        self.checked_replay.is_some()
    }

    /// Return the structured non-admission reason, when present.
    pub fn trust_full_verifier_non_admission_reason(&self) -> Option<&str> {
        self.trust_full_verifier_non_admission_reason.as_deref()
    }

    /// Return the structured Unknown reason, when present.
    pub fn unknown_reason(&self) -> Option<&str> {
        self.unknown_reason.as_deref()
    }

    /// Return the checked solver-transcript URI, when this is a live checked run.
    pub fn checked_transcript_uri(&self) -> Option<&str> {
        self.checked_replay
            .as_ref()
            .map(|checked| checked.transcript_uri.as_str())
    }

    /// Return the checked solver-transcript digest, when present.
    pub fn checked_transcript_sha256(&self) -> Option<&str> {
        self.checked_replay
            .as_ref()
            .map(|checked| checked.transcript_sha256.as_str())
    }

    /// Return the checked replay-log digest, when present.
    pub fn checked_replay_log_sha256(&self) -> Option<&str> {
        self.checked_replay
            .as_ref()
            .map(|checked| checked.replay_log_sha256.as_str())
    }

    /// Return the checked-report digest, when present.
    pub fn checked_report_sha256(&self) -> Option<&str> {
        self.checked_replay
            .as_ref()
            .map(|checked| checked.checked_report_sha256.as_str())
    }

    /// Return the checked replay summary identity, when present.
    pub fn checked_summary_identity_sha256(&self) -> Option<&str> {
        self.checked_replay
            .as_ref()
            .map(|checked| checked.summary_identity_sha256.as_str())
    }
}

/// Immutable consumer-evidence access.
///
/// Consumer evidence is a projection of a sealed proof run and cannot be
/// relabeled by downstream callers:
///
/// ```compile_fail
/// use ay_chc::ChcProofTranscriptConsumerEvidence;
///
/// fn relabel(evidence: &mut ChcProofTranscriptConsumerEvidence) {
///     evidence.verdict = "safe".to_string();
/// }
/// ```
impl ChcProofTranscriptConsumerEvidence {
    /// Return the consumer-evidence schema.
    pub fn schema(&self) -> &'static str {
        self.schema
    }

    /// Return the consumer-evidence schema version.
    pub fn schema_version(&self) -> u64 {
        self.schema_version
    }

    /// Return the human-readable verdict.
    pub fn verdict(&self) -> &str {
        &self.verdict
    }

    /// Return the stable verdict code.
    pub fn verdict_code(&self) -> &str {
        &self.verdict_code
    }

    /// Return the normalized query identity.
    pub fn query_id(&self) -> &str {
        &self.query_id
    }

    /// Return the false-head query clause index, when present.
    pub fn query_clause_index(&self) -> Option<u64> {
        self.query_clause_index
    }

    /// Return the property identity.
    pub fn property_id(&self) -> &str {
        &self.property_id
    }

    /// Return the property identity digest.
    pub fn property_sha256(&self) -> &str {
        &self.property_sha256
    }

    /// Return the solving engine family.
    pub fn engine(&self) -> &str {
        &self.engine
    }

    /// Return the stable backend code.
    pub fn backend_code(&self) -> &str {
        &self.backend_code
    }

    /// Return the normalized-input schema.
    pub fn normalized_input_schema(&self) -> &'static str {
        self.normalized_input_schema
    }

    /// Return the normalized-input digest.
    pub fn normalized_input_sha256(&self) -> &str {
        &self.normalized_input_sha256
    }

    /// Return the normalized-input byte length.
    pub fn normalized_input_bytes(&self) -> u64 {
        self.normalized_input_bytes
    }

    /// Return the proof classification.
    pub fn proof_status(&self) -> &str {
        &self.proof_status
    }

    /// Return whether this evidence is accepted by proof consumers.
    pub fn accepted_for_consumer(&self) -> bool {
        self.accepted_for_consumer
    }

    /// Return the consumer rejection code, when present.
    pub fn consumer_rejection_code(&self) -> Option<&str> {
        self.consumer_rejection_code.as_deref()
    }

    /// Return whether the result model was validated by AY.
    pub fn model_validated(&self) -> bool {
        self.model_validated
    }

    /// Return the model-validation status.
    pub fn model_validation_status(&self) -> &str {
        &self.model_validation_status
    }

    /// Return the verification-level code.
    pub fn verification_level_code(&self) -> &str {
        &self.verification_level_code
    }

    /// Return the Trust admission status code.
    pub fn trust_status(&self) -> &str {
        &self.trust_status
    }

    /// Return whether checked replay makes this evidence Trust-admissible.
    pub fn trust_full_verifier_admissible(&self) -> bool {
        self.trust_full_verifier_admissible
    }

    /// Return the Trust non-admission reason, when present.
    pub fn trust_full_verifier_non_admission_reason(&self) -> Option<&str> {
        self.trust_full_verifier_non_admission_reason.as_deref()
    }

    /// Return the replay material classification.
    pub fn replay_status(&self) -> &str {
        &self.replay_status
    }

    /// Return the transcript material classification.
    pub fn transcript_status(&self) -> &str {
        &self.transcript_status
    }

    /// Return the structured Unknown reason code, when present.
    pub fn unknown_reason_code(&self) -> Option<&str> {
        self.unknown_reason_code.as_deref()
    }

    /// Return the structured resource-limit code, when present.
    pub fn unknown_limit_code(&self) -> Option<&str> {
        self.unknown_limit_code.as_deref()
    }

    /// Return the deepest reached BMC depth, when present.
    pub fn unknown_depth_reached(&self) -> Option<u64> {
        self.unknown_depth_reached
    }

    /// Return the configured BMC depth limit, when present.
    pub fn unknown_depth_limit(&self) -> Option<u64> {
        self.unknown_depth_limit
    }

    /// Return the validated unsafe trace, when this is unsafe evidence.
    pub fn unsafe_trace(&self) -> Option<&ChcUnsafeTraceEvidence> {
        self.unsafe_trace.as_ref()
    }
}

/// Immutable proof-run artifact access.
///
/// ```compile_fail
/// use ay_chc::ChcProofRunArtifact;
///
/// fn relabel(artifact: &mut ChcProofRunArtifact) {
///     artifact.role = "different-role";
/// }
/// ```
impl ChcProofRunArtifact {
    /// Return the payload schema.
    pub fn schema(&self) -> &'static str {
        self.schema
    }

    /// Return the artifact role.
    pub fn role(&self) -> &'static str {
        self.role
    }

    /// Return the content-addressed digest descriptor.
    pub fn digest(&self) -> &ChcProofArtifactDigest {
        &self.digest
    }

    /// Return the concrete artifact bytes emitted by `ay-chc`.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Return the lowercase SHA-256 digest of the artifact bytes.
    pub fn sha256(&self) -> &str {
        &self.digest.sha256
    }

    /// Return the artifact byte length.
    pub fn byte_len(&self) -> u64 {
        self.digest.bytes
    }
}

/// Immutable access to a proof run's atomic artifact bundle.
///
/// ```compile_fail
/// use ay_chc::{ChcProofRunArtifact, ChcProofRunArtifacts};
///
/// fn replace(bundle: &mut ChcProofRunArtifacts, artifact: ChcProofRunArtifact) {
///     bundle.model = artifact;
/// }
/// ```
impl ChcProofRunArtifacts {
    /// Return the model/counterexample validation artifact.
    pub fn model(&self) -> &ChcProofRunArtifact {
        &self.model
    }

    /// Return the replayable quantifier-free invariant, when present.
    pub fn quantifier_free_invariant_model(&self) -> Option<&ChcProofRunArtifact> {
        self.quantifier_free_invariant_model.as_ref()
    }

    /// Return the replay transcript artifact.
    pub fn replay_transcript(&self) -> &ChcProofRunArtifact {
        &self.replay_transcript
    }

    /// Return the model/counterexample validation artifact bytes.
    pub fn model_bytes(&self) -> &[u8] {
        self.model.bytes()
    }

    /// Return the replayable quantifier-free invariant bytes, when present.
    pub fn quantifier_free_invariant_model_bytes(&self) -> Option<&[u8]> {
        self.quantifier_free_invariant_model
            .as_ref()
            .map(ChcProofRunArtifact::bytes)
    }

    /// Return the replay transcript artifact bytes.
    pub fn replay_transcript_bytes(&self) -> &[u8] {
        self.replay_transcript.bytes()
    }
}
