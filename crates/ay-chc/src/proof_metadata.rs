// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deterministic CHC proof/transcript metadata for replay consumers.

use crate::pdr::{ChcReplayObligationKind, PdrConfig};
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, HornClause, PredicateId, VerifiedChcResult,
    VerifiedUnknownReason,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

/// Schema tag for normalized CHC/PDR replay input material.
pub const NORMALIZED_CHC_INPUT_SCHEMA: &str = "ay.chc.normalized-input/v1";

/// Schema tag for CHC proof/transcript metadata.
pub const CHC_PROOF_TRANSCRIPT_SCHEMA: &str = "ay.chc-proof-transcript/v1";

/// Schema tag for consumer-facing CHC proof/transcript evidence rows.
pub const CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA: &str =
    "ay.chc-proof-transcript-consumer-evidence/v1";

/// Schema tag for the CHC BMC unsafe trace assignment evidence contract.
pub const CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA: &str =
    "ay.chc-bmc-unsafe-trace-assignment-contract/v1";

/// Schema tag for BMC unsafe trace assignment completeness reports.
pub const CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA: &str =
    "ay.chc-bmc-unsafe-trace-assignment-completeness/v1";

/// Schema tag for compiler-facing CHC evidence manifests.
pub const CHC_EVIDENCE_MANIFEST_SCHEMA: &str = "ay.chc-evidence-manifest/v1";

/// Schema tag for proof-query cache/admission keys.
pub const CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA: &str = "ay.chc-proof-query-admission-key/v1";

/// Schema tag for durable proof-query cache lookup keys.
pub const CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA: &str = "ay.chc-proof-query-cache-lookup-key/v1";

/// Schema tag for proof-query cache admission policies.
pub const CHC_PROOF_QUERY_CACHE_ADMISSION_POLICY_SCHEMA: &str =
    "ay.chc-proof-query-cache-admission-policy/v1";

/// Schema tag for proof-query cache admission decisions.
pub const CHC_PROOF_QUERY_CACHE_ADMISSION_DECISION_SCHEMA: &str =
    "ay.chc-proof-query-cache-admission-decision/v1";

/// Schema tag for bounded proof-query cache stores.
pub const CHC_PROOF_QUERY_CACHE_SCHEMA: &str = "ay.chc-proof-query-cache/v1";

/// Schema tag for proof-query cache lookup results.
pub const CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA: &str =
    "ay.chc-proof-query-cache-lookup-result/v1";

/// Schema tag for proof-query cache metrics.
pub const CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA: &str = "ay.chc-proof-query-cache-metrics/v1";

/// Schema tag for digest descriptors over CHC/PDR replay artifacts.
pub const CHC_PROOF_ARTIFACT_DIGEST_SCHEMA: &str = "ay.chc-proof-artifact-digest/v1";

/// Schema tag for first-class CHC proof-run model artifacts.
pub const CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA: &str = "ay.chc-proof-run-model-artifact/v1";

/// Schema tag for first-class CHC proof-run replay transcript artifacts.
pub const CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA: &str =
    "ay.chc-proof-run-replay-transcript-artifact/v1";

/// Artifact role for CHC proof-run model validation material.
pub const CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE: &str = "model-validation";

/// Artifact role for CHC proof-run replay transcript material.
pub const CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE: &str = "replay-transcript";

/// Schema tag for caller-supplied CHC/PDR replay evidence bindings.
pub const CHC_REPLAY_EVIDENCE_SCHEMA: &str = "ay.chc-replay-evidence/v1";

/// Schema tag used by native CHC certificate replay summaries.
pub const CHC_CHECKED_REPLAY_SUMMARY_SCHEMA: &str = "ay-chc-certificate-replay/v1";

/// Schema tag for checked replay checker identity rows.
pub(crate) const CHC_REPLAY_CHECKER_IDENTITY_SCHEMA: &str = "ay.chc-replay-checker-identity/v1";

/// Schema tag for checked replay command result rows.
pub(crate) const CHC_REPLAY_CHECK_RESULT_SCHEMA: &str = "ay.chc-replay-check-result/v1";

mod strict_cert;
pub use strict_cert::ChcObligationStrictCert;

/// Schema tag for binding a checked replay summary to one evidence manifest.
pub const CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA: &str =
    "ay.chc-checked-replay-manifest-binding/v1";

/// Checker name reserved for ay's own in-process checked-replay pass.
///
/// The summary validator accepts `checker.external == false` ONLY for this
/// checker identity: it re-executes every digest-bound obligation query on a
/// fresh SMT context independent of the solving run, which is the same
/// discharge power an external `ay` process would apply.
pub const CHC_IN_PROCESS_REPLAY_CHECKER_NAME: &str = "ay-chc-replay";

/// Content digest for one concrete CHC/PDR replay artifact.
///
/// The path is intentionally not part of the stable identity: model-checker-consumer/CertificateConsumer/VerifierConsumer
/// can relocate packaged artifacts without invalidating a cache key as long as
/// the bytes and role are unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofArtifactDigest {
    /// Artifact descriptor schema identifier.
    pub schema: &'static str,
    /// Artifact role, for example `solver-transcript` or `proof-certificate`.
    pub role: String,
    /// SHA-256 of the artifact bytes, lowercase hex.
    pub sha256: String,
    /// Artifact byte length.
    pub bytes: u64,
    /// Optional packaging path for humans and downstream copy plans.
    pub path: Option<String>,
}

impl ChcProofArtifactDigest {
    /// Create an artifact digest by hashing the supplied bytes.
    pub fn from_bytes(role: impl Into<String>, bytes: &[u8]) -> Self {
        Self::from_sha256(role, sha256_hex(bytes), bytes.len() as u64)
    }

    /// Create a replay-log artifact digest by hashing the supplied bytes.
    pub fn replay_log_from_bytes(bytes: &[u8]) -> Self {
        Self::from_bytes("replay-log", bytes)
    }

    /// Create a checked-proof-report artifact digest by hashing the supplied bytes.
    pub fn checked_proof_report_from_bytes(bytes: &[u8]) -> Self {
        Self::from_bytes("checked-proof-report", bytes)
    }

    /// Create an invariant-model artifact digest by hashing the supplied bytes.
    pub fn invariant_model_from_bytes(bytes: &[u8]) -> Self {
        Self::from_bytes("invariant-model", bytes)
    }

    /// Create a counterexample artifact digest by hashing the supplied bytes.
    pub fn counterexample_from_bytes(bytes: &[u8]) -> Self {
        Self::from_bytes("counterexample", bytes)
    }

    /// Create an artifact digest from an already-computed SHA-256.
    pub fn from_sha256(role: impl Into<String>, sha256: impl Into<String>, bytes: u64) -> Self {
        Self {
            schema: CHC_PROOF_ARTIFACT_DIGEST_SCHEMA,
            role: role.into(),
            sha256: sha256.into(),
            bytes,
            path: None,
        }
    }

    /// Attach a packaging path. The path is excluded from cache identity.
    #[must_use]
    pub fn with_path(mut self, path: impl Into<String>) -> Self {
        self.path = Some(path.into());
        self
    }

    /// SHA-256 over the stable artifact identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render this artifact descriptor as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "role": self.role,
            "sha256": self.sha256,
            "bytes": self.bytes,
            "path": self.path,
            "identity_sha256": self.identity_sha256(),
        })
    }

    /// Parse a content-addressed artifact descriptor from JSON and require the
    /// expected artifact role.
    pub fn from_json_value(
        value: &serde_json::Value,
        expected_role: &str,
    ) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let artifact = artifact_from_json_value(value, expected_role, "artifact", &mut reasons);
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(artifact.expect("artifact parsed without reasons"))
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("role={}\n", json_string(&self.role)));
        out.push_str(&format!("sha256={}\n", self.sha256));
        out.push_str(&format!("bytes={}\n", self.bytes));
        out
    }
}

/// Concrete bytes emitted by a sealed CHC proof run for downstream packaging.
///
/// These artifacts are produced by `ay-chc`, not reconstructed by consumers.
/// The payload is a stable schema-bearing envelope whose digest can be bound by
/// ExternalCodegenIr/model-checker-consumer before downstream acceptance.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofRunArtifact {
    /// Artifact payload schema.
    schema: &'static str,
    /// Artifact role.
    role: &'static str,
    /// Content-addressed digest descriptor for the artifact bytes.
    digest: ChcProofArtifactDigest,
    bytes: Vec<u8>,
}

impl ChcProofRunArtifact {
    pub(crate) fn new(schema: &'static str, role: &'static str, bytes: Vec<u8>) -> Self {
        Self {
            schema,
            role,
            digest: ChcProofArtifactDigest::from_bytes(role, &bytes),
            bytes,
        }
    }

    /// Consume this artifact and return its concrete bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

/// Pair of first-class artifacts emitted for a proof-grade CHC run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofRunArtifacts {
    /// Solver-owned model/counterexample validation *metadata* artifact.
    ///
    /// This legacy artifact records consumer status and normalized-input
    /// binding. It is diagnostic metadata, not a serialized invariant and must
    /// never be presented as a replayable PDR model. Safe quantifier-free runs
    /// carry the actual candidate in [`Self::quantifier_free_invariant_model`].
    model: ChcProofRunArtifact,
    /// Canonical, bounded serialization of the actual quantifier-free
    /// invariant, present only for a non-empty, complete Safe model.
    ///
    /// Empty acyclic-BMC certificates, quantified ghost-pair certificates,
    /// Unsafe traces, Unknown results, and any model that fails strict
    /// canonical self-replay leave this field absent.
    quantifier_free_invariant_model: Option<ChcProofRunArtifact>,
    /// Solver-owned replay transcript artifact.
    replay_transcript: ChcProofRunArtifact,
}

/// Reason a supplied pair of proof-run artifacts cannot be accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcProofRunArtifactBundleValidationErrorReason {
    /// The caller did not provide model/counterexample validation artifact bytes.
    MissingModelArtifactBytes,
    /// The caller did not provide replay transcript artifact bytes.
    MissingReplayTranscriptArtifactBytes,
    /// The model/counterexample validation artifact does not match the sealed proof run.
    ModelArtifactMismatch,
    /// The replay transcript artifact does not match the sealed proof run.
    ReplayTranscriptArtifactMismatch,
}

impl ChcProofRunArtifactBundleValidationErrorReason {
    /// Return the stable lower-snake-case reason code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::MissingModelArtifactBytes => "missing_model_artifact_bytes",
            Self::MissingReplayTranscriptArtifactBytes => {
                "missing_replay_transcript_artifact_bytes"
            }
            Self::ModelArtifactMismatch => "model_artifact_mismatch",
            Self::ReplayTranscriptArtifactMismatch => "replay_transcript_artifact_mismatch",
        }
    }
}

/// Typed fail-closed validation error for a model/replay artifact pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcProofRunArtifactBundleValidationError {
    /// Stable bundle validation failure reason.
    pub reason: ChcProofRunArtifactBundleValidationErrorReason,
    /// Stable bundle validation failure reason code.
    pub reason_code: &'static str,
    /// Whether validation remains fail-closed.
    pub fail_closed: bool,
    /// Whether the artifact pair was accepted for downstream consumers.
    pub accepted_for_consumer: bool,
    /// Optional nested artifact validation error.
    pub artifact_error: Option<ChcProofRunArtifactValidationError>,
}

impl ChcProofRunArtifactBundleValidationError {
    fn new(
        reason: ChcProofRunArtifactBundleValidationErrorReason,
        artifact_error: Option<ChcProofRunArtifactValidationError>,
    ) -> Self {
        Self {
            reason,
            reason_code: reason.code(),
            fail_closed: true,
            accepted_for_consumer: false,
            artifact_error,
        }
    }
}

impl std::fmt::Display for ChcProofRunArtifactBundleValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.artifact_error {
            Some(error) => write!(f, "{} ({error})", self.reason_code),
            None => f.write_str(self.reason_code),
        }
    }
}

impl std::error::Error for ChcProofRunArtifactBundleValidationError {}

/// Reason a supplied artifact byte stream does not match a sealed proof run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcProofRunArtifactValidationErrorReason {
    /// The supplied artifact bytes do not match the solver-emitted bytes for this proof run.
    ArtifactDigestMismatch,
}

impl ChcProofRunArtifactValidationErrorReason {
    /// Return the stable lower-snake-case reason code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::ArtifactDigestMismatch => "artifact_digest_mismatch",
        }
    }
}

/// Typed fail-closed validation error for first-class CHC proof-run artifacts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcProofRunArtifactValidationError {
    /// Stable validation failure reason.
    pub reason: ChcProofRunArtifactValidationErrorReason,
    /// Stable validation failure reason code.
    pub reason_code: &'static str,
    /// Artifact role that was being checked.
    pub role: &'static str,
    /// SHA-256 expected from the sealed proof run.
    pub expected_sha256: String,
    /// SHA-256 computed from the supplied artifact bytes.
    pub actual_sha256: String,
}

impl ChcProofRunArtifactValidationError {
    fn digest_mismatch(expected: &ChcProofRunArtifact, actual_bytes: &[u8]) -> Self {
        let reason = ChcProofRunArtifactValidationErrorReason::ArtifactDigestMismatch;
        Self {
            reason,
            reason_code: reason.code(),
            role: expected.role,
            expected_sha256: expected.sha256().to_string(),
            actual_sha256: sha256_hex(actual_bytes),
        }
    }
}

impl std::fmt::Display for ChcProofRunArtifactValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} role={} expected_sha256={} actual_sha256={}",
            self.reason_code, self.role, self.expected_sha256, self.actual_sha256
        )
    }
}

impl std::error::Error for ChcProofRunArtifactValidationError {}

/// Hash-bound replay query paired with the CHC obligation kind it checks.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcReplayObligationArtifact {
    /// Replay obligation kind checked by this query.
    pub kind: ChcReplayObligationKind,
    /// Concrete SMT replay query artifact.
    pub query: ChcProofArtifactDigest,
}

impl ChcReplayObligationArtifact {
    /// Build a replay obligation artifact binding.
    pub fn new(kind: ChcReplayObligationKind, query: ChcProofArtifactDigest) -> Self {
        Self { kind, query }
    }

    /// SHA-256 over the stable obligation artifact identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render as JSON while preserving the flat artifact fields expected by
    /// current CLI consumers.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut value = self.query.to_json_value();
        if let Some(object) = value.as_object_mut() {
            object.insert(
                "kind".to_string(),
                serde_json::Value::String(self.kind.as_str().to_string()),
            );
            object.insert(
                "obligation_identity_sha256".to_string(),
                serde_json::Value::String(self.identity_sha256()),
            );
        }
        value
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str("ay.chc-replay-obligation-artifact/v1\n");
        out.push_str(&format!("kind={}\n", self.kind.as_str()));
        out.push_str(&format!("query={}\n", self.query.identity_sha256()));
        out
    }
}

/// Digest-bearing replay evidence bound to one CHC/PDR proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcReplayEvidence {
    /// Replay evidence schema identifier.
    pub schema: &'static str,
    /// Normalized CHC/PDR problem hash this evidence was produced for.
    pub problem_sha256: String,
    /// Proof/resource option identity hash.
    pub options_sha256: String,
    /// Solver identity hash.
    pub solver_identity_sha256: String,
    /// Caller-stable proof obligation id.
    pub obligation_id: String,
    /// Result this replay material purports to support.
    pub result: String,
    /// Proof status this replay material purports to support.
    pub proof_status: String,
    /// Optional solver transcript artifact.
    pub solver_transcript: Option<ChcProofArtifactDigest>,
    /// Optional proof/certificate artifact.
    pub proof: Option<ChcProofArtifactDigest>,
    /// Optional checked replay report artifact.
    pub replay_report: Option<ChcProofArtifactDigest>,
    /// Optional replay log artifact for downstream verifier packages.
    pub replay_log: Option<ChcProofArtifactDigest>,
    /// Optional checked proof report artifact for downstream verifier packages.
    pub checked_proof_report: Option<ChcProofArtifactDigest>,
    /// Optional safe-result invariant model artifact.
    pub invariant_model: Option<ChcProofArtifactDigest>,
    /// Optional unsafe-result counterexample artifact.
    pub counterexample: Option<ChcProofArtifactDigest>,
    /// Optional per-obligation SMT replay artifacts.
    pub replay_obligations: Vec<ChcReplayObligationArtifact>,
}

impl ChcReplayEvidence {
    /// Build replay evidence for a specific manifest identity.
    pub fn new(
        problem_sha256: impl Into<String>,
        options_sha256: impl Into<String>,
        solver_identity_sha256: impl Into<String>,
        obligation_id: impl Into<String>,
        result: impl Into<String>,
        proof_status: impl Into<String>,
    ) -> Self {
        Self {
            schema: CHC_REPLAY_EVIDENCE_SCHEMA,
            problem_sha256: problem_sha256.into(),
            options_sha256: options_sha256.into(),
            solver_identity_sha256: solver_identity_sha256.into(),
            obligation_id: obligation_id.into(),
            result: result.into(),
            proof_status: proof_status.into(),
            solver_transcript: None,
            proof: None,
            replay_report: None,
            replay_log: None,
            checked_proof_report: None,
            invariant_model: None,
            counterexample: None,
            replay_obligations: Vec::new(),
        }
    }

    /// Attach a solver transcript artifact digest.
    #[must_use]
    pub fn with_solver_transcript(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.solver_transcript = Some(artifact);
        self
    }

    /// Attach a proof/certificate artifact digest.
    #[must_use]
    pub fn with_proof(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.proof = Some(artifact);
        self
    }

    /// Attach a checked replay report artifact digest.
    #[must_use]
    pub fn with_replay_report(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.replay_report = Some(artifact);
        self
    }

    /// Attach a replay log artifact digest.
    #[must_use]
    pub fn with_replay_log(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.replay_log = Some(artifact);
        self
    }

    /// Attach a checked proof report artifact digest.
    #[must_use]
    pub fn with_checked_proof_report(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.checked_proof_report = Some(artifact);
        self
    }

    /// Attach a safe-result invariant model artifact digest.
    #[must_use]
    pub fn with_invariant_model(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.invariant_model = Some(artifact);
        self
    }

    /// Attach an unsafe-result counterexample artifact digest.
    #[must_use]
    pub fn with_counterexample(mut self, artifact: ChcProofArtifactDigest) -> Self {
        self.counterexample = Some(artifact);
        self
    }

    /// Attach one replay obligation artifact digest.
    #[must_use]
    pub fn with_replay_obligation(mut self, artifact: ChcReplayObligationArtifact) -> Self {
        self.replay_obligations.push(artifact);
        self
    }

    /// SHA-256 over the stable replay evidence identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render this replay evidence binding as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        let obligations: Vec<_> = self
            .sorted_replay_obligations()
            .iter()
            .map(ChcReplayObligationArtifact::to_json_value)
            .collect();
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "identity_sha256": self.identity_sha256(),
            "problem_sha256": self.problem_sha256,
            "options_sha256": self.options_sha256,
            "solver_identity_sha256": self.solver_identity_sha256,
            "obligation_id": self.obligation_id,
            "result": self.result,
            "proof_status": self.proof_status,
            "solver_transcript": self.solver_transcript.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "proof": self.proof.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "replay_report": self.replay_report.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "replay_log": self.replay_log.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "checked_proof_report": self.checked_proof_report.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "invariant_model": self.invariant_model.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "counterexample": self.counterexample.as_ref().map(ChcProofArtifactDigest::to_json_value),
            "replay_obligations": obligations,
        })
    }

    /// Parse digest-bearing replay evidence from a manifest/cache snapshot.
    pub fn from_json_value(value: &serde_json::Value) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "replay_evidence is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            CHC_REPLAY_EVIDENCE_SCHEMA,
            "replay_evidence.schema",
            &mut reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "replay_evidence.schema_version",
            &mut reasons,
        );
        let problem_sha256 = sha256_string_field(
            object,
            "problem_sha256",
            "replay_evidence.problem_sha256",
            &mut reasons,
        );
        let options_sha256 = sha256_string_field(
            object,
            "options_sha256",
            "replay_evidence.options_sha256",
            &mut reasons,
        );
        let solver_identity_sha256 = sha256_string_field(
            object,
            "solver_identity_sha256",
            "replay_evidence.solver_identity_sha256",
            &mut reasons,
        );
        let obligation_id = string_field(
            object,
            "obligation_id",
            "replay_evidence.obligation_id",
            &mut reasons,
        );
        let result = string_field(object, "result", "replay_evidence.result", &mut reasons);
        let proof_status = string_field(
            object,
            "proof_status",
            "replay_evidence.proof_status",
            &mut reasons,
        );
        let replay_obligations =
            replay_obligations_from_json(object.get("replay_obligations"), &mut reasons);
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        let mut evidence = Self::new(
            problem_sha256.expect("problem hash parsed without reasons"),
            options_sha256.expect("options hash parsed without reasons"),
            solver_identity_sha256.expect("solver identity parsed without reasons"),
            obligation_id.expect("obligation id parsed without reasons"),
            result.expect("result parsed without reasons"),
            proof_status.expect("proof status parsed without reasons"),
        );
        evidence.solver_transcript = optional_artifact_field(
            object,
            "solver_transcript",
            "solver-transcript",
            "replay_evidence.solver_transcript",
            &mut reasons,
        );
        evidence.proof = optional_artifact_field(
            object,
            "proof",
            "proof-certificate",
            "replay_evidence.proof",
            &mut reasons,
        );
        evidence.replay_report = optional_artifact_field(
            object,
            "replay_report",
            "replay-report",
            "replay_evidence.replay_report",
            &mut reasons,
        );
        evidence.replay_log = optional_artifact_field(
            object,
            "replay_log",
            "replay-log",
            "replay_evidence.replay_log",
            &mut reasons,
        );
        evidence.checked_proof_report = optional_artifact_field(
            object,
            "checked_proof_report",
            "checked-proof-report",
            "replay_evidence.checked_proof_report",
            &mut reasons,
        );
        evidence.invariant_model = optional_artifact_field(
            object,
            "invariant_model",
            "invariant-model",
            "replay_evidence.invariant_model",
            &mut reasons,
        );
        evidence.counterexample = optional_artifact_field(
            object,
            "counterexample",
            "counterexample",
            "replay_evidence.counterexample",
            &mut reasons,
        );
        evidence.replay_obligations = replay_obligations;
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "replay_evidence.identity_sha256",
            &evidence.identity_sha256(),
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(evidence)
    }

    fn sorted_replay_obligations(&self) -> Vec<ChcReplayObligationArtifact> {
        let mut obligations = self.replay_obligations.clone();
        obligations.sort_by_key(|lhs| lhs.identity_input());
        obligations
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("problem_sha256={}\n", self.problem_sha256));
        out.push_str(&format!("options_sha256={}\n", self.options_sha256));
        out.push_str(&format!(
            "solver_identity_sha256={}\n",
            self.solver_identity_sha256
        ));
        out.push_str(&format!(
            "obligation_id={}\n",
            json_string(&self.obligation_id)
        ));
        out.push_str(&format!("result={}\n", json_string(&self.result)));
        out.push_str(&format!(
            "proof_status={}\n",
            json_string(&self.proof_status)
        ));
        push_optional_artifact_identity(&mut out, "solver_transcript", &self.solver_transcript);
        push_optional_artifact_identity(&mut out, "proof", &self.proof);
        push_optional_artifact_identity(&mut out, "replay_report", &self.replay_report);
        push_optional_artifact_identity(&mut out, "replay_log", &self.replay_log);
        push_optional_artifact_identity(
            &mut out,
            "checked_proof_report",
            &self.checked_proof_report,
        );
        push_optional_artifact_identity(&mut out, "invariant_model", &self.invariant_model);
        push_optional_artifact_identity(&mut out, "counterexample", &self.counterexample);
        for obligation in self.sorted_replay_obligations() {
            out.push_str("replay_obligation=");
            out.push_str(&obligation.identity_sha256());
            out.push('\n');
        }
        out
    }
}

/// External replay checker identity recorded in a checked CHC replay summary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcReplayCheckerIdentity {
    /// Checker binary or tool name.
    pub name: String,
    /// Checker version string captured by the replay runner.
    pub version: String,
    /// True when the replay was performed by an external checker process.
    pub external: bool,
}

impl ChcReplayCheckerIdentity {
    /// Create a checker identity.
    pub fn new(name: impl Into<String>, version: impl Into<String>, external: bool) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            external,
        }
    }

    /// SHA-256 over the stable checker identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the checker identity as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": CHC_REPLAY_CHECKER_IDENTITY_SCHEMA,
            "schema_version": 1,
            "name": self.name,
            "version": self.version,
            "external": self.external,
            "identity_sha256": self.identity_sha256(),
        })
    }

    fn from_json_value(value: &serde_json::Value, reasons: &mut Vec<String>) -> Option<Self> {
        let Some(object) = value.as_object() else {
            reasons.push("checker is not an object".to_string());
            return None;
        };
        expect_json_string(
            object,
            "schema",
            CHC_REPLAY_CHECKER_IDENTITY_SCHEMA,
            "checker.schema",
            reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "checker.schema_version",
            reasons,
        );
        let name = string_field(object, "name", "checker.name", reasons)?;
        let version = string_field(object, "version", "checker.version", reasons)?;
        let external = bool_field(object, "external", "checker.external", reasons)?;
        let checker = Self::new(name, version, external);
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "checker.identity_sha256",
            &checker.identity_sha256(),
            reasons,
        );
        Some(checker)
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(CHC_REPLAY_CHECKER_IDENTITY_SCHEMA);
        out.push('\n');
        out.push_str(&format!("name={}\n", json_string(&self.name)));
        out.push_str(&format!("version={}\n", json_string(&self.version)));
        out.push_str(&format!("external={}\n", self.external));
        out
    }
}

/// Checked replay command result for a full summary or one obligation query.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcReplayCheckResult {
    /// True when the replay runner actually executed the check.
    pub checked: bool,
    /// Stable replay status, expected to be `pass` for admission.
    pub status: String,
    /// Process exit code from the checker command.
    pub exit_code: i64,
    /// Number of failed replay checks reported by the runner.
    pub failures: u64,
}

impl ChcReplayCheckResult {
    /// Passing replay result.
    pub fn pass() -> Self {
        Self {
            checked: true,
            status: "pass".to_string(),
            exit_code: 0,
            failures: 0,
        }
    }

    /// Render the replay result as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": CHC_REPLAY_CHECK_RESULT_SCHEMA,
            "schema_version": 1,
            "checked": self.checked,
            "status": self.status,
            "exit_code": self.exit_code,
            "failures": self.failures,
        })
    }

    fn from_json_value(
        value: Option<&serde_json::Value>,
        label: &str,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let Some(value) = value else {
            reasons.push(format!("{label} is not an object"));
            return None;
        };
        let Some(object) = value.as_object() else {
            reasons.push(format!("{label} is not an object"));
            return None;
        };
        expect_json_string(
            object,
            "schema",
            CHC_REPLAY_CHECK_RESULT_SCHEMA,
            &format!("{label}.schema"),
            reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            &format!("{label}.schema_version"),
            reasons,
        );
        let checked = bool_field(object, "checked", &format!("{label}.checked"), reasons)?;
        let status = string_field(object, "status", &format!("{label}.status"), reasons)?;
        let exit_code = i64_field(object, "exit_code", &format!("{label}.exit_code"), reasons)?;
        let failures = u64_field(object, "failures", &format!("{label}.failures"), reasons)?;
        Some(Self {
            checked,
            status,
            exit_code,
            failures,
        })
    }

    fn validate_pass(&self, label: &str, reasons: &mut Vec<String>) {
        if !self.checked {
            reasons.push(format!("{label}.checked is not true"));
        }
        if self.status != "pass" {
            reasons.push(format!(
                "{label}.status={}, expected 'pass'",
                json_string(&self.status)
            ));
        }
        if self.exit_code != 0 {
            reasons.push(format!("{label}.exit_code={}", self.exit_code));
        }
        if self.failures != 0 {
            reasons.push(format!("{label}.failures={}", self.failures));
        }
    }

    fn identity_input(&self) -> String {
        format!(
            "{}\nchecked={}\nstatus={}\nexit_code={}\nfailures={}\n",
            CHC_REPLAY_CHECK_RESULT_SCHEMA,
            self.checked,
            json_string(&self.status),
            self.exit_code,
            self.failures
        )
    }
}

/// One checked CHC replay obligation query.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcCheckedReplayObligation {
    /// Human-readable obligation name.
    pub name: String,
    /// Obligation kind: `initiation`, `consecution`, `safety`, or
    /// `trace-validity`.
    pub kind: ChcReplayObligationKind,
    /// Hash-bound replay query.
    pub query: ChcProofArtifactDigest,
    /// Exact checker command used for this obligation.
    pub checker_command: String,
    /// Checked replay result for this obligation.
    pub result: ChcReplayCheckResult,
    /// Native strict certificate for this obligation, when it was an UNSAT
    /// obligation discharged by a real AY-native-verified proof.
    /// `None` for `sat` (trace-validity) obligations, which have no UNSAT
    /// proof, and for any obligation admitted before this evidence existed.
    pub strict_cert: Option<ChcObligationStrictCert>,
}

impl ChcCheckedReplayObligation {
    /// Build one replay obligation row.
    pub fn new(
        name: impl Into<String>,
        kind: ChcReplayObligationKind,
        query: ChcProofArtifactDigest,
        checker_command: impl Into<String>,
        result: ChcReplayCheckResult,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            query,
            checker_command: checker_command.into(),
            result,
            strict_cert: None,
        }
    }

    /// Attach native strict proof-bundle commitments to this obligation row.
    ///
    /// Used for UNSAT obligations discharged via
    /// `smtlib_strict_unsat_cert_via_executor`: the row records that AY's
    /// in-process, no-z3 offline checker verified the exact-bound bundle rather
    /// than merely trusting a re-run verdict. It stores only commitments, not
    /// the standalone bundle bytes; Alethe presentation is optional.
    #[must_use]
    pub(crate) fn with_strict_cert(mut self, cert: ChcObligationStrictCert) -> Self {
        self.strict_cert = Some(cert);
        self
    }

    /// SHA-256 over the stable obligation identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the replay obligation as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut value = serde_json::json!({
            "name": self.name,
            "kind": self.kind.as_str(),
            "query": self.query.to_json_value(),
            "checker_command": self.checker_command,
            "result": self.result.to_json_value(),
            "identity_sha256": self.identity_sha256(),
        });
        if let Some(cert) = &self.strict_cert {
            value["strict_cert"] = cert.to_json_value();
        }
        value
    }

    fn from_json_value(
        value: &serde_json::Value,
        index: usize,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let label = format!("obligations[{index}]");
        let Some(object) = value.as_object() else {
            reasons.push(format!("{label} is not an object"));
            return None;
        };
        let name = string_field(object, "name", &format!("{label}.name"), reasons)?;
        let kind = obligation_kind_field(object, "kind", &format!("{label}.kind"), reasons)?;
        let query = artifact_field(
            object,
            "query",
            "replay-obligation",
            &format!("{label}.query"),
            reasons,
        )?;
        let checker_command = string_field(
            object,
            "checker_command",
            &format!("{label}.checker_command"),
            reasons,
        )?;
        let result = ChcReplayCheckResult::from_json_value(
            object.get("result"),
            &format!("{label}.result"),
            reasons,
        )?;
        let strict_cert = ChcObligationStrictCert::from_json_value_opt(
            object,
            "strict_cert",
            &format!("{label}.strict_cert"),
            reasons,
        );
        let mut obligation = Self::new(name, kind, query, checker_command, result);
        obligation.strict_cert = strict_cert;
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            &format!("{label}.identity_sha256"),
            &obligation.identity_sha256(),
            reasons,
        );
        Some(obligation)
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str("ay.chc-checked-replay-obligation/v1\n");
        out.push_str(&format!("name={}\n", json_string(&self.name)));
        out.push_str(&format!("kind={}\n", self.kind.as_str()));
        out.push_str(&format!("query={}\n", self.query.identity_sha256()));
        out.push_str(&format!(
            "checker_command={}\n",
            json_string(&self.checker_command)
        ));
        out.push_str(&self.result.identity_input());
        // Include the strict cert in identity only when present, so obligations
        // recorded before this evidence existed keep their prior identity
        // (backward compatible), while a cert-bearing obligation binds its
        // bundle checker/schema, bundle digest, and explicit Alethe-presence
        // state into the obligation identity.
        if let Some(cert) = &self.strict_cert {
            out.push_str(&cert.identity_input());
        }
        out
    }
}

/// File artifacts checked by an external CHC certificate replay run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcCheckedReplayArtifacts {
    /// Original or normalized CHC problem artifact checked by the replay packet.
    pub problem: ChcProofArtifactDigest,
    /// Emitted CHC certificate artifact checked by the replay packet.
    pub certificate: ChcProofArtifactDigest,
    /// Solver run log artifact checked by the replay packet.
    pub run_log: ChcProofArtifactDigest,
    /// External replay log/report artifact checked by the replay packet.
    pub replay_log: ChcProofArtifactDigest,
}

impl ChcCheckedReplayArtifacts {
    /// Build the artifact bundle required for a checked replay summary.
    pub fn new(
        problem: ChcProofArtifactDigest,
        certificate: ChcProofArtifactDigest,
        run_log: ChcProofArtifactDigest,
        replay_log: ChcProofArtifactDigest,
    ) -> Self {
        Self {
            problem,
            certificate,
            run_log,
            replay_log,
        }
    }
}

/// Binding that ties a checked replay summary to one evidence manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcCheckedReplayManifestBinding {
    /// Binding schema identifier.
    pub schema: &'static str,
    /// Evidence manifest schema this summary claims to bind.
    pub evidence_manifest_schema: String,
    /// Normalized CHC/PDR problem hash from the manifest.
    pub problem_sha256: String,
    /// Proof/resource option identity from the manifest.
    pub options_sha256: String,
    /// Solver identity hash from the manifest.
    pub solver_identity_sha256: String,
    /// Caller-stable proof obligation id from the manifest.
    pub obligation_id: String,
    /// Manifest result.
    pub result: String,
    /// Manifest proof status.
    pub proof_status: String,
    /// Admission key before the checked summary is attached.
    pub precheck_admission_key_sha256: String,
    /// Replay evidence identity from the manifest, when present.
    pub replay_evidence_sha256: Option<String>,
    /// Solver transcript hash expected by the manifest.
    pub solver_transcript_sha256: Option<String>,
    /// Proof/certificate artifact hash expected by the manifest.
    pub proof_artifact_sha256: Option<String>,
    /// Checked replay report hash expected by the manifest.
    pub replay_report_sha256: Option<String>,
    /// Replay obligation query hashes expected by the manifest.
    pub replay_obligation_query_sha256: Vec<String>,
    /// Replay obligation artifact identities expected by the manifest.
    pub replay_obligation_identity_sha256: Vec<String>,
}

impl ChcCheckedReplayManifestBinding {
    fn from_manifest(manifest: &ChcProofEvidenceManifest) -> Self {
        let replay_evidence = manifest.replay_evidence.as_ref();
        let precheck_admission_key_sha256 = manifest
            .checked_replay_summary
            .as_ref()
            .map(|summary| {
                summary
                    .manifest_binding
                    .precheck_admission_key_sha256
                    .clone()
            })
            .unwrap_or_else(|| manifest.admission_key_sha256());
        Self {
            schema: CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA,
            evidence_manifest_schema: manifest.schema.to_string(),
            problem_sha256: manifest.problem_sha256.clone(),
            options_sha256: manifest.options.identity_sha256(),
            solver_identity_sha256: manifest.solver.identity_sha256(),
            obligation_id: manifest.obligation_id.clone(),
            result: manifest.result.clone(),
            proof_status: manifest.proof_status.clone(),
            precheck_admission_key_sha256,
            replay_evidence_sha256: replay_evidence.map(ChcReplayEvidence::identity_sha256),
            solver_transcript_sha256: replay_evidence
                .and_then(|evidence| evidence.solver_transcript.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            proof_artifact_sha256: replay_evidence
                .and_then(|evidence| evidence.proof.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            replay_report_sha256: replay_evidence
                .and_then(|evidence| evidence.replay_report.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            replay_obligation_query_sha256: replay_evidence
                .map(replay_obligation_query_hashes)
                .unwrap_or_default(),
            replay_obligation_identity_sha256: replay_evidence
                .map(replay_obligation_identity_hashes)
                .unwrap_or_default(),
        }
    }

    /// SHA-256 over the stable manifest binding.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the manifest binding as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "identity_sha256": self.identity_sha256(),
            "evidence_manifest_schema": self.evidence_manifest_schema,
            "problem_sha256": self.problem_sha256,
            "options_sha256": self.options_sha256,
            "solver_identity_sha256": self.solver_identity_sha256,
            "obligation_id": self.obligation_id,
            "result": self.result,
            "proof_status": self.proof_status,
            "precheck_admission_key_sha256": self.precheck_admission_key_sha256,
            "replay_evidence_sha256": self.replay_evidence_sha256,
            "solver_transcript_sha256": self.solver_transcript_sha256,
            "proof_artifact_sha256": self.proof_artifact_sha256,
            "replay_report_sha256": self.replay_report_sha256,
            "replay_obligation_query_sha256": self.replay_obligation_query_sha256,
            "replay_obligation_identity_sha256": self.replay_obligation_identity_sha256,
        })
    }

    fn from_json_value(
        value: Option<&serde_json::Value>,
        reasons: &mut Vec<String>,
    ) -> Option<Self> {
        let Some(value) = value else {
            reasons.push("manifest_binding is missing".to_string());
            return None;
        };
        let Some(object) = value.as_object() else {
            reasons.push("manifest_binding is not an object".to_string());
            return None;
        };
        expect_json_string(
            object,
            "schema",
            CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA,
            "manifest_binding.schema",
            reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "manifest_binding.schema_version",
            reasons,
        );
        let evidence_manifest_schema = string_field(
            object,
            "evidence_manifest_schema",
            "manifest_binding.evidence_manifest_schema",
            reasons,
        )?;
        let problem_sha256 = sha256_string_field(
            object,
            "problem_sha256",
            "manifest_binding.problem_sha256",
            reasons,
        )?;
        let options_sha256 = sha256_string_field(
            object,
            "options_sha256",
            "manifest_binding.options_sha256",
            reasons,
        )?;
        let solver_identity_sha256 = sha256_string_field(
            object,
            "solver_identity_sha256",
            "manifest_binding.solver_identity_sha256",
            reasons,
        )?;
        let obligation_id = string_field(
            object,
            "obligation_id",
            "manifest_binding.obligation_id",
            reasons,
        )?;
        let result = string_field(object, "result", "manifest_binding.result", reasons)?;
        let proof_status = string_field(
            object,
            "proof_status",
            "manifest_binding.proof_status",
            reasons,
        )?;
        let precheck_admission_key_sha256 = sha256_string_field(
            object,
            "precheck_admission_key_sha256",
            "manifest_binding.precheck_admission_key_sha256",
            reasons,
        )?;
        let replay_evidence_sha256 = optional_sha256_field(
            object,
            "replay_evidence_sha256",
            "manifest_binding.replay_evidence_sha256",
            reasons,
        );
        let solver_transcript_sha256 = optional_sha256_field(
            object,
            "solver_transcript_sha256",
            "manifest_binding.solver_transcript_sha256",
            reasons,
        );
        let proof_artifact_sha256 = optional_sha256_field(
            object,
            "proof_artifact_sha256",
            "manifest_binding.proof_artifact_sha256",
            reasons,
        );
        let replay_report_sha256 = optional_sha256_field(
            object,
            "replay_report_sha256",
            "manifest_binding.replay_report_sha256",
            reasons,
        );
        let replay_obligation_query_sha256 = sha256_string_array_field(
            object,
            "replay_obligation_query_sha256",
            "manifest_binding.replay_obligation_query_sha256",
            reasons,
        )?;
        let replay_obligation_identity_sha256 = sha256_string_array_field(
            object,
            "replay_obligation_identity_sha256",
            "manifest_binding.replay_obligation_identity_sha256",
            reasons,
        )?;
        let binding = Self {
            schema: CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA,
            evidence_manifest_schema,
            problem_sha256,
            options_sha256,
            solver_identity_sha256,
            obligation_id,
            result,
            proof_status,
            precheck_admission_key_sha256,
            replay_evidence_sha256,
            solver_transcript_sha256,
            proof_artifact_sha256,
            replay_report_sha256,
            replay_obligation_query_sha256,
            replay_obligation_identity_sha256,
        };
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "manifest_binding.identity_sha256",
            &binding.identity_sha256(),
            reasons,
        );
        Some(binding)
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!(
            "evidence_manifest_schema={}\n",
            json_string(&self.evidence_manifest_schema)
        ));
        out.push_str(&format!("problem_sha256={}\n", self.problem_sha256));
        out.push_str(&format!("options_sha256={}\n", self.options_sha256));
        out.push_str(&format!(
            "solver_identity_sha256={}\n",
            self.solver_identity_sha256
        ));
        out.push_str(&format!(
            "obligation_id={}\n",
            json_string(&self.obligation_id)
        ));
        out.push_str(&format!("result={}\n", json_string(&self.result)));
        out.push_str(&format!(
            "proof_status={}\n",
            json_string(&self.proof_status)
        ));
        out.push_str(&format!(
            "precheck_admission_key_sha256={}\n",
            self.precheck_admission_key_sha256
        ));
        out.push_str(&format!(
            "replay_evidence_sha256={}\n",
            optional_identity(self.replay_evidence_sha256.as_deref())
        ));
        out.push_str(&format!(
            "solver_transcript_sha256={}\n",
            optional_identity(self.solver_transcript_sha256.as_deref())
        ));
        out.push_str(&format!(
            "proof_artifact_sha256={}\n",
            optional_identity(self.proof_artifact_sha256.as_deref())
        ));
        out.push_str(&format!(
            "replay_report_sha256={}\n",
            optional_identity(self.replay_report_sha256.as_deref())
        ));
        let mut obligations = self.replay_obligation_query_sha256.clone();
        obligations.sort();
        for sha256 in obligations {
            out.push_str(&format!("replay_obligation_query_sha256={sha256}\n"));
        }
        let mut obligation_identities = self.replay_obligation_identity_sha256.clone();
        obligation_identities.sort();
        for sha256 in obligation_identities {
            out.push_str(&format!("replay_obligation_identity_sha256={sha256}\n"));
        }
        out
    }
}

/// Parsed, typed `ay-chc-certificate-replay/v1` summary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcCheckedReplaySummary {
    /// Summary schema identifier.
    pub schema: &'static str,
    /// Summary status emitted by the replay runner.
    pub status: String,
    /// Proof surface, expected to be `CHC certificates`.
    pub surface: String,
    /// ay source revision checked by the replay runner.
    pub ay_commit: Option<String>,
    /// Failure classifier. Nonempty values reject admission.
    pub failure_kind: Option<String>,
    /// Diagnostic-only summaries cannot admit proof evidence.
    pub diagnostic_only: bool,
    /// CHC verdict checked by the summary.
    pub verdict: String,
    /// External checker identity.
    pub checker: ChcReplayCheckerIdentity,
    /// Top-level replay command.
    pub command: String,
    /// Binding to the exact evidence manifest and precheck admission key.
    pub manifest_binding: ChcCheckedReplayManifestBinding,
    /// Raw CHC problem artifact checked by the replay packet.
    pub problem: ChcProofArtifactDigest,
    /// CHC proof/certificate artifact checked by the replay packet.
    pub certificate: ChcProofArtifactDigest,
    /// Solver run log artifact checked by the replay packet.
    pub run_log: ChcProofArtifactDigest,
    /// Replay log/report artifact checked by the replay packet.
    pub replay_log: ChcProofArtifactDigest,
    /// Top-level checked replay result.
    pub result: ChcReplayCheckResult,
    /// Per-obligation replay checks.
    pub obligations: Vec<ChcCheckedReplayObligation>,
    /// Replay runner errors. Must be empty for admission.
    pub errors: Vec<String>,
}

impl ChcCheckedReplaySummary {
    /// Build and validate a passing checked replay summary for a manifest.
    ///
    /// This is the fail-closed constructor external replay runners should use
    /// after they have executed the checker process and observed every required
    /// CHC obligation pass. Unsafe manifests require a passing `trace-validity`
    /// obligation; safe manifests require `initiation`, `consecution`, and
    /// `safety`.
    pub fn from_passed_manifest_replay(
        manifest: &ChcProofEvidenceManifest,
        artifacts: ChcCheckedReplayArtifacts,
        checker: ChcReplayCheckerIdentity,
        command: impl Into<String>,
        obligations: Vec<ChcCheckedReplayObligation>,
    ) -> Result<Self, ChcCheckedReplaySummaryError> {
        let summary = Self {
            schema: CHC_CHECKED_REPLAY_SUMMARY_SCHEMA,
            status: "pass".to_string(),
            surface: "CHC certificates".to_string(),
            ay_commit: manifest.solver.ay_revision.clone(),
            failure_kind: None,
            diagnostic_only: false,
            verdict: manifest.result.clone(),
            checker,
            command: command.into(),
            manifest_binding: manifest.checked_replay_manifest_binding(),
            problem: artifacts.problem,
            certificate: artifacts.certificate,
            run_log: artifacts.run_log,
            replay_log: artifacts.replay_log,
            result: ChcReplayCheckResult::pass(),
            obligations,
            errors: Vec::new(),
        };
        let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);
        if reasons.is_empty() {
            Ok(summary)
        } else {
            Err(ChcCheckedReplaySummaryError::new(reasons))
        }
    }

    /// Parse a checked replay summary from JSON.
    pub fn from_json_value(
        value: &serde_json::Value,
    ) -> Result<Self, ChcCheckedReplaySummaryError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcCheckedReplaySummaryError::new(vec![
                "summary is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            CHC_CHECKED_REPLAY_SUMMARY_SCHEMA,
            "schema",
            &mut reasons,
        );
        expect_json_u64(object, "schema_version", 1, "schema_version", &mut reasons);
        let status = string_field(object, "status", "status", &mut reasons);
        let surface = string_field(object, "surface", "surface", &mut reasons);
        let ay_commit = optional_string_field(object, "ay_commit", "ay_commit", &mut reasons);
        let failure_kind =
            optional_string_field(object, "failure_kind", "failure_kind", &mut reasons);
        let diagnostic_only =
            optional_bool_field(object, "diagnostic_only", "diagnostic_only", &mut reasons)
                .unwrap_or(false);
        let verdict = string_field(object, "verdict", "verdict", &mut reasons);
        let checker = match object.get("checker") {
            Some(value) => ChcReplayCheckerIdentity::from_json_value(value, &mut reasons),
            None => {
                reasons.push("checker is not an object".to_string());
                None
            }
        };
        let command = string_field(object, "command", "command", &mut reasons);
        let manifest_binding = ChcCheckedReplayManifestBinding::from_json_value(
            object.get("manifest_binding"),
            &mut reasons,
        );
        let problem = artifact_field(object, "problem", "problem", "problem", &mut reasons);
        let certificate = artifact_field(
            object,
            "certificate",
            "proof-certificate",
            "certificate",
            &mut reasons,
        );
        let run_log = artifact_field(
            object,
            "run_log",
            "solver-transcript",
            "run_log",
            &mut reasons,
        );
        let replay_log = artifact_field(
            object,
            "replay_log",
            "replay-report",
            "replay_log",
            &mut reasons,
        );
        let result =
            ChcReplayCheckResult::from_json_value(object.get("result"), "result", &mut reasons);
        let obligations = obligations_from_json(object.get("obligations"), &mut reasons);
        let errors = string_vec_field(object, "errors", "errors", &mut reasons);

        if !reasons.is_empty() {
            return Err(ChcCheckedReplaySummaryError::new(reasons));
        }
        let summary = Self {
            schema: CHC_CHECKED_REPLAY_SUMMARY_SCHEMA,
            status: status.expect("status parsed without reasons"),
            surface: surface.expect("surface parsed without reasons"),
            ay_commit,
            failure_kind,
            diagnostic_only,
            verdict: verdict.expect("verdict parsed without reasons"),
            checker: checker.expect("checker parsed without reasons"),
            command: command.expect("command parsed without reasons"),
            manifest_binding: manifest_binding.expect("binding parsed without reasons"),
            problem: problem.expect("problem parsed without reasons"),
            certificate: certificate.expect("certificate parsed without reasons"),
            run_log: run_log.expect("run log parsed without reasons"),
            replay_log: replay_log.expect("replay log parsed without reasons"),
            result: result.expect("result parsed without reasons"),
            obligations,
            errors,
        };
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "identity_sha256",
            &summary.identity_sha256(),
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcCheckedReplaySummaryError::new(reasons));
        }
        Ok(summary)
    }

    /// SHA-256 over the stable summary identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the checked replay summary as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut obligations = self.obligations.clone();
        obligations.sort_by_key(|lhs| lhs.identity_input());
        let obligations: Vec<_> = obligations
            .iter()
            .map(ChcCheckedReplayObligation::to_json_value)
            .collect();
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "identity_sha256": self.identity_sha256(),
            "status": self.status,
            "surface": self.surface,
            "ay_commit": self.ay_commit,
            "failure_kind": self.failure_kind,
            "diagnostic_only": self.diagnostic_only,
            "verdict": self.verdict,
            "checker": self.checker.to_json_value(),
            "command": self.command,
            "manifest_binding": self.manifest_binding.to_json_value(),
            "problem": self.problem.to_json_value(),
            "certificate": self.certificate.to_json_value(),
            "run_log": self.run_log.to_json_value(),
            "replay_log": self.replay_log.to_json_value(),
            "result": self.result.to_json_value(),
            "obligations": obligations,
            "errors": self.errors,
        })
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("status={}\n", json_string(&self.status)));
        out.push_str(&format!("surface={}\n", json_string(&self.surface)));
        out.push_str(&format!(
            "ay_commit={}\n",
            self.ay_commit
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!(
            "failure_kind={}\n",
            self.failure_kind
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!("diagnostic_only={}\n", self.diagnostic_only));
        out.push_str(&format!("verdict={}\n", json_string(&self.verdict)));
        out.push_str(&format!("checker={}\n", self.checker.identity_sha256()));
        out.push_str(&format!("command={}\n", json_string(&self.command)));
        out.push_str(&format!(
            "manifest_binding={}\n",
            self.manifest_binding.identity_sha256()
        ));
        out.push_str(&format!("problem={}\n", self.problem.identity_sha256()));
        out.push_str(&format!(
            "certificate={}\n",
            self.certificate.identity_sha256()
        ));
        out.push_str(&format!("run_log={}\n", self.run_log.identity_sha256()));
        out.push_str(&format!(
            "replay_log={}\n",
            self.replay_log.identity_sha256()
        ));
        out.push_str("result\n");
        out.push_str(&self.result.identity_input());
        let mut obligations = self.obligations.clone();
        obligations.sort_by_key(|lhs| lhs.identity_input());
        for obligation in obligations {
            out.push_str(&format!("obligation={}\n", obligation.identity_sha256()));
        }
        let mut errors = self.errors.clone();
        errors.sort();
        for error in errors {
            out.push_str(&format!("error={}\n", json_string(&error)));
        }
        out
    }
}

/// Structured rejection details from checked CHC replay summary parsing or
/// manifest validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcCheckedReplaySummaryError {
    reasons: Vec<String>,
}

impl ChcCheckedReplaySummaryError {
    fn new(reasons: Vec<String>) -> Self {
        Self { reasons }
    }

    /// Rejection reasons, in deterministic validation order.
    pub fn reasons(&self) -> &[String] {
        &self.reasons
    }
}

impl std::fmt::Display for ChcCheckedReplaySummaryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "CHC checked replay summary rejected: {}",
            self.reasons.join("; ")
        )
    }
}

impl std::error::Error for ChcCheckedReplaySummaryError {}

/// Structured rejection details from parsing durable CHC proof evidence or
/// proof-query cache snapshots.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofEvidenceParseError {
    reasons: Vec<String>,
}

impl ChcProofEvidenceParseError {
    fn new(reasons: Vec<String>) -> Self {
        Self { reasons }
    }

    /// Rejection reasons, in deterministic validation order.
    pub fn reasons(&self) -> &[String] {
        &self.reasons
    }
}

impl std::fmt::Display for ChcProofEvidenceParseError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "CHC proof evidence JSON rejected: {}",
            self.reasons.join("; ")
        )
    }
}

impl std::error::Error for ChcProofEvidenceParseError {}

/// Replay/proof metadata attached to a verified CHC result.
///
/// Crate-internal constructors produce metadata-only records containing the
/// deterministic normalized input hash and result classification that an
/// external transcript/replay package must bind to. `Unknown` results are
/// always marked as non-proof. After a successful post-solve CHECKED replay
/// pass ([`ChcPdrProofRun::run_checked_replay`]), a crate-internal upgrade
/// carries `replayable` statuses plus transcript/replay/checked-report
/// digests. The Trust full-verifier admission bit stays fail-closed for
/// everything else — in particular for metadata parsed back from JSON.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofTranscriptMetadata {
    /// Metadata schema identifier.
    schema: &'static str,
    /// Normalized input schema identifier.
    normalized_input_schema: &'static str,
    /// SHA-256 of [`normalized_chc_input`], lowercase hex.
    normalized_input_sha256: String,
    /// Byte length of the normalized CHC input.
    normalized_input_bytes: u64,
    /// Solving engine family that produced the result.
    engine: String,
    /// Semantic CHC result: `safe`, `unsafe`, or `unknown`.
    result: String,
    /// Stable proof classification for consumers.
    proof_status: String,
    /// True only for validated safe/unsafe evidence.
    accepted_as_proof: bool,
    /// Replay material classification.
    replay_status: String,
    /// Transcript material classification.
    transcript_status: String,
    /// Structured reason when full-verifier admission is denied.
    trust_full_verifier_non_admission_reason: Option<String>,
    /// Structured unknown reason when `result == "unknown"`.
    unknown_reason: Option<String>,
    /// Checked-replay transcript digests. `Some` ONLY for metadata produced
    /// in-process by the crate-internal checked-replay upgrade from a validated
    /// checked replay summary. Deliberately private and NEVER
    /// populated by JSON parsing, so copied or mutated reporting metadata can
    /// never upgrade itself into replay evidence (fail-closed).
    checked_replay: Option<ChcCheckedReplayTranscriptDigests>,
}

/// Digest set carried by a checked (replayable) CHC proof transcript.
///
/// Only constructed by the crate-internal upgrade after the checked replay
/// summary validated against its evidence manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ChcCheckedReplayTranscriptDigests {
    /// Content address (or on-disk path) of the solver transcript artifact.
    transcript_uri: String,
    /// SHA-256 of the solver transcript (run log) bytes, lowercase hex.
    transcript_sha256: String,
    /// SHA-256 of the replay log (per-obligation pass record) bytes.
    replay_log_sha256: String,
    /// SHA-256 of the checked proof report (summary JSON) bytes.
    checked_report_sha256: String,
    /// Stable identity of the validated checked replay summary.
    summary_identity_sha256: String,
}

const BMC_TRACE_ASSIGNMENT_REQUIRED_FIELDS: [&str; 4] =
    ["name", "predicate_argument_index", "sort", "value"];
const BMC_TRACE_ASSIGNMENT_SUPPORTED_SORT_FAMILIES: [&str; 3] = ["Bool", "Int", "BitVec(width)"];
const BMC_TRACE_ASSIGNMENT_FAIL_CLOSED_SORT_FAMILIES: [&str; 5] = [
    "Real",
    "Array",
    "Datatype",
    "Uninterpreted",
    "BitVec(value_does_not_fit_i64)",
];
const BMC_TRACE_ASSIGNMENT_NAME_FORMAT: &str = "__p{predicate_id}_a{predicate_argument_index}";
const BMC_TRACE_ASSIGNMENT_SCOPE: &str = "unsafe_trace.steps[].assignments[]";
const BMC_TRACE_ASSIGNMENT_UNSUPPORTED_SORT_REASON_CODE: &str =
    "ay_chc_bmc_trace_assignment_sort_unsupported";
const BMC_TRACE_ASSIGNMENT_VALUE_OUT_OF_RANGE_REASON_CODE: &str =
    "ay_chc_bmc_trace_assignment_value_out_of_range";

/// Versioned contract for BMC unsafe trace assignment evidence rows.
///
/// Downstream consumers should use this descriptor to validate the assignment
/// rows AY emits under `unsafe_trace.steps[].assignments[]` instead of copying
/// local naming or sort-admission assumptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcBmcUnsafeTraceAssignmentContract {
    /// Contract schema identifier.
    pub schema: &'static str,
    /// Contract schema version.
    pub schema_version: u64,
    /// JSON scope where assignment rows appear.
    pub scope: &'static str,
    /// Stable producer for this contract.
    pub producer: &'static str,
    /// Canonical variable naming format for predicate argument assignments.
    pub canonical_name_format: &'static str,
    /// Assignment fields required for downstream acceptance.
    pub required_fields: &'static [&'static str],
    /// Predicate argument sort families admitted by the typed BMC trace path.
    pub supported_sort_families: &'static [&'static str],
    /// Sort families or value cases that must fail closed for typed assignment acceptance.
    pub fail_closed_sort_families: &'static [&'static str],
    /// Reason code for unsupported typed assignment sort families.
    pub unsupported_sort_reason_code: &'static str,
    /// Reason code when a concrete scalar value cannot be represented in the row encoding.
    pub value_out_of_range_reason_code: &'static str,
    /// Concrete value encoding used by assignment rows.
    pub value_encoding: &'static str,
}

impl ChcBmcUnsafeTraceAssignmentContract {
    /// Current BMC unsafe trace assignment evidence contract.
    pub const fn current() -> Self {
        Self {
            schema: CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA,
            schema_version: 1,
            scope: BMC_TRACE_ASSIGNMENT_SCOPE,
            producer: "ay_chc_bmc",
            canonical_name_format: BMC_TRACE_ASSIGNMENT_NAME_FORMAT,
            required_fields: &BMC_TRACE_ASSIGNMENT_REQUIRED_FIELDS,
            supported_sort_families: &BMC_TRACE_ASSIGNMENT_SUPPORTED_SORT_FAMILIES,
            fail_closed_sort_families: &BMC_TRACE_ASSIGNMENT_FAIL_CLOSED_SORT_FAMILIES,
            unsupported_sort_reason_code: BMC_TRACE_ASSIGNMENT_UNSUPPORTED_SORT_REASON_CODE,
            value_out_of_range_reason_code: BMC_TRACE_ASSIGNMENT_VALUE_OUT_OF_RANGE_REASON_CODE,
            value_encoding:
                "integer-encoded scalar: Bool 0/1, Int i64, BitVec unsigned value when it fits i64",
        }
    }

    /// Render the contract as stable JSON for sidecar/evidence sinks.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "scope": self.scope,
            "producer": self.producer,
            "canonical_name_format": self.canonical_name_format,
            "required_fields": self.required_fields,
            "supported_sort_families": self.supported_sort_families,
            "fail_closed_sort_families": self.fail_closed_sort_families,
            "unsupported_sort_reason_code": self.unsupported_sort_reason_code,
            "value_out_of_range_reason_code": self.value_out_of_range_reason_code,
            "value_encoding": self.value_encoding,
        })
    }
}

/// Current BMC unsafe trace assignment evidence contract.
pub const fn bmc_unsafe_trace_assignment_contract() -> ChcBmcUnsafeTraceAssignmentContract {
    ChcBmcUnsafeTraceAssignmentContract::current()
}

/// Typed status for BMC unsafe trace assignment completeness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcBmcUnsafeTraceAssignmentCompletenessStatus {
    /// The unsafe trace covers every expected step/predicate-argument assignment.
    Accepted,
    /// The unsafe trace cannot be accepted for downstream replay.
    Rejected,
}

impl ChcBmcUnsafeTraceAssignmentCompletenessStatus {
    /// Return the stable lower-snake-case status code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }
}

/// Typed reason for BMC unsafe trace assignment completeness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcBmcUnsafeTraceAssignmentCompletenessReason {
    /// The unsafe trace covers every expected assignment.
    Complete,
    /// The consumer evidence has no unsafe trace material.
    MissingUnsafeTrace,
    /// The trace step count does not match the downstream replay expectation.
    StepCountMismatch,
    /// At least one expected predicate-argument assignment is absent.
    IncompletePredicateArgumentAssignments,
    /// A step contains multiple assignments for the same expected predicate argument.
    DuplicatePredicateArgumentAssignment,
    /// A typed assignment uses a sort outside the BMC assignment contract.
    UnsupportedSortEncoding,
    /// A typed assignment value cannot be represented by the BMC assignment contract.
    ValueOutOfRange,
}

impl ChcBmcUnsafeTraceAssignmentCompletenessReason {
    /// Return the stable lower-snake-case reason code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::MissingUnsafeTrace => "missing_unsafe_trace",
            Self::StepCountMismatch => "step_count_mismatch",
            Self::IncompletePredicateArgumentAssignments => {
                "incomplete_predicate_argument_assignments"
            }
            Self::DuplicatePredicateArgumentAssignment => "duplicate_predicate_argument_assignment",
            Self::UnsupportedSortEncoding => BMC_TRACE_ASSIGNMENT_UNSUPPORTED_SORT_REASON_CODE,
            Self::ValueOutOfRange => BMC_TRACE_ASSIGNMENT_VALUE_OUT_OF_RANGE_REASON_CODE,
        }
    }
}

/// AY-owned summary of BMC unsafe trace assignment coverage.
///
/// Downstream BTOR2/hardware replay consumers should use this report instead of
/// locally counting trace steps and predicate-argument assignments.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcBmcUnsafeTraceAssignmentCompleteness {
    /// Report schema identifier.
    pub schema: &'static str,
    /// Report schema version.
    pub schema_version: u64,
    /// Typed completeness status.
    pub status: ChcBmcUnsafeTraceAssignmentCompletenessStatus,
    /// Stable completeness status code.
    pub status_code: &'static str,
    /// Typed completeness reason.
    pub reason: ChcBmcUnsafeTraceAssignmentCompletenessReason,
    /// Stable completeness reason code.
    pub reason_code: &'static str,
    /// Whether downstream replay can consume the trace assignments.
    pub accepted_for_consumer: bool,
    /// Whether rejection remains fail-closed.
    pub fail_closed: bool,
    /// Expected number of unsafe trace steps.
    pub expected_step_count: u64,
    /// Expected canonical predicate-argument assignments per step.
    pub expected_predicate_argument_count: u64,
    /// Expected total canonical predicate-argument assignments.
    pub expected_assignment_count: u64,
    /// Actual unsafe trace step count reported by AY.
    pub actual_step_count: u64,
    /// Number of expected canonical assignment cells covered before acceptance/rejection.
    pub covered_assignment_count: u64,
    /// First rejected or missing trace step index, when relevant.
    pub first_problem_step_index: Option<u64>,
    /// First rejected or missing predicate-argument index, when relevant.
    pub first_problem_predicate_argument_index: Option<u64>,
    /// Sort string for an unsupported sort rejection, when relevant.
    pub first_problem_sort: Option<String>,
    /// Concrete value for a value-encoding rejection, when relevant.
    pub first_problem_value: Option<i64>,
    /// Assignment contract schema used by this report.
    pub assignment_contract_schema: &'static str,
    /// Assignment contract schema version used by this report.
    pub assignment_contract_schema_version: u64,
}

impl ChcBmcUnsafeTraceAssignmentCompleteness {
    fn accepted(
        expected_step_count: u64,
        expected_predicate_argument_count: u64,
        actual_step_count: u64,
        covered_assignment_count: u64,
    ) -> Self {
        Self::new(
            ChcBmcUnsafeTraceAssignmentCompletenessStatus::Accepted,
            ChcBmcUnsafeTraceAssignmentCompletenessReason::Complete,
            expected_step_count,
            expected_predicate_argument_count,
            actual_step_count,
            covered_assignment_count,
            None,
            None,
            None,
            None,
        )
    }

    fn rejected(
        reason: ChcBmcUnsafeTraceAssignmentCompletenessReason,
        expected_step_count: u64,
        expected_predicate_argument_count: u64,
        actual_step_count: u64,
        covered_assignment_count: u64,
        first_problem_step_index: Option<u64>,
        first_problem_predicate_argument_index: Option<u64>,
        first_problem_sort: Option<String>,
        first_problem_value: Option<i64>,
    ) -> Self {
        Self::new(
            ChcBmcUnsafeTraceAssignmentCompletenessStatus::Rejected,
            reason,
            expected_step_count,
            expected_predicate_argument_count,
            actual_step_count,
            covered_assignment_count,
            first_problem_step_index,
            first_problem_predicate_argument_index,
            first_problem_sort,
            first_problem_value,
        )
    }

    fn new(
        status: ChcBmcUnsafeTraceAssignmentCompletenessStatus,
        reason: ChcBmcUnsafeTraceAssignmentCompletenessReason,
        expected_step_count: u64,
        expected_predicate_argument_count: u64,
        actual_step_count: u64,
        covered_assignment_count: u64,
        first_problem_step_index: Option<u64>,
        first_problem_predicate_argument_index: Option<u64>,
        first_problem_sort: Option<String>,
        first_problem_value: Option<i64>,
    ) -> Self {
        let accepted_for_consumer = matches!(
            status,
            ChcBmcUnsafeTraceAssignmentCompletenessStatus::Accepted
        );
        let contract = bmc_unsafe_trace_assignment_contract();
        Self {
            schema: CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
            schema_version: 1,
            status,
            status_code: status.code(),
            reason,
            reason_code: reason.code(),
            accepted_for_consumer,
            fail_closed: !accepted_for_consumer,
            expected_step_count,
            expected_predicate_argument_count,
            expected_assignment_count: expected_step_count
                .saturating_mul(expected_predicate_argument_count),
            actual_step_count,
            covered_assignment_count,
            first_problem_step_index,
            first_problem_predicate_argument_index,
            first_problem_sort,
            first_problem_value,
            assignment_contract_schema: contract.schema,
            assignment_contract_schema_version: contract.schema_version,
        }
    }

    /// Render this report as stable JSON for sidecar/evidence sinks.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "expected_step_count": self.expected_step_count,
            "expected_predicate_argument_count": self.expected_predicate_argument_count,
            "expected_assignment_count": self.expected_assignment_count,
            "actual_step_count": self.actual_step_count,
            "covered_assignment_count": self.covered_assignment_count,
            "first_problem_step_index": self.first_problem_step_index,
            "first_problem_predicate_argument_index": self.first_problem_predicate_argument_index,
            "first_problem_sort": self.first_problem_sort,
            "first_problem_value": self.first_problem_value,
            "assignment_contract_schema": self.assignment_contract_schema,
            "assignment_contract_schema_version": self.assignment_contract_schema_version,
        })
    }
}

/// Summarize unsafe trace assignment coverage for downstream BMC replay consumers.
pub fn bmc_unsafe_trace_assignment_completeness(
    evidence: &ChcProofTranscriptConsumerEvidence,
    expected_step_count: u64,
    expected_predicate_argument_count: u64,
) -> ChcBmcUnsafeTraceAssignmentCompleteness {
    evidence.bmc_unsafe_trace_assignment_completeness(
        expected_step_count,
        expected_predicate_argument_count,
    )
}

/// One concrete scalar assignment in an unsafe CHC trace.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcTraceAssignmentEvidence {
    /// Variable name as emitted by the CHC counterexample builder.
    pub name: String,
    /// Predicate argument index when the assignment uses AY's canonical CHC name.
    pub predicate_argument_index: Option<u64>,
    /// Sort of the assigned predicate argument, when it can be inferred.
    pub sort: Option<String>,
    /// Concrete integer-encoded value for the variable at this trace step.
    pub value: i64,
}

impl ChcTraceAssignmentEvidence {
    /// Render the assignment as stable JSON for sidecar/evidence sinks.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "name": self.name,
            "predicate_argument_index": self.predicate_argument_index,
            "sort": self.sort,
            "value": self.value,
        })
    }
}

/// One step in a concrete unsafe CHC trace.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcTraceStepEvidence {
    /// Zero-based trace step index.
    pub step_index: u64,
    /// Dense predicate identifier within the solved CHC problem.
    pub predicate_id: u64,
    /// Predicate name from the solved CHC problem, when still available.
    pub predicate_name: Option<String>,
    /// TLA+ action identifier associated with this transition step, if present.
    pub action_id: Option<u64>,
    /// TLA+ action name associated with this transition step, if present.
    pub action_name: Option<String>,
    /// Clause index used to derive this trace step, if present.
    pub clause_index: Option<u64>,
    /// Concrete scalar assignments for this step, sorted by variable name.
    pub assignments: Vec<ChcTraceAssignmentEvidence>,
}

impl ChcTraceStepEvidence {
    /// Render the trace step as stable JSON for sidecar/evidence sinks.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "step_index": self.step_index,
            "predicate_id": self.predicate_id,
            "predicate_name": self.predicate_name,
            "action_id": self.action_id,
            "action_name": self.action_name,
            "clause_index": self.clause_index,
            "assignments": self
                .assignments
                .iter()
                .map(ChcTraceAssignmentEvidence::to_json_value)
                .collect::<Vec<_>>(),
        })
    }
}

/// Concrete trace material attached to a validated unsafe CHC result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcUnsafeTraceEvidence {
    /// Stable trace status code.
    pub status: String,
    /// Number of concrete trace steps.
    pub step_count: u64,
    /// Concrete trace steps in execution order.
    pub steps: Vec<ChcTraceStepEvidence>,
}

impl ChcUnsafeTraceEvidence {
    /// Render the unsafe trace as stable JSON for sidecar/evidence sinks.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "status": self.status,
            "step_count": self.step_count,
            "steps": self
                .steps
                .iter()
                .map(ChcTraceStepEvidence::to_json_value)
                .collect::<Vec<_>>(),
        })
    }
}

/// Typed consumer evidence derived from a sealed CHC/PDR proof run.
///
/// This is the row shape downstream consumers should copy into capability
/// sidecars instead of reclassifying AY result strings. Acceptance is derived
/// from [`ChcPdrProofRun::accepted_as_proof`] and the sealed
/// [`VerifiedChcResult`], while Trust full-verifier admission remains
/// fail-closed through [`ChcProofTranscriptMetadata`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofTranscriptConsumerEvidence {
    /// Evidence schema identifier.
    schema: &'static str,
    /// Evidence schema version.
    schema_version: u64,
    /// Human-readable verdict label.
    verdict: String,
    /// Stable verdict code: `safe`, `unsafe`, or `unknown`.
    verdict_code: String,
    /// Query identity within the normalized CHC problem.
    query_id: String,
    /// False-head query clause index, when present.
    query_clause_index: Option<u64>,
    /// Property identity binding the normalized problem hash to the query.
    property_id: String,
    /// SHA-256 over the stable property identity.
    property_sha256: String,
    /// Solving backend family reported by the proof run.
    engine: String,
    /// Stable backend code for cross-consumer lane comparisons.
    backend_code: String,
    /// Normalized input schema identifier.
    normalized_input_schema: &'static str,
    /// SHA-256 of the normalized CHC input.
    normalized_input_sha256: String,
    /// Byte length of the normalized CHC input.
    normalized_input_bytes: u64,
    /// Stable proof classification from AY.
    proof_status: String,
    /// True only when AY's sealed result is validated safe/unsafe evidence.
    accepted_for_consumer: bool,
    /// Stable rejection code when [`accepted_for_consumer`](Self::accepted_for_consumer) is false.
    consumer_rejection_code: Option<String>,
    /// True only when the invariant/counterexample model was validated by AY.
    model_validated: bool,
    /// Stable model-validation status code.
    model_validation_status: String,
    /// Stable verification-level code for downstream evidence rows.
    verification_level_code: String,
    /// Trust full-verifier admission status code.
    trust_status: String,
    /// True only when this evidence has checked replay material for Trust admission.
    trust_full_verifier_admissible: bool,
    /// Structured reason when full-verifier admission is denied.
    trust_full_verifier_non_admission_reason: Option<String>,
    /// Replay material classification.
    replay_status: String,
    /// Transcript material classification.
    transcript_status: String,
    /// Structured unknown reason code, if this run is non-proof Unknown.
    unknown_reason_code: Option<String>,
    /// Structured limit code for bounded Unknown exits, if applicable.
    unknown_limit_code: Option<String>,
    /// Deepest BMC depth reached for bounded Unknown exits, if available.
    unknown_depth_reached: Option<u64>,
    /// BMC depth limit for bounded Unknown exits, if available.
    unknown_depth_limit: Option<u64>,
    /// Concrete trace material for validated unsafe results.
    unsafe_trace: Option<ChcUnsafeTraceEvidence>,
}

impl ChcProofTranscriptConsumerEvidence {
    /// Build typed consumer evidence from a sealed CHC/PDR proof run.
    pub(crate) fn for_run(run: &ChcPdrProofRun) -> Self {
        let problem = run.problem();
        let query_clause_index = chc_query_clause_index(problem).map(usize_to_u64);
        let query_id = query_clause_index
            .map(|index| format!("chc.false_clause.{index}"))
            .unwrap_or_else(|| "chc.false_clause.unknown".to_string());
        let property_id = format!("{}:{query_id}", run.metadata.normalized_input_sha256);
        let property_sha256 = sha256_hex(property_id.as_bytes());

        let accepted_for_consumer = run.accepted_as_proof();
        let (
            model_validated,
            model_validation_status,
            verification_level_code,
            consumer_rejection_code,
            unknown_reason_code,
            unknown_limit_code,
            unknown_depth_reached,
            unknown_depth_limit,
            unsafe_trace,
        ) = match &run.result {
            VerifiedChcResult::Safe(_) => (
                true,
                "validated".to_string(),
                "ay_chc_verified_invariant".to_string(),
                None,
                None,
                None,
                None,
                None,
                None,
            ),
            VerifiedChcResult::Unsafe(cex) => (
                true,
                "validated".to_string(),
                "ay_chc_verified_counterexample".to_string(),
                None,
                None,
                None,
                None,
                None,
                Some(unsafe_trace_evidence(problem, cex.counterexample())),
            ),
            VerifiedChcResult::Unknown(marker) => {
                let reason_code = marker.reason().code().to_string();
                (
                    false,
                    "not_validated".to_string(),
                    "ay_chc_non_proof".to_string(),
                    Some(format!("ay_chc_unknown_{reason_code}")),
                    Some(reason_code),
                    unknown_limit_code(marker).map(str::to_string),
                    marker.bmc_depth_reached().map(usize_to_u64),
                    marker.bmc_max_depth().map(usize_to_u64),
                    None,
                )
            }
        };

        Self {
            schema: CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA,
            schema_version: 1,
            verdict: run.metadata.result.clone(),
            verdict_code: run.metadata.result.clone(),
            query_id,
            query_clause_index,
            property_id,
            property_sha256,
            engine: run.metadata.engine.clone(),
            backend_code: chc_backend_code(&run.metadata.engine),
            normalized_input_schema: run.metadata.normalized_input_schema,
            normalized_input_sha256: run.metadata.normalized_input_sha256.clone(),
            normalized_input_bytes: run.metadata.normalized_input_bytes,
            proof_status: run.metadata.proof_status.clone(),
            accepted_for_consumer,
            consumer_rejection_code,
            model_validated,
            model_validation_status,
            verification_level_code,
            trust_status: if run.metadata.trust_full_verifier_admissible() {
                "trust_full_verifier_admissible".to_string()
            } else {
                "trust_full_verifier_rejected".to_string()
            },
            trust_full_verifier_admissible: run.metadata.trust_full_verifier_admissible(),
            trust_full_verifier_non_admission_reason: run
                .metadata
                .trust_full_verifier_non_admission_reason
                .clone(),
            replay_status: run.metadata.replay_status.clone(),
            transcript_status: run.metadata.transcript_status.clone(),
            unknown_reason_code,
            unknown_limit_code,
            unknown_depth_reached,
            unknown_depth_limit,
            unsafe_trace,
        }
    }

    /// Render this evidence as stable JSON for capability sidecars.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "verdict": self.verdict,
            "verdict_code": self.verdict_code,
            "query_id": self.query_id,
            "query_clause_index": self.query_clause_index,
            "property_id": self.property_id,
            "property_sha256": self.property_sha256,
            "engine": self.engine,
            "backend_code": self.backend_code,
            "normalized_input_schema": self.normalized_input_schema,
            "normalized_input_sha256": self.normalized_input_sha256,
            "pdr_input_sha256": self.normalized_input_sha256,
            "normalized_input_bytes": self.normalized_input_bytes,
            "proof_status": self.proof_status,
            "accepted_for_consumer": self.accepted_for_consumer,
            "consumer_rejection_code": self.consumer_rejection_code,
            "model_validated": self.model_validated,
            "model_validation_status": self.model_validation_status,
            "verification_level_code": self.verification_level_code,
            "trust_status": self.trust_status,
            "trust_full_verifier_admissible": self.trust_full_verifier_admissible,
            "trust_full_verifier_non_admission_reason": self.trust_full_verifier_non_admission_reason,
            "replay_status": self.replay_status,
            "transcript_status": self.transcript_status,
            "unknown_reason_code": self.unknown_reason_code,
            "unknown_limit_code": self.unknown_limit_code,
            "unknown_depth_reached": self.unknown_depth_reached,
            "unknown_depth_limit": self.unknown_depth_limit,
            "unsafe_trace_assignment_contract": bmc_unsafe_trace_assignment_contract().to_json_value(),
            "unsafe_trace": self
                .unsafe_trace
                .as_ref()
                .map(ChcUnsafeTraceEvidence::to_json_value)
                .unwrap_or_else(|| serde_json::json!({
                    "status": "not_applicable",
                    "step_count": 0,
                    "steps": [],
                })),
        })
    }

    /// Summarize whether unsafe trace assignments cover the expected BMC replay shape.
    ///
    /// The report checks for one canonical predicate-argument assignment for
    /// each argument index in `0..expected_predicate_argument_count` at every
    /// expected step. Non-canonical extra assignments are ignored. Missing,
    /// duplicate, unsupported-sort, and value-encoding failures are reported
    /// with stable fail-closed reason codes from AY.
    pub fn bmc_unsafe_trace_assignment_completeness(
        &self,
        expected_step_count: u64,
        expected_predicate_argument_count: u64,
    ) -> ChcBmcUnsafeTraceAssignmentCompleteness {
        let Some(trace) = &self.unsafe_trace else {
            return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                ChcBmcUnsafeTraceAssignmentCompletenessReason::MissingUnsafeTrace,
                expected_step_count,
                expected_predicate_argument_count,
                0,
                0,
                None,
                None,
                None,
                None,
            );
        };

        let actual_step_count = trace.step_count;
        if actual_step_count != expected_step_count
            || usize_to_u64(trace.steps.len()) != expected_step_count
        {
            return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                ChcBmcUnsafeTraceAssignmentCompletenessReason::StepCountMismatch,
                expected_step_count,
                expected_predicate_argument_count,
                actual_step_count,
                0,
                Some(actual_step_count.min(expected_step_count)),
                None,
                None,
                None,
            );
        }

        let mut covered_assignment_count = 0_u64;
        for (expected_step_index, step) in trace.steps.iter().enumerate() {
            let expected_step_index = usize_to_u64(expected_step_index);
            if step.step_index != expected_step_index {
                return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                    ChcBmcUnsafeTraceAssignmentCompletenessReason::StepCountMismatch,
                    expected_step_count,
                    expected_predicate_argument_count,
                    actual_step_count,
                    covered_assignment_count,
                    Some(expected_step_index),
                    None,
                    None,
                    None,
                );
            }

            let mut covered_arguments = BTreeSet::new();
            for assignment in &step.assignments {
                let Some(argument_index) = assignment.predicate_argument_index else {
                    continue;
                };
                if argument_index >= expected_predicate_argument_count {
                    continue;
                }
                if !covered_arguments.insert(argument_index) {
                    return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                        ChcBmcUnsafeTraceAssignmentCompletenessReason::DuplicatePredicateArgumentAssignment,
                        expected_step_count,
                        expected_predicate_argument_count,
                        actual_step_count,
                        covered_assignment_count,
                        Some(expected_step_index),
                        Some(argument_index),
                        assignment.sort.clone(),
                        Some(assignment.value),
                    );
                }
                if let Some(reason) = bmc_trace_assignment_encoding_rejection(assignment) {
                    return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                        reason,
                        expected_step_count,
                        expected_predicate_argument_count,
                        actual_step_count,
                        covered_assignment_count,
                        Some(expected_step_index),
                        Some(argument_index),
                        assignment.sort.clone(),
                        Some(assignment.value),
                    );
                }
            }

            for argument_index in 0..expected_predicate_argument_count {
                if !covered_arguments.contains(&argument_index) {
                    return ChcBmcUnsafeTraceAssignmentCompleteness::rejected(
                        ChcBmcUnsafeTraceAssignmentCompletenessReason::IncompletePredicateArgumentAssignments,
                        expected_step_count,
                        expected_predicate_argument_count,
                        actual_step_count,
                        covered_assignment_count,
                        Some(expected_step_index),
                        Some(argument_index),
                        None,
                        None,
                    );
                }
            }
            covered_assignment_count =
                covered_assignment_count.saturating_add(usize_to_u64(covered_arguments.len()));
        }

        ChcBmcUnsafeTraceAssignmentCompleteness::accepted(
            expected_step_count,
            expected_predicate_argument_count,
            actual_step_count,
            covered_assignment_count,
        )
    }
}

/// Verified CHC/PDR solve result plus replay/proof binding metadata.
///
/// This is the library-facing artifact for consumers that need a single
/// fail-closed object to feed into an external proof manifest. The metadata is
/// derived from the exact `ChcProblem` supplied to the solver and the sealed
/// [`VerifiedChcResult`] returned after validation.
#[derive(Clone)]
#[non_exhaustive]
#[must_use = "proof runs must be inspected; Unknown is non-proof evidence"]
pub struct ChcPdrProofRun {
    problem: std::sync::Arc<proof_run::IterativeDropProblem>,
    result: VerifiedChcResult,
    metadata: ChcProofTranscriptMetadata,
}

/// Stable proof-relevant option identity for CHC/PDR evidence manifests.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofEvidenceOptions {
    /// Proof mode that determines admissibility semantics.
    pub proof_mode: String,
    /// Maximum PDR frame count.
    pub max_frames: u64,
    /// Maximum PDR iteration count.
    pub max_iterations: u64,
    /// Maximum obligations processed by one strengthen call.
    pub max_obligations: u64,
    /// Optional solve timeout in milliseconds.
    pub solve_timeout_ms: Option<u64>,
    /// Optional process memory limit in bytes.
    pub memory_limit_bytes: Option<u64>,
    /// Whether strict proof mode was enabled.
    pub strict_proofs: bool,
}

impl ChcProofEvidenceOptions {
    /// Capture the proof-relevant public PDR resource limits and proof mode.
    pub fn pdr(config: &PdrConfig) -> Self {
        Self {
            proof_mode: if config.strict_proofs {
                "pdr-strict"
            } else {
                "pdr"
            }
            .to_string(),
            max_frames: config.max_frames as u64,
            max_iterations: config.max_iterations as u64,
            max_obligations: config.max_obligations as u64,
            solve_timeout_ms: config.solve_timeout.map(duration_millis_u64),
            memory_limit_bytes: None,
            strict_proofs: config.strict_proofs,
        }
    }

    /// Capture the proof-relevant public resource limits for CLI portfolio CHC.
    pub fn portfolio(time_budget: Duration, strict_proofs: bool) -> Self {
        let mut config = PdrConfig::production(false);
        config.solve_timeout = if time_budget.is_zero() {
            None
        } else {
            Some(time_budget)
        };
        config.strict_proofs = strict_proofs;
        let mut options = Self::pdr(&config);
        options.proof_mode = if strict_proofs {
            "portfolio-strict"
        } else {
            "portfolio"
        }
        .to_string();
        options
    }

    /// Capture the proof-grade PDR API mode. `solve_pdr_proof` forces this.
    pub fn pdr_strict(config: &PdrConfig) -> Self {
        let mut options = Self::pdr(config);
        options.proof_mode = "pdr-strict".to_string();
        options.strict_proofs = true;
        options
    }

    /// Attach a process memory limit to the proof/resource option identity.
    #[must_use]
    pub fn with_memory_limit_bytes(mut self, memory_limit_bytes: Option<u64>) -> Self {
        self.memory_limit_bytes = memory_limit_bytes;
        self
    }

    /// SHA-256 over the stable option identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the stable options as JSON for manifests and stats envelopes.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": "ay.chc-proof-options/v1",
            "proof_mode": self.proof_mode,
            "max_frames": self.max_frames,
            "max_iterations": self.max_iterations,
            "max_obligations": self.max_obligations,
            "solve_timeout_ms": self.solve_timeout_ms,
            "memory_limit_bytes": self.memory_limit_bytes,
            "strict_proofs": self.strict_proofs,
            "identity_sha256": self.identity_sha256(),
        })
    }

    /// Parse proof/resource options from a manifest/cache snapshot.
    pub fn from_json_value(value: &serde_json::Value) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "options is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            "ay.chc-proof-options/v1",
            "options.schema",
            &mut reasons,
        );
        let proof_mode = string_field(object, "proof_mode", "options.proof_mode", &mut reasons);
        let max_frames = u64_field(object, "max_frames", "options.max_frames", &mut reasons);
        let max_iterations = u64_field(
            object,
            "max_iterations",
            "options.max_iterations",
            &mut reasons,
        );
        let max_obligations = u64_field(
            object,
            "max_obligations",
            "options.max_obligations",
            &mut reasons,
        );
        let solve_timeout_ms = optional_u64_field(
            object,
            "solve_timeout_ms",
            "options.solve_timeout_ms",
            &mut reasons,
        );
        let memory_limit_bytes = optional_u64_field(
            object,
            "memory_limit_bytes",
            "options.memory_limit_bytes",
            &mut reasons,
        );
        let strict_proofs = bool_field(
            object,
            "strict_proofs",
            "options.strict_proofs",
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        let options = Self {
            proof_mode: proof_mode.expect("proof mode parsed without reasons"),
            max_frames: max_frames.expect("max frames parsed without reasons"),
            max_iterations: max_iterations.expect("max iterations parsed without reasons"),
            max_obligations: max_obligations.expect("max obligations parsed without reasons"),
            solve_timeout_ms,
            memory_limit_bytes,
            strict_proofs: strict_proofs.expect("strict proofs parsed without reasons"),
        };
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "options.identity_sha256",
            &options.identity_sha256(),
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(options)
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str("ay.chc-proof-options/v1\n");
        out.push_str(&format!("proof_mode={}\n", json_string(&self.proof_mode)));
        out.push_str(&format!("max_frames={}\n", self.max_frames));
        out.push_str(&format!("max_iterations={}\n", self.max_iterations));
        out.push_str(&format!("max_obligations={}\n", self.max_obligations));
        out.push_str(&format!(
            "solve_timeout_ms={}\n",
            self.solve_timeout_ms
                .map(|value| value.to_string())
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!(
            "memory_limit_bytes={}\n",
            self.memory_limit_bytes
                .map(|value| value.to_string())
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!("strict_proofs={}\n", self.strict_proofs));
        out
    }
}

/// Stable solver identity bound into evidence manifests and cache keys.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofSolverIdentity {
    /// Solver name.
    pub solver_name: String,
    /// Engine family, for example `pdr` or `portfolio`.
    pub engine: String,
    /// ay revision or build commit, when known.
    pub ay_revision: Option<String>,
    /// SHA-256 of the ay binary, when known.
    pub solver_binary_sha256: Option<String>,
    /// Extra dependency solver identities, already content-addressed by caller.
    pub dependency_solver_identities: Vec<String>,
}

impl ChcProofSolverIdentity {
    /// Create a ay solver identity for the named engine.
    pub fn new(engine: impl Into<String>) -> Self {
        Self {
            solver_name: "ay".to_string(),
            engine: engine.into(),
            ay_revision: None,
            solver_binary_sha256: None,
            dependency_solver_identities: Vec::new(),
        }
    }

    /// Attach a ay source revision/build commit.
    pub fn with_ay_revision(mut self, revision: impl Into<String>) -> Self {
        self.ay_revision = Some(revision.into());
        self
    }

    /// Attach a lowercase SHA-256 over the solver binary.
    pub fn with_solver_binary_sha256(mut self, sha256: impl Into<String>) -> Self {
        self.solver_binary_sha256 = Some(sha256.into());
        self
    }

    /// Attach an additional content-addressed dependency solver identity.
    pub fn with_dependency_solver_identity(mut self, identity: impl Into<String>) -> Self {
        self.dependency_solver_identities.push(identity.into());
        self
    }

    /// SHA-256 over the stable solver identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the solver identity as JSON for manifests and stats envelopes.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": "ay.chc-proof-solver-identity/v1",
            "solver_name": self.solver_name,
            "engine": self.engine,
            "ay_revision": self.ay_revision,
            "solver_binary_sha256": self.solver_binary_sha256,
            "dependency_solver_identities": self.sorted_dependencies(),
            "identity_sha256": self.identity_sha256(),
        })
    }

    /// Parse solver identity from a manifest/cache snapshot.
    pub fn from_json_value(value: &serde_json::Value) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "solver is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            "ay.chc-proof-solver-identity/v1",
            "solver.schema",
            &mut reasons,
        );
        let solver_name = string_field(object, "solver_name", "solver.solver_name", &mut reasons);
        let engine = string_field(object, "engine", "solver.engine", &mut reasons);
        let ay_revision =
            optional_string_field(object, "ay_revision", "solver.ay_revision", &mut reasons);
        let solver_binary_sha256 = optional_sha256_field(
            object,
            "solver_binary_sha256",
            "solver.solver_binary_sha256",
            &mut reasons,
        );
        let dependency_solver_identities = string_array_field(
            object,
            "dependency_solver_identities",
            "solver.dependency_solver_identities",
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        let solver = Self {
            solver_name: solver_name.expect("solver name parsed without reasons"),
            engine: engine.expect("engine parsed without reasons"),
            ay_revision,
            solver_binary_sha256,
            dependency_solver_identities,
        };
        check_optional_identity_sha256(
            object,
            "identity_sha256",
            "solver.identity_sha256",
            &solver.identity_sha256(),
            &mut reasons,
        );
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(solver)
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str("ay.chc-proof-solver-identity/v1\n");
        out.push_str(&format!("solver_name={}\n", json_string(&self.solver_name)));
        out.push_str(&format!("engine={}\n", json_string(&self.engine)));
        out.push_str(&format!(
            "ay_revision={}\n",
            self.ay_revision
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!(
            "solver_binary_sha256={}\n",
            self.solver_binary_sha256
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        for dependency in self.sorted_dependencies() {
            out.push_str(&format!("dependency={}\n", json_string(&dependency)));
        }
        out
    }

    fn sorted_dependencies(&self) -> Vec<String> {
        let mut dependencies = self.dependency_solver_identities.clone();
        dependencies.sort();
        dependencies
    }
}

/// Typed admission key for durable proof-query caches.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryAdmissionKey {
    schema: &'static str,
    problem_sha256: String,
    options_sha256: String,
    solver_identity_sha256: String,
    transcript_identity_sha256: String,
    replay_evidence_sha256: Option<String>,
    checked_replay_summary_sha256: Option<String>,
    checked_replay_checker_identity_sha256: Option<String>,
    solver_transcript_sha256: Option<String>,
    proof_artifact_sha256: Option<String>,
    replay_report_sha256: Option<String>,
    replay_log_sha256: Option<String>,
    checked_proof_report_sha256: Option<String>,
    invariant_model_sha256: Option<String>,
    counterexample_sha256: Option<String>,
    proof_mode: String,
    obligation_id: String,
    result: String,
    proof_status: String,
    accepted_as_proof: bool,
    trust_full_verifier_admissible: bool,
    replay_status: String,
    transcript_status: String,
}

impl ChcProofQueryAdmissionKey {
    fn from_manifest(manifest: &ChcProofEvidenceManifest) -> Self {
        Self {
            schema: CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA,
            problem_sha256: manifest.problem_sha256.clone(),
            options_sha256: manifest.options.identity_sha256(),
            solver_identity_sha256: manifest.solver.identity_sha256(),
            transcript_identity_sha256: manifest.transcript_metadata.identity_sha256(),
            replay_evidence_sha256: manifest
                .replay_evidence
                .as_ref()
                .map(ChcReplayEvidence::identity_sha256),
            checked_replay_summary_sha256: manifest
                .checked_replay_summary
                .as_ref()
                .map(ChcCheckedReplaySummary::identity_sha256),
            checked_replay_checker_identity_sha256: manifest
                .checked_replay_summary
                .as_ref()
                .map(|summary| summary.checker.identity_sha256()),
            solver_transcript_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.solver_transcript.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            proof_artifact_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.proof.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            replay_report_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.replay_report.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            replay_log_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.replay_log.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            checked_proof_report_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.checked_proof_report.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            invariant_model_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.invariant_model.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            counterexample_sha256: manifest
                .replay_evidence
                .as_ref()
                .and_then(|evidence| evidence.counterexample.as_ref())
                .map(|artifact| artifact.sha256.clone()),
            proof_mode: manifest.options.proof_mode.clone(),
            obligation_id: manifest.obligation_id.clone(),
            result: manifest.result.clone(),
            proof_status: manifest.proof_status.clone(),
            accepted_as_proof: manifest.accepted_as_proof,
            trust_full_verifier_admissible: manifest.trust_full_verifier_admissible,
            replay_status: manifest.transcript_metadata.replay_status.clone(),
            transcript_status: manifest.transcript_metadata.transcript_status.clone(),
        }
    }

    /// SHA-256 over the complete admission identity.
    pub fn sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the admission key as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "sha256": self.sha256(),
            "problem_sha256": self.problem_sha256,
            "options_sha256": self.options_sha256,
            "solver_identity_sha256": self.solver_identity_sha256,
            "transcript_identity_sha256": self.transcript_identity_sha256,
            "replay_evidence_sha256": self.replay_evidence_sha256,
            "checked_replay_summary_sha256": self.checked_replay_summary_sha256,
            "checked_replay_checker_identity_sha256": self.checked_replay_checker_identity_sha256,
            "solver_transcript_sha256": self.solver_transcript_sha256,
            "proof_artifact_sha256": self.proof_artifact_sha256,
            "replay_report_sha256": self.replay_report_sha256,
            "replay_log_sha256": self.replay_log_sha256,
            "checked_proof_report_sha256": self.checked_proof_report_sha256,
            "invariant_model_sha256": self.invariant_model_sha256,
            "counterexample_sha256": self.counterexample_sha256,
            "proof_mode": self.proof_mode,
            "obligation_id": self.obligation_id,
            "result": self.result,
            "proof_status": self.proof_status,
            "accepted_as_proof": self.accepted_as_proof,
            "trust_full_verifier_admissible": self.trust_full_verifier_admissible,
            "replay_status": self.replay_status,
            "transcript_status": self.transcript_status,
        })
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("problem_sha256={}\n", self.problem_sha256));
        out.push_str(&format!("options_sha256={}\n", self.options_sha256));
        out.push_str(&format!(
            "solver_identity_sha256={}\n",
            self.solver_identity_sha256
        ));
        out.push_str(&format!(
            "transcript_identity_sha256={}\n",
            self.transcript_identity_sha256
        ));
        out.push_str(&format!(
            "replay_evidence_sha256={}\n",
            optional_identity(self.replay_evidence_sha256.as_deref())
        ));
        out.push_str(&format!(
            "checked_replay_summary_sha256={}\n",
            optional_identity(self.checked_replay_summary_sha256.as_deref())
        ));
        out.push_str(&format!(
            "checked_replay_checker_identity_sha256={}\n",
            optional_identity(self.checked_replay_checker_identity_sha256.as_deref())
        ));
        out.push_str(&format!(
            "solver_transcript_sha256={}\n",
            optional_identity(self.solver_transcript_sha256.as_deref())
        ));
        out.push_str(&format!(
            "proof_artifact_sha256={}\n",
            optional_identity(self.proof_artifact_sha256.as_deref())
        ));
        out.push_str(&format!(
            "replay_report_sha256={}\n",
            optional_identity(self.replay_report_sha256.as_deref())
        ));
        out.push_str(&format!(
            "replay_log_sha256={}\n",
            optional_identity(self.replay_log_sha256.as_deref())
        ));
        out.push_str(&format!(
            "checked_proof_report_sha256={}\n",
            optional_identity(self.checked_proof_report_sha256.as_deref())
        ));
        out.push_str(&format!(
            "invariant_model_sha256={}\n",
            optional_identity(self.invariant_model_sha256.as_deref())
        ));
        out.push_str(&format!(
            "counterexample_sha256={}\n",
            optional_identity(self.counterexample_sha256.as_deref())
        ));
        out.push_str(&format!("proof_mode={}\n", json_string(&self.proof_mode)));
        out.push_str(&format!(
            "obligation_id={}\n",
            json_string(&self.obligation_id)
        ));
        out.push_str(&format!("result={}\n", json_string(&self.result)));
        out.push_str(&format!(
            "proof_status={}\n",
            json_string(&self.proof_status)
        ));
        out.push_str(&format!("accepted_as_proof={}\n", self.accepted_as_proof));
        out.push_str(&format!(
            "trust_full_verifier_admissible={}\n",
            self.trust_full_verifier_admissible
        ));
        out.push_str(&format!(
            "replay_status={}\n",
            json_string(&self.replay_status)
        ));
        out.push_str(&format!(
            "transcript_status={}\n",
            json_string(&self.transcript_status)
        ));
        out
    }
}

/// Stable lookup key for proof-query cache records.
///
/// This key is intentionally narrower than [`ChcProofQueryAdmissionKey`]: it
/// identifies the current obligation/result tuple that a compiler verifier
/// wants to reuse, while admission still depends on a checked replay summary and
/// the full artifact-bearing admission key on the cached record.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCacheLookupKey {
    /// Lookup key schema identifier.
    pub schema: &'static str,
    /// Evidence manifest schema the key was derived from.
    pub evidence_manifest_schema: &'static str,
    /// Normalized CHC/PDR problem hash.
    pub problem_sha256: String,
    /// Proof/resource option identity hash.
    pub options_sha256: String,
    /// Solver identity hash.
    pub solver_identity_sha256: String,
    /// Proof mode that scopes replay semantics.
    pub proof_mode: String,
    /// Caller-stable proof obligation id.
    pub obligation_id: String,
    /// Verified result label, such as `safe` or `unsafe`.
    pub result: String,
    /// Proof status label, such as `verified-invariant`.
    pub proof_status: String,
}

impl ChcProofQueryCacheLookupKey {
    fn from_manifest(manifest: &ChcProofEvidenceManifest) -> Self {
        Self {
            schema: CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA,
            evidence_manifest_schema: manifest.schema,
            problem_sha256: manifest.problem_sha256.clone(),
            options_sha256: manifest.options.identity_sha256(),
            solver_identity_sha256: manifest.solver.identity_sha256(),
            proof_mode: manifest.options.proof_mode.clone(),
            obligation_id: manifest.obligation_id.clone(),
            result: manifest.result.clone(),
            proof_status: manifest.proof_status.clone(),
        }
    }

    /// SHA-256 over the lookup key identity.
    pub fn sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the lookup key as JSON for cache indexes and diagnostics.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "sha256": self.sha256(),
            "evidence_manifest_schema": self.evidence_manifest_schema,
            "problem_sha256": self.problem_sha256,
            "options_sha256": self.options_sha256,
            "solver_identity_sha256": self.solver_identity_sha256,
            "proof_mode": self.proof_mode,
            "obligation_id": self.obligation_id,
            "result": self.result,
            "proof_status": self.proof_status,
        })
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!(
            "evidence_manifest_schema={}\n",
            json_string(self.evidence_manifest_schema)
        ));
        out.push_str(&format!("problem_sha256={}\n", self.problem_sha256));
        out.push_str(&format!("options_sha256={}\n", self.options_sha256));
        out.push_str(&format!(
            "solver_identity_sha256={}\n",
            self.solver_identity_sha256
        ));
        out.push_str(&format!("proof_mode={}\n", json_string(&self.proof_mode)));
        out.push_str(&format!(
            "obligation_id={}\n",
            json_string(&self.obligation_id)
        ));
        out.push_str(&format!("result={}\n", json_string(&self.result)));
        out.push_str(&format!(
            "proof_status={}\n",
            json_string(&self.proof_status)
        ));
        out
    }
}

/// Typed outcome for a proof-query cache hit admission check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcProofQueryCacheAdmissionStatus {
    /// The cached checked proof evidence may be reused for the current key.
    AdmitCheckedProofEvidence,
    /// The current manifest is not a proof-grade result.
    RejectCurrentNonProof,
    /// The cached record is not admitted checked proof evidence.
    RejectCachedNonAdmissible,
    /// The current lookup key does not match the cached record lookup key.
    RejectLookupKeyMismatch,
    /// The cached record does not carry a checked replay summary.
    RejectCachedSummaryMissing,
    /// The cached checked replay summary does not validate against the record.
    RejectCachedSummaryInvalid,
    /// The configured cache policy was not satisfied.
    RejectPolicyViolation,
}

impl ChcProofQueryCacheAdmissionStatus {
    /// Stable status label for JSON/report consumers.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::AdmitCheckedProofEvidence => "admit-checked-proof-evidence",
            Self::RejectCurrentNonProof => "reject-current-non-proof",
            Self::RejectCachedNonAdmissible => "reject-cached-non-admissible",
            Self::RejectLookupKeyMismatch => "reject-lookup-key-mismatch",
            Self::RejectCachedSummaryMissing => "reject-cached-summary-missing",
            Self::RejectCachedSummaryInvalid => "reject-cached-summary-invalid",
            Self::RejectPolicyViolation => "reject-policy-violation",
        }
    }

    /// True only for admitted checked proof evidence.
    pub fn is_admitted(self) -> bool {
        matches!(self, Self::AdmitCheckedProofEvidence)
    }
}

/// Fail-closed admission policy for durable proof-query cache hits.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCacheAdmissionPolicy {
    /// Policy schema identifier.
    pub schema: &'static str,
    /// Evidence manifest schema this policy accepts.
    pub required_evidence_manifest_schema: &'static str,
    /// Admission key schema this policy accepts.
    pub required_admission_key_schema: &'static str,
    /// Cache lookup key schema this policy accepts.
    pub required_lookup_key_schema: &'static str,
    /// Require a checked replay summary on cached records.
    pub require_checked_replay_summary: bool,
    /// Require the checked replay summary to identify an external checker.
    pub require_external_checker: bool,
}

impl Default for ChcProofQueryCacheAdmissionPolicy {
    fn default() -> Self {
        Self::trust_full_verifier()
    }
}

impl ChcProofQueryCacheAdmissionPolicy {
    /// Strict Trust full-verifier cache policy.
    pub fn trust_full_verifier() -> Self {
        Self {
            schema: CHC_PROOF_QUERY_CACHE_ADMISSION_POLICY_SCHEMA,
            required_evidence_manifest_schema: CHC_EVIDENCE_MANIFEST_SCHEMA,
            required_admission_key_schema: CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA,
            required_lookup_key_schema: CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA,
            require_checked_replay_summary: true,
            require_external_checker: true,
        }
    }

    /// SHA-256 over the stable policy identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Evaluate whether a cached checked proof record may be reused for the
    /// current manifest's lookup key.
    pub fn evaluate_cache_hit(
        &self,
        current: &ChcProofEvidenceManifest,
        cached: &ChcProofEvidenceManifest,
    ) -> ChcProofQueryCacheAdmissionDecision {
        let current_lookup_key = current.cache_lookup_key();
        let cached_lookup_key = cached.cache_lookup_key();
        let current_lookup_key_sha256 = current_lookup_key.sha256();
        let cached_lookup_key_sha256 = cached_lookup_key.sha256();
        let cached_admission_key_sha256 = cached.admission_key_sha256();
        let mut reasons = Vec::new();

        self.validate_manifest_schema("current", current, &current_lookup_key, &mut reasons);
        self.validate_manifest_schema("cached", cached, &cached_lookup_key, &mut reasons);

        if current_lookup_key_sha256 != cached_lookup_key_sha256 {
            reasons.push("cache_lookup_key_mismatch".to_string());
        }
        if !current.accepted_as_proof {
            reasons.push("current_manifest_result_is_non_proof".to_string());
        }
        if !matches!(current.result.as_str(), "safe" | "unsafe") {
            reasons.push(format!(
                "current_manifest_result_is_not_replayable:{}",
                current.result
            ));
        }
        if !cached.accepted_as_proof {
            reasons.push("cached_manifest_result_is_non_proof".to_string());
        }
        if !cached.trust_full_verifier_admissible() {
            reasons.push("cached_manifest_not_trust_full_verifier_admissible".to_string());
        }
        if !cached.non_admission_reasons.is_empty() {
            reasons.push(format!(
                "cached_manifest_has_non_admission_reasons:{:?}",
                cached.non_admission_reasons
            ));
        }
        if cached.replay_evidence.is_none() {
            reasons.push("cached_manifest_replay_evidence_missing".to_string());
        }

        match &cached.checked_replay_summary {
            Some(summary) => {
                if self.require_external_checker && !summary.checker.external {
                    reasons.push("cached_checked_replay_checker_not_external".to_string());
                }
                let summary_reasons = cached.checked_replay_summary_rejection_reasons(summary);
                for reason in summary_reasons {
                    reasons.push(format!("cached_checked_replay_summary_invalid:{reason}"));
                }
            }
            None if self.require_checked_replay_summary => {
                reasons.push("cached_checked_replay_summary_missing".to_string());
            }
            None => {}
        }

        let status = cache_admission_status_from_reasons(&reasons);
        ChcProofQueryCacheAdmissionDecision {
            schema: CHC_PROOF_QUERY_CACHE_ADMISSION_DECISION_SCHEMA,
            status,
            policy_sha256: self.identity_sha256(),
            current_lookup_key_sha256,
            cached_lookup_key_sha256,
            cached_admission_key_sha256,
            reasons,
        }
    }

    /// Render the policy as JSON for cache metadata.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "identity_sha256": self.identity_sha256(),
            "required_evidence_manifest_schema": self.required_evidence_manifest_schema,
            "required_admission_key_schema": self.required_admission_key_schema,
            "required_lookup_key_schema": self.required_lookup_key_schema,
            "require_checked_replay_summary": self.require_checked_replay_summary,
            "require_external_checker": self.require_external_checker,
        })
    }

    fn validate_manifest_schema(
        &self,
        label: &str,
        manifest: &ChcProofEvidenceManifest,
        lookup_key: &ChcProofQueryCacheLookupKey,
        reasons: &mut Vec<String>,
    ) {
        if manifest.schema != self.required_evidence_manifest_schema {
            reasons.push(format!("{label}_manifest_schema_mismatch"));
        }
        if manifest.admission_key().schema != self.required_admission_key_schema {
            reasons.push(format!("{label}_admission_key_schema_mismatch"));
        }
        if lookup_key.schema != self.required_lookup_key_schema {
            reasons.push(format!("{label}_lookup_key_schema_mismatch"));
        }
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!(
            "required_evidence_manifest_schema={}\n",
            json_string(self.required_evidence_manifest_schema)
        ));
        out.push_str(&format!(
            "required_admission_key_schema={}\n",
            json_string(self.required_admission_key_schema)
        ));
        out.push_str(&format!(
            "required_lookup_key_schema={}\n",
            json_string(self.required_lookup_key_schema)
        ));
        out.push_str(&format!(
            "require_checked_replay_summary={}\n",
            self.require_checked_replay_summary
        ));
        out.push_str(&format!(
            "require_external_checker={}\n",
            self.require_external_checker
        ));
        out
    }
}

/// Typed decision produced by a proof-query cache admission policy.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCacheAdmissionDecision {
    /// Decision schema identifier.
    pub schema: &'static str,
    /// Typed admission status.
    pub status: ChcProofQueryCacheAdmissionStatus,
    /// Policy identity used for this decision.
    pub policy_sha256: String,
    /// Current obligation lookup key.
    pub current_lookup_key_sha256: String,
    /// Cached record lookup key.
    pub cached_lookup_key_sha256: String,
    /// Full artifact-bearing admission key for the cached record.
    pub cached_admission_key_sha256: String,
    /// Deterministic fail-closed rejection reasons. Empty only when admitted.
    pub reasons: Vec<String>,
}

impl ChcProofQueryCacheAdmissionDecision {
    /// True only when the cache hit can be reused as checked proof evidence.
    pub fn admitted(&self) -> bool {
        self.status.is_admitted() && self.reasons.is_empty()
    }

    /// Stable decision status label.
    pub fn status_label(&self) -> &'static str {
        self.status.as_str()
    }

    /// SHA-256 over the decision identity.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    /// Render the typed decision as JSON for cache telemetry.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "identity_sha256": self.identity_sha256(),
            "status": self.status_label(),
            "admitted": self.admitted(),
            "policy_sha256": self.policy_sha256,
            "current_lookup_key_sha256": self.current_lookup_key_sha256,
            "cached_lookup_key_sha256": self.cached_lookup_key_sha256,
            "cached_admission_key_sha256": self.cached_admission_key_sha256,
            "reasons": self.reasons,
        })
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(self.schema);
        out.push('\n');
        out.push_str(&format!("status={}\n", self.status.as_str()));
        out.push_str(&format!("policy_sha256={}\n", self.policy_sha256));
        out.push_str(&format!(
            "current_lookup_key_sha256={}\n",
            self.current_lookup_key_sha256
        ));
        out.push_str(&format!(
            "cached_lookup_key_sha256={}\n",
            self.cached_lookup_key_sha256
        ));
        out.push_str(&format!(
            "cached_admission_key_sha256={}\n",
            self.cached_admission_key_sha256
        ));
        let mut reasons = self.reasons.clone();
        reasons.sort();
        for reason in reasons {
            out.push_str(&format!("reason={}\n", json_string(&reason)));
        }
        out
    }
}

/// Lookup outcome for a bounded proof-query cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcProofQueryCacheLookupStatus {
    /// A checked proof record was found and admitted by policy.
    Hit,
    /// No cache record matched the current lookup key.
    Miss,
    /// The same caller obligation was present, but identity/options/problem changed.
    Stale,
    /// A cached replay summary was present but no longer validates.
    ReplayFailed,
    /// A cache record was present but rejected by admission policy.
    Rejected,
}

impl ChcProofQueryCacheLookupStatus {
    /// Stable status label for JSON/report consumers.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Hit => "hit",
            Self::Miss => "miss",
            Self::Stale => "stale",
            Self::ReplayFailed => "replay-failed",
            Self::Rejected => "rejected",
        }
    }
}

/// Counters exposed by the proof-query cache.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCacheMetrics {
    /// Metrics schema identifier.
    pub schema: &'static str,
    /// Total lookup attempts.
    pub lookups: u64,
    /// Lookups admitted as reusable checked proof evidence.
    pub hits: u64,
    /// Lookups with no matching cache record.
    pub misses: u64,
    /// Lookups that found only stale records for the caller obligation.
    pub stale: u64,
    /// Lookups rejected because cached replay evidence no longer validates.
    pub replay_failed: u64,
    /// Inserts or lookups rejected by policy for other reasons.
    pub rejected: u64,
    /// Admissible records inserted into the cache.
    pub insertions: u64,
    /// Records evicted by the bounded LRU policy.
    pub evictions: u64,
    /// Current number of records in the cache.
    pub entries: u64,
}

impl Default for ChcProofQueryCacheMetrics {
    fn default() -> Self {
        Self {
            schema: CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA,
            lookups: 0,
            hits: 0,
            misses: 0,
            stale: 0,
            replay_failed: 0,
            rejected: 0,
            insertions: 0,
            evictions: 0,
            entries: 0,
        }
    }
}

impl ChcProofQueryCacheMetrics {
    /// Render metrics as JSON for Trust/model-checker-consumer telemetry.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "lookups": self.lookups,
            "hits": self.hits,
            "hit": self.hits,
            "misses": self.misses,
            "miss": self.misses,
            "stale": self.stale,
            "replay_failed": self.replay_failed,
            "replay-failed": self.replay_failed,
            "rejected": self.rejected,
            "insertions": self.insertions,
            "evictions": self.evictions,
            "entries": self.entries,
        })
    }
}

/// Result of one proof-query cache lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCacheLookupResult {
    /// Lookup result schema identifier.
    pub schema: &'static str,
    /// Typed lookup outcome.
    pub status: ChcProofQueryCacheLookupStatus,
    /// Lookup key requested by the caller.
    pub lookup_key_sha256: String,
    /// Cached lookup key considered for this lookup, if any.
    pub cached_lookup_key_sha256: Option<String>,
    /// Admission decision for an exact cache key match.
    pub admission_decision: Option<ChcProofQueryCacheAdmissionDecision>,
    /// Admitted cached manifest, present only for hits.
    pub admitted_manifest: Option<ChcProofEvidenceManifest>,
    /// Deterministic diagnostic reasons for misses, stale records, or rejections.
    pub reasons: Vec<String>,
}

impl ChcProofQueryCacheLookupResult {
    /// True when this lookup returned reusable checked proof evidence.
    pub fn admitted(&self) -> bool {
        matches!(self.status, ChcProofQueryCacheLookupStatus::Hit)
            && self.admitted_manifest.is_some()
    }

    /// Stable status label.
    pub fn status_label(&self) -> &'static str {
        self.status.as_str()
    }

    /// Borrow the admitted cached manifest, when this was a hit.
    pub fn admitted_manifest(&self) -> Option<&ChcProofEvidenceManifest> {
        self.admitted_manifest.as_ref()
    }

    /// Render the lookup result as JSON.
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "status": self.status_label(),
            "admitted": self.admitted(),
            "lookup_key_sha256": self.lookup_key_sha256,
            "cached_lookup_key_sha256": self.cached_lookup_key_sha256,
            "admission_decision": self.admission_decision.as_ref().map(ChcProofQueryCacheAdmissionDecision::to_json_value),
            "admitted_manifest": self.admitted_manifest.as_ref().map(ChcProofEvidenceManifest::to_json_value),
            "reasons": self.reasons,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ChcProofQueryCacheEntry {
    manifest: ChcProofEvidenceManifest,
    lookup_key_sha256: String,
    admission_key_sha256: String,
    inserted_at: u64,
    last_access: u64,
    hit_count: u64,
}

impl ChcProofQueryCacheEntry {
    fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "lookup_key_sha256": self.lookup_key_sha256,
            "admission_key_sha256": self.admission_key_sha256,
            "inserted_at": self.inserted_at,
            "last_access": self.last_access,
            "hit_count": self.hit_count,
            "manifest": self.manifest.to_json_value(),
        })
    }
}

/// Bounded proof-query cache for checked CHC/PDR evidence manifests.
///
/// The cache stores only manifests that the configured admission policy accepts
/// against themselves. Lookups still re-run policy admission against the current
/// manifest, so stale solver/options/problem identities and corrupted replay
/// summaries fail closed even when a lookup key is present.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofQueryCache {
    /// Cache schema identifier.
    pub schema: &'static str,
    policy: ChcProofQueryCacheAdmissionPolicy,
    max_entries: usize,
    entries: BTreeMap<String, ChcProofQueryCacheEntry>,
    next_access: u64,
    metrics: ChcProofQueryCacheMetrics,
}

impl ChcProofQueryCache {
    /// Create a Trust full-verifier cache with a bounded LRU capacity.
    pub fn new(max_entries: usize) -> Self {
        Self::with_policy(
            max_entries,
            ChcProofQueryCacheAdmissionPolicy::trust_full_verifier(),
        )
    }

    /// Create a cache with an explicit admission policy.
    pub fn with_policy(max_entries: usize, policy: ChcProofQueryCacheAdmissionPolicy) -> Self {
        Self {
            schema: CHC_PROOF_QUERY_CACHE_SCHEMA,
            policy,
            max_entries: max_entries.max(1),
            entries: BTreeMap::new(),
            next_access: 0,
            metrics: ChcProofQueryCacheMetrics::default(),
        }
    }

    /// Number of cached proof records.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// True when the cache has no records.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Return a metrics snapshot with the current entry count populated.
    pub fn metrics(&self) -> ChcProofQueryCacheMetrics {
        let mut metrics = self.metrics.clone();
        metrics.entries = self.entries.len() as u64;
        metrics
    }

    /// Insert a checked proof manifest if it satisfies the cache policy.
    ///
    /// The returned decision is empty-reason admitted only when the record was
    /// stored. Non-admissible manifests are not cached and increment the
    /// `rejected` metric.
    pub fn insert(
        &mut self,
        manifest: ChcProofEvidenceManifest,
    ) -> ChcProofQueryCacheAdmissionDecision {
        let decision = self.policy.evaluate_cache_hit(&manifest, &manifest);
        if !decision.admitted() {
            self.metrics.rejected = self.metrics.rejected.saturating_add(1);
            self.refresh_entry_metric();
            return decision;
        }

        let lookup_key_sha256 = manifest.cache_lookup_key_sha256();
        self.evict_for_insert(&lookup_key_sha256);
        let now = self.bump_access();
        let entry = ChcProofQueryCacheEntry {
            admission_key_sha256: manifest.admission_key_sha256(),
            manifest,
            lookup_key_sha256: lookup_key_sha256.clone(),
            inserted_at: now,
            last_access: now,
            hit_count: 0,
        };
        self.entries.insert(lookup_key_sha256, entry);
        self.metrics.insertions = self.metrics.insertions.saturating_add(1);
        self.refresh_entry_metric();
        decision
    }

    /// Look up a current manifest and admit a cached checked proof record only
    /// when the configured policy still accepts it.
    pub fn lookup(&mut self, current: &ChcProofEvidenceManifest) -> ChcProofQueryCacheLookupResult {
        self.metrics.lookups = self.metrics.lookups.saturating_add(1);
        let lookup_key_sha256 = current.cache_lookup_key_sha256();

        if let Some(entry) = self.entries.get(&lookup_key_sha256) {
            let decision = self.policy.evaluate_cache_hit(current, &entry.manifest);
            let cached_lookup_key_sha256 = Some(entry.lookup_key_sha256.clone());

            if decision.admitted() {
                let manifest = entry.manifest.clone();
                let now = self.bump_access();
                if let Some(entry) = self.entries.get_mut(&lookup_key_sha256) {
                    entry.last_access = now;
                    entry.hit_count = entry.hit_count.saturating_add(1);
                }
                self.metrics.hits = self.metrics.hits.saturating_add(1);
                self.refresh_entry_metric();
                return ChcProofQueryCacheLookupResult {
                    schema: CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA,
                    status: ChcProofQueryCacheLookupStatus::Hit,
                    lookup_key_sha256,
                    cached_lookup_key_sha256,
                    admission_decision: Some(decision),
                    admitted_manifest: Some(manifest),
                    reasons: Vec::new(),
                };
            }

            let status = if decision.status
                == ChcProofQueryCacheAdmissionStatus::RejectCachedSummaryInvalid
            {
                self.metrics.replay_failed = self.metrics.replay_failed.saturating_add(1);
                ChcProofQueryCacheLookupStatus::ReplayFailed
            } else {
                self.metrics.rejected = self.metrics.rejected.saturating_add(1);
                ChcProofQueryCacheLookupStatus::Rejected
            };
            let reasons = decision.reasons.clone();
            self.refresh_entry_metric();
            return ChcProofQueryCacheLookupResult {
                schema: CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA,
                status,
                lookup_key_sha256,
                cached_lookup_key_sha256,
                admission_decision: Some(decision),
                admitted_manifest: None,
                reasons,
            };
        }

        if let Some(stale_lookup_key_sha256) = self.stale_candidate_key(current) {
            self.metrics.stale = self.metrics.stale.saturating_add(1);
            self.refresh_entry_metric();
            return ChcProofQueryCacheLookupResult {
                schema: CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA,
                status: ChcProofQueryCacheLookupStatus::Stale,
                lookup_key_sha256,
                cached_lookup_key_sha256: Some(stale_lookup_key_sha256),
                admission_decision: None,
                admitted_manifest: None,
                reasons: vec![
                    "stale_cache_record_for_obligation_identity".to_string(),
                    "cache_lookup_key_mismatch".to_string(),
                ],
            };
        }

        self.metrics.misses = self.metrics.misses.saturating_add(1);
        self.refresh_entry_metric();
        ChcProofQueryCacheLookupResult {
            schema: CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA,
            status: ChcProofQueryCacheLookupStatus::Miss,
            lookup_key_sha256,
            cached_lookup_key_sha256: None,
            admission_decision: None,
            admitted_manifest: None,
            reasons: vec!["cache_lookup_key_absent".to_string()],
        }
    }

    /// Render a deterministic cache snapshot for diagnostics or caller-managed
    /// persistence.
    pub fn to_json_value(&self) -> serde_json::Value {
        let entries = self
            .entries
            .values()
            .map(ChcProofQueryCacheEntry::to_json_value)
            .collect::<Vec<_>>();
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "policy": self.policy.to_json_value(),
            "max_entries": self.max_entries,
            "metrics": self.metrics().to_json_value(),
            "entries": entries,
        })
    }

    /// Hydrate a bounded proof-query cache from a deterministic JSON snapshot.
    ///
    /// Every persisted entry is parsed as a typed evidence manifest and then
    /// re-admitted against the snapshot policy. Corrupt, stale, or metadata-only
    /// entries reject the entire snapshot instead of becoming cache hits.
    pub fn from_json_value(value: &serde_json::Value) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "cache snapshot is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            CHC_PROOF_QUERY_CACHE_SCHEMA,
            "cache.schema",
            &mut reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "cache.schema_version",
            &mut reasons,
        );
        let policy = parse_cache_policy_field(object.get("policy"), &mut reasons);
        let max_entries = u64_field(object, "max_entries", "cache.max_entries", &mut reasons)
            .and_then(|value| match usize::try_from(value) {
                Ok(value) => Some(value),
                Err(_) => {
                    reasons.push("cache.max_entries does not fit usize".to_string());
                    None
                }
            });
        let metrics = parse_cache_metrics_field(object.get("metrics"), &mut reasons);
        let Some(entries_json) = object.get("entries").and_then(serde_json::Value::as_array) else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "cache.entries is not an array".to_string(),
            ]));
        };
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        let policy = policy.expect("policy parsed without reasons");
        let max_entries = max_entries.expect("max entries parsed without reasons");
        let mut cache = Self::with_policy(max_entries, policy);
        cache.metrics = metrics.expect("metrics parsed without reasons");

        for (index, row) in entries_json.iter().enumerate() {
            let Some(entry_object) = row.as_object() else {
                reasons.push(format!("cache.entries[{index}] is not an object"));
                continue;
            };
            let lookup_key_sha256 = sha256_string_field(
                entry_object,
                "lookup_key_sha256",
                &format!("cache.entries[{index}].lookup_key_sha256"),
                &mut reasons,
            );
            let admission_key_sha256 = sha256_string_field(
                entry_object,
                "admission_key_sha256",
                &format!("cache.entries[{index}].admission_key_sha256"),
                &mut reasons,
            );
            let inserted_at = u64_field(
                entry_object,
                "inserted_at",
                &format!("cache.entries[{index}].inserted_at"),
                &mut reasons,
            );
            let last_access = u64_field(
                entry_object,
                "last_access",
                &format!("cache.entries[{index}].last_access"),
                &mut reasons,
            );
            let hit_count = u64_field(
                entry_object,
                "hit_count",
                &format!("cache.entries[{index}].hit_count"),
                &mut reasons,
            );
            let manifest = match entry_object.get("manifest") {
                Some(value) => match ChcProofEvidenceManifest::from_json_value(value) {
                    Ok(manifest) => Some(manifest),
                    Err(error) => {
                        for reason in error.reasons() {
                            reasons.push(format!("cache.entries[{index}].manifest:{reason}"));
                        }
                        None
                    }
                },
                None => {
                    reasons.push(format!("cache.entries[{index}].manifest is missing"));
                    None
                }
            };
            let Some(manifest) = manifest else {
                continue;
            };
            let (
                Some(lookup_key_sha256),
                Some(admission_key_sha256),
                Some(inserted_at),
                Some(last_access),
                Some(hit_count),
            ) = (
                lookup_key_sha256,
                admission_key_sha256,
                inserted_at,
                last_access,
                hit_count,
            )
            else {
                continue;
            };
            if lookup_key_sha256 != manifest.cache_lookup_key_sha256() {
                reasons.push(format!(
                    "cache.entries[{index}].lookup_key_sha256 does not match manifest"
                ));
            }
            if admission_key_sha256 != manifest.admission_key_sha256() {
                reasons.push(format!(
                    "cache.entries[{index}].admission_key_sha256 does not match manifest"
                ));
            }
            let decision = cache.policy.evaluate_cache_hit(&manifest, &manifest);
            if !decision.admitted() {
                reasons.push(format!(
                    "cache.entries[{index}] rejected by admission policy: {:?}",
                    decision.reasons
                ));
            }
            if cache.entries.contains_key(&lookup_key_sha256) {
                reasons.push(format!(
                    "cache.entries[{index}].lookup_key_sha256 is duplicated"
                ));
            }
            cache.next_access = cache.next_access.max(inserted_at).max(last_access);
            cache.entries.insert(
                lookup_key_sha256.clone(),
                ChcProofQueryCacheEntry {
                    manifest,
                    lookup_key_sha256,
                    admission_key_sha256,
                    inserted_at,
                    last_access,
                    hit_count,
                },
            );
        }

        if cache.entries.len() > cache.max_entries {
            reasons.push(format!(
                "cache.entries length {} exceeds max_entries {}",
                cache.entries.len(),
                cache.max_entries
            ));
        }
        cache.refresh_entry_metric();
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(cache)
    }

    /// Hydrate a proof-query cache from a JSON string.
    pub fn from_json_str(input: &str) -> Result<Self, ChcProofEvidenceParseError> {
        let value = serde_json::from_str(input)
            .map_err(|error| ChcProofEvidenceParseError::new(vec![error.to_string()]))?;
        Self::from_json_value(&value)
    }

    fn bump_access(&mut self) -> u64 {
        self.next_access = self.next_access.saturating_add(1);
        self.next_access
    }

    fn evict_for_insert(&mut self, inserting_key: &str) {
        while self.entries.len() >= self.max_entries && !self.entries.contains_key(inserting_key) {
            let Some(evict_key) = self
                .entries
                .iter()
                .min_by_key(|(_, entry)| (entry.last_access, entry.inserted_at))
                .map(|(key, _)| key.clone())
            else {
                break;
            };
            self.entries.remove(&evict_key);
            self.metrics.evictions = self.metrics.evictions.saturating_add(1);
        }
    }

    fn refresh_entry_metric(&mut self) {
        self.metrics.entries = self.entries.len() as u64;
    }

    fn stale_candidate_key(&self, current: &ChcProofEvidenceManifest) -> Option<String> {
        self.entries
            .values()
            .find(|entry| {
                entry.manifest.obligation_id == current.obligation_id
                    && entry.manifest.result == current.result
                    && entry.manifest.proof_status == current.proof_status
            })
            .map(|entry| entry.lookup_key_sha256.clone())
    }
}

fn cache_admission_status_from_reasons(reasons: &[String]) -> ChcProofQueryCacheAdmissionStatus {
    if reasons.is_empty() {
        return ChcProofQueryCacheAdmissionStatus::AdmitCheckedProofEvidence;
    }
    if reasons
        .iter()
        .any(|reason| reason == "current_manifest_result_is_non_proof")
    {
        return ChcProofQueryCacheAdmissionStatus::RejectCurrentNonProof;
    }
    if reasons
        .iter()
        .any(|reason| reason == "cache_lookup_key_mismatch")
    {
        return ChcProofQueryCacheAdmissionStatus::RejectLookupKeyMismatch;
    }
    if reasons
        .iter()
        .any(|reason| reason == "cached_checked_replay_summary_missing")
    {
        return ChcProofQueryCacheAdmissionStatus::RejectCachedSummaryMissing;
    }
    if reasons
        .iter()
        .any(|reason| reason.starts_with("cached_checked_replay_summary_invalid:"))
    {
        return ChcProofQueryCacheAdmissionStatus::RejectCachedSummaryInvalid;
    }
    if reasons.iter().any(|reason| {
        reason == "cached_manifest_not_trust_full_verifier_admissible"
            || reason == "cached_manifest_result_is_non_proof"
    }) {
        return ChcProofQueryCacheAdmissionStatus::RejectCachedNonAdmissible;
    }
    ChcProofQueryCacheAdmissionStatus::RejectPolicyViolation
}

/// Typed CHC/PDR evidence manifest for compiler verifier backends.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcProofEvidenceManifest {
    schema: &'static str,
    problem_schema: &'static str,
    problem_sha256: String,
    problem_bytes: u64,
    solver: ChcProofSolverIdentity,
    options: ChcProofEvidenceOptions,
    obligation_id: String,
    result: String,
    proof_status: String,
    accepted_as_proof: bool,
    trust_full_verifier_admissible: bool,
    transcript_metadata: ChcProofTranscriptMetadata,
    replay_evidence: Option<ChcReplayEvidence>,
    checked_replay_summary: Option<ChcCheckedReplaySummary>,
    replay_evidence_binding_status: String,
    non_admission_reasons: Vec<String>,
}

impl ChcProofEvidenceManifest {
    fn for_run(
        run: &ChcPdrProofRun,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
    ) -> Self {
        Self::for_run_with_replay_evidence(run, options, solver, obligation_id, None)
    }

    fn for_run_with_replay_evidence(
        run: &ChcPdrProofRun,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        replay_evidence: Option<ChcReplayEvidence>,
    ) -> Self {
        let problem = run.problem();
        let normalized = normalized_chc_input(problem);
        let problem_sha256 = sha256_hex(normalized.as_bytes());
        let problem_bytes = normalized.len() as u64;
        let accepted_as_proof = run.accepted_as_proof();
        let trust_full_verifier_admissible = false;
        let obligation_id = obligation_id.into();
        let result = result_label(&run.result).to_string();
        let proof_status = proof_status_label(&run.result).to_string();

        let mut non_admission_reasons = Vec::new();
        if run.metadata.normalized_input_sha256 != problem_sha256 {
            non_admission_reasons.push("metadata_problem_hash_mismatch".to_string());
        }
        if !accepted_as_proof {
            let reason = run
                .metadata
                .unknown_reason
                .as_deref()
                .unwrap_or("result_is_non_proof");
            non_admission_reasons.push(format!("result_is_non_proof:{reason}"));
        }
        if !trust_full_verifier_admissible {
            non_admission_reasons.push(
                run.metadata
                    .trust_full_verifier_non_admission_reason
                    .clone()
                    .unwrap_or_else(|| "missing_full_verifier_admission".to_string()),
            );
        }
        let replay_evidence_binding_status = replay_evidence_binding_status(
            replay_evidence.as_ref(),
            &problem_sha256,
            &options,
            &solver,
            &obligation_id,
            &result,
            &proof_status,
            &mut non_admission_reasons,
        );

        Self {
            schema: CHC_EVIDENCE_MANIFEST_SCHEMA,
            problem_schema: NORMALIZED_CHC_INPUT_SCHEMA,
            problem_sha256,
            problem_bytes,
            solver,
            options,
            obligation_id,
            result,
            proof_status,
            accepted_as_proof,
            trust_full_verifier_admissible,
            transcript_metadata: run.metadata.clone(),
            replay_evidence,
            checked_replay_summary: None,
            replay_evidence_binding_status,
            non_admission_reasons,
        }
    }

    /// Return the manifest binding that checked replay summaries must embed.
    pub fn checked_replay_manifest_binding(&self) -> ChcCheckedReplayManifestBinding {
        ChcCheckedReplayManifestBinding::from_manifest(self)
    }

    /// Return replay evidence attached to this manifest, if any.
    pub fn replay_evidence(&self) -> Option<&ChcReplayEvidence> {
        self.replay_evidence.as_ref()
    }

    /// Return the validated checked replay summary bound to this manifest, if
    /// one was admitted via [`Self::try_with_checked_replay_summary`].
    pub fn checked_replay_summary(&self) -> Option<&ChcCheckedReplaySummary> {
        self.checked_replay_summary.as_ref()
    }

    /// Attach an external replay report/log artifact after the replay runner
    /// has checked the emitted obligation queries.
    pub fn try_with_replay_report_artifact(
        mut self,
        artifact: ChcProofArtifactDigest,
    ) -> Result<Self, ChcCheckedReplaySummaryError> {
        let Some(mut evidence) = self.replay_evidence.take() else {
            return Err(ChcCheckedReplaySummaryError::new(vec![
                "manifest_replay_evidence is missing".to_string(),
            ]));
        };
        evidence.replay_report = Some(artifact);
        self.replay_evidence = Some(evidence);
        self.refresh_replay_evidence_binding_status();
        Ok(self)
    }

    /// Validate a checked replay summary against this manifest without changing
    /// admission state.
    pub fn checked_replay_summary_rejection_reasons(
        &self,
        summary: &ChcCheckedReplaySummary,
    ) -> Vec<String> {
        checked_replay_summary_rejection_reasons(self, summary)
    }

    /// Attach a checked CHC replay summary and admit the manifest only when all
    /// manifest, admission-key, and artifact bindings match.
    pub fn try_with_checked_replay_summary(
        mut self,
        summary: ChcCheckedReplaySummary,
    ) -> Result<Self, ChcCheckedReplaySummaryError> {
        let reasons = self.checked_replay_summary_rejection_reasons(&summary);
        if !reasons.is_empty() {
            return Err(ChcCheckedReplaySummaryError::new(reasons));
        }

        self.checked_replay_summary = Some(summary);
        self.trust_full_verifier_admissible = true;
        self.replay_evidence_binding_status = "checked-summary-bound".to_string();
        self.non_admission_reasons
            .retain(|reason| !checked_replay_resolves_reason(reason));
        Ok(self)
    }

    /// Return the fail-closed proof-query admission key.
    pub fn admission_key(&self) -> ChcProofQueryAdmissionKey {
        ChcProofQueryAdmissionKey::from_manifest(self)
    }

    /// SHA-256 of the admission key.
    pub fn admission_key_sha256(&self) -> String {
        self.admission_key().sha256()
    }

    /// Return the durable cache lookup key for this obligation/result tuple.
    pub fn cache_lookup_key(&self) -> ChcProofQueryCacheLookupKey {
        ChcProofQueryCacheLookupKey::from_manifest(self)
    }

    /// SHA-256 of the durable cache lookup key.
    pub fn cache_lookup_key_sha256(&self) -> String {
        self.cache_lookup_key().sha256()
    }

    /// Evaluate a cached checked proof record against this manifest using the
    /// supplied cache admission policy.
    pub fn cache_admission_decision_against(
        &self,
        cached: &Self,
        policy: &ChcProofQueryCacheAdmissionPolicy,
    ) -> ChcProofQueryCacheAdmissionDecision {
        policy.evaluate_cache_hit(self, cached)
    }

    /// Whether the manifest is admissible for Trust full-verifier proof reuse.
    pub fn trust_full_verifier_admissible(&self) -> bool {
        self.trust_full_verifier_admissible
    }

    /// Cache admission decision for this manifest.
    pub fn cache_admission_status(&self) -> &'static str {
        if self.trust_full_verifier_admissible {
            "admit-checked-proof-evidence"
        } else {
            "reject-non-admissible-proof-evidence"
        }
    }

    /// Render the manifest as stable JSON for compiler backend adapters.
    pub fn to_json_value(&self) -> serde_json::Value {
        let solver_transcript = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.solver_transcript.as_ref());
        let proof = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.proof.as_ref());
        let replay_report = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.replay_report.as_ref());
        let replay_log = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.replay_log.as_ref());
        let checked_proof_report = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.checked_proof_report.as_ref());
        let invariant_model = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.invariant_model.as_ref());
        let counterexample = self
            .replay_evidence
            .as_ref()
            .and_then(|evidence| evidence.counterexample.as_ref());
        let replay_obligations: Vec<_> = self
            .replay_evidence
            .as_ref()
            .map(ChcReplayEvidence::sorted_replay_obligations)
            .unwrap_or_default()
            .iter()
            .map(ChcReplayObligationArtifact::to_json_value)
            .collect();
        let checked_replay_summary = self.checked_replay_summary.as_ref();
        serde_json::json!({
            "schema": self.schema,
            "schema_version": 1,
            "problem": {
                "normalized_input_schema": self.problem_schema,
                "normalized_input_sha256": self.problem_sha256,
                "pdr_input_sha256": self.problem_sha256,
                "normalized_input_bytes": self.problem_bytes,
            },
            "solver": self.solver.to_json_value(),
            "options": self.options.to_json_value(),
            "obligation_id": self.obligation_id,
            "replay_evidence_binding_status": self.replay_evidence_binding_status,
            "result": {
                "result": self.result,
                "proof_status": self.proof_status,
                "accepted_as_proof": self.accepted_as_proof,
                "trust_full_verifier_admissible": self.trust_full_verifier_admissible(),
                "unknown_reason": self.transcript_metadata.unknown_reason,
            },
            "artifacts": {
                "normalized_input": {
                    "status": "hash-bound",
                    "sha256": self.problem_sha256,
                    "bytes": self.problem_bytes,
                    "required_for_trust_full_verifier": true,
                },
                "solver_transcript": {
                    "status": if solver_transcript.is_some() { "hash-bound" } else { "missing" },
                    "artifact": solver_transcript.map(ChcProofArtifactDigest::to_json_value),
                    "metadata_only": solver_transcript.is_none(),
                    "required_for_trust_full_verifier": true,
                },
                "proof": {
                    "status": if proof.is_some() { "hash-bound" } else { "missing" },
                    "artifact": proof.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": true,
                },
                "replay_report": {
                    "status": if replay_report.is_some() { "hash-bound" } else { "missing" },
                    "artifact": replay_report.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": true,
                },
                "replay_log": {
                    "status": if replay_log.is_some() { "hash-bound" } else { "missing" },
                    "artifact": replay_log.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": false,
                },
                "checked_proof_report": {
                    "status": if checked_proof_report.is_some() { "hash-bound" } else { "missing" },
                    "artifact": checked_proof_report.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": false,
                },
                "invariant_model": {
                    "status": if invariant_model.is_some() { "hash-bound" } else { "missing" },
                    "artifact": invariant_model.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": false,
                    "result_kind": "safe",
                },
                "counterexample": {
                    "status": if counterexample.is_some() { "hash-bound" } else { "missing" },
                    "artifact": counterexample.map(ChcProofArtifactDigest::to_json_value),
                    "required_for_trust_full_verifier": false,
                    "result_kind": "unsafe",
                },
                "replay_obligations": {
                    "status": if replay_obligations.is_empty() { "missing" } else { "hash-bound" },
                    "artifacts": replay_obligations,
                    "required_for_trust_full_verifier": true,
                },
            },
            "replay_evidence": self.replay_evidence.as_ref().map(ChcReplayEvidence::to_json_value),
            "checked_replay_summary": checked_replay_summary.map(ChcCheckedReplaySummary::to_json_value),
            "checked_replay": {
                "status": if checked_replay_summary.is_some() {
                    self.replay_evidence_binding_status.as_str()
                } else {
                    "missing"
                },
                "summary_sha256": checked_replay_summary.map(ChcCheckedReplaySummary::identity_sha256),
                "checker": checked_replay_summary.map(|summary| summary.checker.to_json_value()),
                "checker_identity_sha256": checked_replay_summary.map(|summary| summary.checker.identity_sha256()),
            },
            "admission": {
                "key": self.admission_key().to_json_value(),
                "cache_lookup_key": self.cache_lookup_key().to_json_value(),
                "cache_lookup_key_sha256": self.cache_lookup_key_sha256(),
                "cache_hit_admission": self.cache_admission_status(),
                "replay_evidence_sha256": self.replay_evidence.as_ref().map(ChcReplayEvidence::identity_sha256),
                "checked_replay_summary_sha256": checked_replay_summary.map(ChcCheckedReplaySummary::identity_sha256),
                "checked_replay_checker_identity_sha256": checked_replay_summary.map(|summary| summary.checker.identity_sha256()),
                "solver_transcript_sha256": solver_transcript.map(|artifact| artifact.sha256.clone()),
                "proof_artifact_sha256": proof.map(|artifact| artifact.sha256.clone()),
                "replay_report_sha256": replay_report.map(|artifact| artifact.sha256.clone()),
                "replay_log_sha256": replay_log.map(|artifact| artifact.sha256.clone()),
                "checked_proof_report_sha256": checked_proof_report.map(|artifact| artifact.sha256.clone()),
                "invariant_model_sha256": invariant_model.map(|artifact| artifact.sha256.clone()),
                "counterexample_sha256": counterexample.map(|artifact| artifact.sha256.clone()),
                "non_admission_reasons": self.non_admission_reasons,
            },
            "transcript_metadata": self.transcript_metadata.to_json_value(),
        })
    }

    /// Parse a typed evidence manifest from stable JSON.
    ///
    /// This is intended for durable proof-query cache hydration. Checked replay
    /// summaries are revalidated against the parsed manifest before any
    /// admitted state is accepted.
    pub fn from_json_value(value: &serde_json::Value) -> Result<Self, ChcProofEvidenceParseError> {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "manifest is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            CHC_EVIDENCE_MANIFEST_SCHEMA,
            "manifest.schema",
            &mut reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "manifest.schema_version",
            &mut reasons,
        );
        let Some(problem_object) = object.get("problem").and_then(serde_json::Value::as_object)
        else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "manifest.problem is not an object".to_string(),
            ]));
        };
        expect_json_string(
            problem_object,
            "normalized_input_schema",
            NORMALIZED_CHC_INPUT_SCHEMA,
            "manifest.problem.normalized_input_schema",
            &mut reasons,
        );
        let problem_sha256 = sha256_string_field(
            problem_object,
            "normalized_input_sha256",
            "manifest.problem.normalized_input_sha256",
            &mut reasons,
        );
        let problem_bytes = u64_field(
            problem_object,
            "normalized_input_bytes",
            "manifest.problem.normalized_input_bytes",
            &mut reasons,
        );
        let solver = parse_solver_field(object.get("solver"), &mut reasons);
        let options = parse_options_field(object.get("options"), &mut reasons);
        let obligation_id = string_field(
            object,
            "obligation_id",
            "manifest.obligation_id",
            &mut reasons,
        );
        let replay_evidence_binding_status = string_field(
            object,
            "replay_evidence_binding_status",
            "manifest.replay_evidence_binding_status",
            &mut reasons,
        );
        let Some(result_object) = object.get("result").and_then(serde_json::Value::as_object)
        else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "manifest.result is not an object".to_string(),
            ]));
        };
        let result = string_field(
            result_object,
            "result",
            "manifest.result.result",
            &mut reasons,
        );
        let proof_status = string_field(
            result_object,
            "proof_status",
            "manifest.result.proof_status",
            &mut reasons,
        );
        let accepted_as_proof = bool_field(
            result_object,
            "accepted_as_proof",
            "manifest.result.accepted_as_proof",
            &mut reasons,
        );
        let trust_full_verifier_admissible = bool_field(
            result_object,
            "trust_full_verifier_admissible",
            "manifest.result.trust_full_verifier_admissible",
            &mut reasons,
        );
        let replay_evidence =
            parse_replay_evidence_field(object.get("replay_evidence"), &mut reasons);
        let checked_replay_summary =
            parse_checked_replay_summary_field(object.get("checked_replay_summary"), &mut reasons);
        let transcript_metadata =
            parse_transcript_metadata_field(object.get("transcript_metadata"), &mut reasons);
        let non_admission_reasons = object
            .get("admission")
            .and_then(serde_json::Value::as_object)
            .map(|admission| {
                string_vec_field(
                    admission,
                    "non_admission_reasons",
                    "manifest.admission.non_admission_reasons",
                    &mut reasons,
                )
            })
            .unwrap_or_default();
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }

        let manifest = Self {
            schema: CHC_EVIDENCE_MANIFEST_SCHEMA,
            problem_schema: NORMALIZED_CHC_INPUT_SCHEMA,
            problem_sha256: problem_sha256.expect("problem hash parsed without reasons"),
            problem_bytes: problem_bytes.expect("problem bytes parsed without reasons"),
            solver: solver.expect("solver parsed without reasons"),
            options: options.expect("options parsed without reasons"),
            obligation_id: obligation_id.expect("obligation id parsed without reasons"),
            result: result.expect("result parsed without reasons"),
            proof_status: proof_status.expect("proof status parsed without reasons"),
            accepted_as_proof: accepted_as_proof.expect("accepted flag parsed without reasons"),
            trust_full_verifier_admissible: trust_full_verifier_admissible
                .expect("trust admission flag parsed without reasons"),
            transcript_metadata: transcript_metadata.expect("transcript parsed without reasons"),
            replay_evidence,
            checked_replay_summary,
            replay_evidence_binding_status: replay_evidence_binding_status
                .expect("binding status parsed without reasons"),
            non_admission_reasons,
        };
        manifest.validate_parsed_json(object, &mut reasons);
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(manifest)
    }

    fn validate_parsed_json(
        &self,
        object: &serde_json::Map<String, serde_json::Value>,
        reasons: &mut Vec<String>,
    ) {
        if self.transcript_metadata.normalized_input_schema != self.problem_schema {
            reasons.push("manifest transcript normalized_input_schema mismatch".to_string());
        }
        if self.transcript_metadata.normalized_input_sha256 != self.problem_sha256 {
            reasons.push("manifest transcript normalized_input_sha256 mismatch".to_string());
        }
        if self.transcript_metadata.normalized_input_bytes != self.problem_bytes {
            reasons.push("manifest transcript normalized_input_bytes mismatch".to_string());
        }
        if self.transcript_metadata.result != self.result {
            reasons.push("manifest transcript result mismatch".to_string());
        }
        if self.transcript_metadata.proof_status != self.proof_status {
            reasons.push("manifest transcript proof_status mismatch".to_string());
        }
        if self.transcript_metadata.accepted_as_proof != self.accepted_as_proof {
            reasons.push("manifest transcript accepted_as_proof mismatch".to_string());
        }
        let mut recomputed = Vec::new();
        let expected_binding_status = replay_evidence_binding_status(
            self.replay_evidence.as_ref(),
            &self.problem_sha256,
            &self.options,
            &self.solver,
            &self.obligation_id,
            &self.result,
            &self.proof_status,
            &mut recomputed,
        );
        if self.checked_replay_summary.is_some() {
            recomputed.retain(|reason| !checked_replay_resolves_reason(reason));
        }
        if self.checked_replay_summary.is_some() {
            if self.replay_evidence_binding_status != "checked-summary-bound" {
                reasons.push(
                    "manifest checked summary is not marked checked-summary-bound".to_string(),
                );
            }
        } else if self.replay_evidence_binding_status != expected_binding_status {
            reasons.push(format!(
                "manifest replay_evidence_binding_status={} does not match recomputed {}",
                json_string(&self.replay_evidence_binding_status),
                json_string(&expected_binding_status)
            ));
        }
        if self.trust_full_verifier_admissible && self.checked_replay_summary.is_none() {
            reasons.push("manifest admitted without checked replay summary".to_string());
        }
        if let Some(summary) = &self.checked_replay_summary {
            let summary_reasons = self.checked_replay_summary_rejection_reasons(summary);
            for reason in summary_reasons {
                reasons.push(format!("manifest checked replay summary invalid:{reason}"));
            }
        }
        if let Some(admission) = object
            .get("admission")
            .and_then(serde_json::Value::as_object)
        {
            if let Some(cache_lookup_key_sha256) = admission
                .get("cache_lookup_key_sha256")
                .and_then(serde_json::Value::as_str)
            {
                if cache_lookup_key_sha256 != self.cache_lookup_key_sha256() {
                    reasons.push("manifest admission.cache_lookup_key_sha256 mismatch".to_string());
                }
            }
            if let Some(key) = admission
                .get("key")
                .and_then(serde_json::Value::as_object)
                .and_then(|key| key.get("sha256"))
                .and_then(serde_json::Value::as_str)
            {
                if key != self.admission_key_sha256() {
                    reasons.push("manifest admission.key.sha256 mismatch".to_string());
                }
            }
        }
    }

    fn refresh_replay_evidence_binding_status(&mut self) {
        self.non_admission_reasons
            .retain(|reason| !is_replay_evidence_binding_reason(reason));
        self.replay_evidence_binding_status = replay_evidence_binding_status(
            self.replay_evidence.as_ref(),
            &self.problem_sha256,
            &self.options,
            &self.solver,
            &self.obligation_id,
            &self.result,
            &self.proof_status,
            &mut self.non_admission_reasons,
        );
    }
}

type TranscriptMetadataParseResult = Result<ChcProofTranscriptMetadata, ChcProofEvidenceParseError>;

impl ChcProofTranscriptMetadata {
    /// Build metadata for a CHC result and the problem it was solved against.
    pub(crate) fn for_result(
        problem: &ChcProblem,
        result: &VerifiedChcResult,
        engine: impl Into<String>,
    ) -> Self {
        let normalized = normalized_chc_input(problem);
        let normalized_input_sha256 = sha256_hex(normalized.as_bytes());
        let normalized_input_bytes = normalized.len() as u64;

        let (
            result,
            proof_status,
            accepted_as_proof,
            replay_status,
            transcript_status,
            trust_reason,
            reason,
        ) = match result {
            VerifiedChcResult::Safe(_) => (
                "safe",
                "verified-invariant",
                true,
                "replay-artifacts-required",
                "metadata-only",
                Some("metadata_only_missing_checked_replay_artifacts".to_string()),
                None,
            ),
            VerifiedChcResult::Unsafe(_) => (
                "unsafe",
                "verified-counterexample",
                true,
                "replay-artifacts-required",
                "metadata-only",
                Some("metadata_only_missing_checked_replay_artifacts".to_string()),
                None,
            ),
            VerifiedChcResult::Unknown(marker) => {
                let reason = unknown_reason_label(marker.reason()).to_string();
                (
                    "unknown",
                    "non-proof",
                    false,
                    "not-replayable",
                    "non-proof",
                    Some(format!("result_is_non_proof:{reason}")),
                    Some(reason),
                )
            }
        };

        Self {
            schema: CHC_PROOF_TRANSCRIPT_SCHEMA,
            normalized_input_schema: NORMALIZED_CHC_INPUT_SCHEMA,
            normalized_input_sha256,
            normalized_input_bytes,
            engine: engine.into(),
            result: result.to_string(),
            proof_status: proof_status.to_string(),
            accepted_as_proof,
            replay_status: replay_status.to_string(),
            transcript_status: transcript_status.to_string(),
            trust_full_verifier_non_admission_reason: trust_reason,
            unknown_reason: reason,
            checked_replay: None,
        }
    }

    /// Upgrade metadata-only transcript metadata after a CHECKED replay pass.
    ///
    /// Fail-closed, crate-internal constructor: the ONLY way to obtain
    /// transcript metadata whose replay/transcript status is `replayable` and
    /// whose [`Self::trust_full_verifier_admissible`] derives to `true`. It
    /// consumes an evidence manifest that already admitted a validated
    /// [`ChcCheckedReplaySummary`] (via
    /// [`ChcProofEvidenceManifest::try_with_checked_replay_summary`], which
    /// re-validates every digest binding) and re-verifies the summary against
    /// the manifest here. Every precondition failure returns `None` so callers
    /// stay metadata-only rather than over-claiming replayability.
    pub(crate) fn for_checked_run(
        base: &ChcProofTranscriptMetadata,
        manifest: &ChcProofEvidenceManifest,
        checked_report_sha256: &str,
    ) -> Option<Self> {
        if !manifest.trust_full_verifier_admissible() {
            return None;
        }
        let summary = manifest.checked_replay_summary.as_ref()?;
        if !manifest
            .checked_replay_summary_rejection_reasons(summary)
            .is_empty()
        {
            return None;
        }
        if !base.accepted_as_proof || !matches!(base.result.as_str(), "safe" | "unsafe") {
            return None;
        }
        if summary.verdict != base.result {
            return None;
        }
        if manifest.result != base.result {
            return None;
        }
        if summary.problem.sha256 != base.normalized_input_sha256
            || manifest.problem_sha256 != base.normalized_input_sha256
        {
            return None;
        }
        if !is_lower_sha256(checked_report_sha256) {
            return None;
        }

        let transcript_uri = summary
            .run_log
            .path
            .as_deref()
            .filter(|path| !path.trim().is_empty())
            .map(str::to_string)
            .unwrap_or_else(|| format!("ay://chc/transcript/{}", summary.run_log.sha256));
        let mut upgraded = base.clone();
        upgraded.replay_status = "replayable".to_string();
        upgraded.transcript_status = "replayable".to_string();
        upgraded.trust_full_verifier_non_admission_reason = None;
        upgraded.checked_replay = Some(ChcCheckedReplayTranscriptDigests {
            transcript_uri,
            transcript_sha256: summary.run_log.sha256.clone(),
            replay_log_sha256: summary.replay_log.sha256.clone(),
            checked_report_sha256: checked_report_sha256.to_string(),
            summary_identity_sha256: summary.identity_sha256(),
        });
        Some(upgraded)
    }

    /// Render this metadata as a stable JSON object for report paths.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut map = serde_json::Map::new();
        map.insert("schema".to_string(), serde_json::json!(self.schema));
        map.insert("schema_version".to_string(), serde_json::json!(1));
        map.insert(
            "normalized_input_schema".to_string(),
            serde_json::json!(self.normalized_input_schema),
        );
        map.insert(
            "normalized_input_sha256".to_string(),
            serde_json::json!(self.normalized_input_sha256),
        );
        map.insert(
            "pdr_input_sha256".to_string(),
            serde_json::json!(self.pdr_input_sha256()),
        );
        map.insert(
            "normalized_input_bytes".to_string(),
            serde_json::json!(self.normalized_input_bytes),
        );
        map.insert("engine".to_string(), serde_json::json!(self.engine));
        map.insert("result".to_string(), serde_json::json!(self.result));
        map.insert(
            "proof_status".to_string(),
            serde_json::json!(self.proof_status),
        );
        map.insert(
            "accepted_as_proof".to_string(),
            serde_json::json!(self.accepted_as_proof),
        );
        map.insert(
            "trust_full_verifier_admissible".to_string(),
            serde_json::json!(self.trust_full_verifier_admissible()),
        );
        if let Some(reason) = &self.trust_full_verifier_non_admission_reason {
            map.insert(
                "trust_full_verifier_non_admission_reason".to_string(),
                serde_json::json!(reason),
            );
        }
        map.insert(
            "admission_policy".to_string(),
            serde_json::json!({
                "schema": CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA,
                "cache_hit_admission": if self.trust_full_verifier_admissible() {
                    "admit-checked-proof-evidence"
                } else {
                    "reject-non-admissible-proof-evidence"
                },
                "requires_checked_replay_artifacts": true,
            }),
        );
        match &self.checked_replay {
            Some(checked) => {
                map.insert(
                    "replay".to_string(),
                    serde_json::json!({
                        "status": self.replay_status,
                        "input_sha256": self.normalized_input_sha256,
                        "sha256": checked.replay_log_sha256,
                    }),
                );
                map.insert(
                    "transcript".to_string(),
                    serde_json::json!({
                        "status": self.transcript_status,
                        "metadata_only": false,
                        "uri": checked.transcript_uri,
                        "sha256": checked.transcript_sha256,
                    }),
                );
                map.insert(
                    "checked_report".to_string(),
                    serde_json::json!({
                        "sha256": checked.checked_report_sha256,
                        "summary_identity_sha256": checked.summary_identity_sha256,
                    }),
                );
            }
            None => {
                map.insert(
                    "replay".to_string(),
                    serde_json::json!({
                        "status": self.replay_status,
                        "input_sha256": self.normalized_input_sha256,
                    }),
                );
                map.insert(
                    "transcript".to_string(),
                    serde_json::json!({
                        "status": self.transcript_status,
                        "metadata_only": true,
                    }),
                );
            }
        }
        if let Some(reason) = &self.unknown_reason {
            map.insert("unknown_reason".to_string(), serde_json::json!(reason));
            map.insert("non_proof_reason".to_string(), serde_json::json!(reason));
        }
        serde_json::Value::Object(map)
    }

    /// Parse transcript metadata from a manifest/cache snapshot.
    pub(crate) fn from_json_value(value: &serde_json::Value) -> TranscriptMetadataParseResult {
        let mut reasons = Vec::new();
        let Some(object) = value.as_object() else {
            return Err(ChcProofEvidenceParseError::new(vec![
                "transcript_metadata is not an object".to_string(),
            ]));
        };
        expect_json_string(
            object,
            "schema",
            CHC_PROOF_TRANSCRIPT_SCHEMA,
            "transcript_metadata.schema",
            &mut reasons,
        );
        expect_json_u64(
            object,
            "schema_version",
            1,
            "transcript_metadata.schema_version",
            &mut reasons,
        );
        expect_json_string(
            object,
            "normalized_input_schema",
            NORMALIZED_CHC_INPUT_SCHEMA,
            "transcript_metadata.normalized_input_schema",
            &mut reasons,
        );
        let normalized_input_sha256 = sha256_string_field(
            object,
            "normalized_input_sha256",
            "transcript_metadata.normalized_input_sha256",
            &mut reasons,
        );
        let normalized_input_bytes = u64_field(
            object,
            "normalized_input_bytes",
            "transcript_metadata.normalized_input_bytes",
            &mut reasons,
        );
        let engine = string_field(object, "engine", "transcript_metadata.engine", &mut reasons);
        let result = string_field(object, "result", "transcript_metadata.result", &mut reasons);
        let proof_status = string_field(
            object,
            "proof_status",
            "transcript_metadata.proof_status",
            &mut reasons,
        );
        let accepted_as_proof = bool_field(
            object,
            "accepted_as_proof",
            "transcript_metadata.accepted_as_proof",
            &mut reasons,
        );
        let _reported_trust_full_verifier_admissible = optional_bool_field(
            object,
            "trust_full_verifier_admissible",
            "transcript_metadata.trust_full_verifier_admissible",
            &mut reasons,
        )
        .unwrap_or(false);
        let trust_full_verifier_non_admission_reason = optional_string_field(
            object,
            "trust_full_verifier_non_admission_reason",
            "transcript_metadata.trust_full_verifier_non_admission_reason",
            &mut reasons,
        );
        let unknown_reason = optional_string_field(
            object,
            "unknown_reason",
            "transcript_metadata.unknown_reason",
            &mut reasons,
        );
        let replay_status = object
            .get("replay")
            .and_then(serde_json::Value::as_object)
            .and_then(|replay| {
                string_field(
                    replay,
                    "status",
                    "transcript_metadata.replay.status",
                    &mut reasons,
                )
            });
        let transcript_status = object
            .get("transcript")
            .and_then(serde_json::Value::as_object)
            .and_then(|transcript| {
                string_field(
                    transcript,
                    "status",
                    "transcript_metadata.transcript.status",
                    &mut reasons,
                )
            });
        if !reasons.is_empty() {
            return Err(ChcProofEvidenceParseError::new(reasons));
        }
        Ok(Self {
            schema: CHC_PROOF_TRANSCRIPT_SCHEMA,
            normalized_input_schema: NORMALIZED_CHC_INPUT_SCHEMA,
            normalized_input_sha256: normalized_input_sha256
                .expect("normalized input hash parsed without reasons"),
            normalized_input_bytes: normalized_input_bytes
                .expect("normalized input bytes parsed without reasons"),
            engine: engine.expect("engine parsed without reasons"),
            result: result.expect("result parsed without reasons"),
            proof_status: proof_status.expect("proof status parsed without reasons"),
            accepted_as_proof: accepted_as_proof.expect("accepted flag parsed without reasons"),
            replay_status: replay_status.unwrap_or_else(|| "unknown".to_string()),
            transcript_status: transcript_status.unwrap_or_else(|| "unknown".to_string()),
            trust_full_verifier_non_admission_reason,
            unknown_reason,
            // Fail-closed: parsed/copied metadata can never carry checked
            // replay digests, so it can never claim admissibility.
            checked_replay: None,
        })
    }

    /// SHA-256 over the stable transcript identity used by admission keys.
    pub fn identity_sha256(&self) -> String {
        sha256_hex(self.identity_input().as_bytes())
    }

    fn identity_input(&self) -> String {
        let mut out = String::new();
        out.push_str(CHC_PROOF_TRANSCRIPT_SCHEMA);
        out.push('\n');
        out.push_str(&format!(
            "normalized_input_schema={}\n",
            json_string(self.normalized_input_schema)
        ));
        out.push_str(&format!(
            "normalized_input_sha256={}\n",
            self.normalized_input_sha256
        ));
        out.push_str(&format!(
            "normalized_input_bytes={}\n",
            self.normalized_input_bytes
        ));
        out.push_str(&format!("engine={}\n", json_string(&self.engine)));
        out.push_str(&format!("result={}\n", json_string(&self.result)));
        out.push_str(&format!(
            "proof_status={}\n",
            json_string(&self.proof_status)
        ));
        out.push_str(&format!("accepted_as_proof={}\n", self.accepted_as_proof));
        out.push_str(&format!(
            "replay_status={}\n",
            json_string(&self.replay_status)
        ));
        out.push_str(&format!(
            "transcript_status={}\n",
            json_string(&self.transcript_status)
        ));
        // Derived admissibility is intentionally EXCLUDED from the stable
        // transcript identity: it cannot survive serialization (parsed copies
        // are always non-admissible by design), and including the live getter
        // would make a producer-side checked transcript hash to a different
        // identity than its own parsed round-trip, breaking admission-key
        // stability. The `replayable` status strings above and the checked
        // summary's own identity (bound through the evidence manifest) already
        // capture the upgrade. This line is kept as a literal so every
        // pre-existing metadata identity remains byte-identical.
        out.push_str("trust_full_verifier_admissible=false\n");
        out.push_str(&format!(
            "trust_full_verifier_non_admission_reason={}\n",
            self.trust_full_verifier_non_admission_reason
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        out.push_str(&format!(
            "unknown_reason={}\n",
            self.unknown_reason
                .as_deref()
                .map(json_string)
                .unwrap_or_else(|| "none".to_string())
        ));
        out
    }
}

impl VerifiedChcResult {
    /// Build replay/proof metadata for this result.
    pub(crate) fn proof_transcript_metadata(
        &self,
        problem: &ChcProblem,
        engine: impl Into<String>,
    ) -> ChcProofTranscriptMetadata {
        ChcProofTranscriptMetadata::for_result(problem, self, engine)
    }
}

impl ChcProblem {
    /// Return the deterministic normalized CHC/PDR input text used for hashing.
    pub fn normalized_input(&self) -> String {
        normalized_chc_input(self)
    }

    /// Return the SHA-256 hash of [`Self::normalized_input`], lowercase hex.
    pub fn normalized_input_sha256(&self) -> String {
        normalized_chc_input_sha256(self)
    }
}

/// Return deterministic normalized CHC/PDR input text for replay binding.
pub fn normalized_chc_input(problem: &ChcProblem) -> String {
    let pred_names = canonical_predicate_names(problem);
    let mut out = String::new();
    out.push_str(NORMALIZED_CHC_INPUT_SCHEMA);
    out.push('\n');
    out.push_str(&format!(
        "fixedpoint={}\n",
        if problem.is_fixedpoint_format() {
            "true"
        } else {
            "false"
        }
    ));

    out.push_str("datatypes\n");
    for (name, constructors) in sorted_datatypes(problem) {
        let ctor_parts: Vec<_> = constructors
            .iter()
            .map(|(ctor, selectors)| {
                let selector_parts: Vec<_> = selectors
                    .iter()
                    .map(|(selector, sort)| {
                        format!("{}:{}", json_string(selector), normalized_sort(sort))
                    })
                    .collect();
                format!("{}({})", json_string(ctor), selector_parts.join(","))
            })
            .collect();
        out.push_str(&format!(
            "datatype {}={}\n",
            json_string(&name),
            ctor_parts.join("|")
        ));
    }

    out.push_str("actions\n");
    let mut actions: Vec<_> = problem
        .action_names()
        .iter()
        .map(|name| json_string(name))
        .collect();
    actions.sort();
    for action in actions {
        out.push_str(&format!("action {action}\n"));
    }

    out.push_str("predicates\n");
    let mut predicates: Vec<_> = problem
        .predicates()
        .iter()
        .map(|predicate| {
            let canonical = pred_names
                .get(&predicate.id.index())
                .cloned()
                .unwrap_or_else(|| fallback_predicate_name(predicate.id));
            let sorts: Vec<_> = predicate.arg_sorts.iter().map(normalized_sort).collect();
            format!(
                "predicate {canonical} name={} args=[{}]",
                json_string(&predicate.name),
                sorts.join(",")
            )
        })
        .collect();
    predicates.sort();
    for predicate in predicates {
        out.push_str(&predicate);
        out.push('\n');
    }

    out.push_str("clauses\n");
    let mut clauses: Vec<_> = problem
        .clauses()
        .iter()
        .map(|clause| normalized_clause(problem, clause, &pred_names))
        .collect();
    clauses.sort();
    for clause in clauses {
        out.push_str(&clause);
        out.push('\n');
    }

    out
}

/// Return SHA-256 of [`normalized_chc_input`], lowercase hex.
pub fn normalized_chc_input_sha256(problem: &ChcProblem) -> String {
    sha256_hex(normalized_chc_input(problem).as_bytes())
}

fn unknown_reason_label(reason: VerifiedUnknownReason) -> &'static str {
    reason.code()
}

fn unknown_limit_code(marker: &crate::VerifiedUnknownMarker) -> Option<&'static str> {
    match marker.reason() {
        VerifiedUnknownReason::BmcExhaustedSearch => Some("bmc_max_depth_reached"),
        VerifiedUnknownReason::BmcBudgetExhausted => Some("bmc_budget_exhausted"),
        VerifiedUnknownReason::Inconclusive | VerifiedUnknownReason::NotApplicable => None,
    }
}

fn chc_query_clause_index(problem: &ChcProblem) -> Option<usize> {
    problem
        .clauses()
        .iter()
        .position(|clause| matches!(clause.head, ClauseHead::False))
}

fn unsafe_trace_evidence(
    problem: &ChcProblem,
    cex: &crate::pdr::Counterexample,
) -> ChcUnsafeTraceEvidence {
    let steps: Vec<_> = cex
        .steps
        .iter()
        .enumerate()
        .map(|(step_index, step)| {
            let mut assignments: Vec<_> = step
                .assignments
                .iter()
                .map(|(name, value)| {
                    let (predicate_argument_index, sort) =
                        assignment_argument_metadata(problem, step.predicate, name);
                    ChcTraceAssignmentEvidence {
                        name: name.clone(),
                        predicate_argument_index,
                        sort,
                        value: *value,
                    }
                })
                .collect();
            assignments.sort_by(|left, right| left.name.cmp(&right.name));

            ChcTraceStepEvidence {
                step_index: usize_to_u64(step_index),
                predicate_id: usize_to_u64(step.predicate.index()),
                predicate_name: problem
                    .get_predicate(step.predicate)
                    .map(|predicate| predicate.name.clone()),
                action_id: step
                    .action_id
                    .map(|action_id| usize_to_u64(action_id.index())),
                action_name: step
                    .action_id
                    .and_then(|action_id| problem.action_name(action_id))
                    .map(str::to_string),
                clause_index: step.clause_index.map(usize_to_u64),
                assignments,
            }
        })
        .collect();

    ChcUnsafeTraceEvidence {
        status: "validated_counterexample".to_string(),
        step_count: usize_to_u64(steps.len()),
        steps,
    }
}

fn bmc_trace_assignment_encoding_rejection(
    assignment: &ChcTraceAssignmentEvidence,
) -> Option<ChcBmcUnsafeTraceAssignmentCompletenessReason> {
    let Some(sort) = assignment.sort.as_deref() else {
        return Some(ChcBmcUnsafeTraceAssignmentCompletenessReason::UnsupportedSortEncoding);
    };
    match sort {
        "Bool" => {
            if matches!(assignment.value, 0 | 1) {
                None
            } else {
                Some(ChcBmcUnsafeTraceAssignmentCompletenessReason::ValueOutOfRange)
            }
        }
        "Int" => None,
        sort => match parse_normalized_bitvec_sort_width(sort) {
            Some(width) => bmc_bitvec_value_rejection(width, assignment.value),
            None => Some(ChcBmcUnsafeTraceAssignmentCompletenessReason::UnsupportedSortEncoding),
        },
    }
}

fn parse_normalized_bitvec_sort_width(sort: &str) -> Option<u32> {
    let width = sort
        .strip_prefix("BitVec(")?
        .strip_suffix(')')?
        .parse()
        .ok()?;
    Some(width)
}

fn bmc_bitvec_value_rejection(
    width: u32,
    value: i64,
) -> Option<ChcBmcUnsafeTraceAssignmentCompletenessReason> {
    if value < 0 || width == 0 {
        return Some(ChcBmcUnsafeTraceAssignmentCompletenessReason::ValueOutOfRange);
    }
    if width < 63 {
        let max_value = (1_i128 << width) - 1;
        if i128::from(value) > max_value {
            return Some(ChcBmcUnsafeTraceAssignmentCompletenessReason::ValueOutOfRange);
        }
    }
    None
}

fn assignment_argument_metadata(
    problem: &ChcProblem,
    predicate_id: PredicateId,
    name: &str,
) -> (Option<u64>, Option<String>) {
    let Some(predicate) = problem.get_predicate(predicate_id) else {
        return (None, None);
    };
    for (argument_index, sort) in predicate.arg_sorts.iter().enumerate() {
        if crate::lemma_hints::canonical_var_name(predicate_id, argument_index) == name {
            return (
                Some(usize_to_u64(argument_index)),
                Some(normalized_sort(sort)),
            );
        }
    }
    (None, None)
}

fn chc_backend_code(engine: &str) -> String {
    let mut normalized = String::with_capacity(engine.len());
    let mut last_was_separator = false;
    for byte in engine.bytes() {
        if byte.is_ascii_alphanumeric() {
            normalized.push(byte.to_ascii_lowercase() as char);
            last_was_separator = false;
        } else if !last_was_separator {
            normalized.push('_');
            last_was_separator = true;
        }
    }
    while normalized.ends_with('_') {
        normalized.pop();
    }
    if normalized.is_empty() {
        "ay_chc_unknown".to_string()
    } else {
        format!("ay_chc_{normalized}")
    }
}

fn usize_to_u64(value: usize) -> u64 {
    value.try_into().unwrap_or(u64::MAX)
}

fn result_label(result: &VerifiedChcResult) -> &'static str {
    match result {
        VerifiedChcResult::Safe(_) => "safe",
        VerifiedChcResult::Unsafe(_) => "unsafe",
        VerifiedChcResult::Unknown(_) => "unknown",
    }
}

fn proof_status_label(result: &VerifiedChcResult) -> &'static str {
    match result {
        VerifiedChcResult::Safe(_) => "verified-invariant",
        VerifiedChcResult::Unsafe(_) => "verified-counterexample",
        VerifiedChcResult::Unknown(_) => "non-proof",
    }
}

fn duration_millis_u64(duration: Duration) -> u64 {
    duration.as_millis().try_into().unwrap_or(u64::MAX)
}

fn replay_evidence_binding_status(
    evidence: Option<&ChcReplayEvidence>,
    problem_sha256: &str,
    options: &ChcProofEvidenceOptions,
    solver: &ChcProofSolverIdentity,
    obligation_id: &str,
    result: &str,
    proof_status: &str,
    non_admission_reasons: &mut Vec<String>,
) -> String {
    let Some(evidence) = evidence else {
        non_admission_reasons.push("missing_replay_evidence".to_string());
        non_admission_reasons.push("missing_solver_transcript_artifact".to_string());
        non_admission_reasons.push("missing_proof_artifact".to_string());
        non_admission_reasons.push("missing_checked_replay_report".to_string());
        return "missing".to_string();
    };

    let mut mismatched = false;
    if evidence.problem_sha256 != problem_sha256 {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_problem_hash_mismatch".to_string());
    }
    if evidence.options_sha256 != options.identity_sha256() {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_options_hash_mismatch".to_string());
    }
    if evidence.solver_identity_sha256 != solver.identity_sha256() {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_solver_identity_mismatch".to_string());
    }
    if evidence.obligation_id != obligation_id {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_obligation_id_mismatch".to_string());
    }
    if evidence.result != result {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_result_mismatch".to_string());
    }
    if evidence.proof_status != proof_status {
        mismatched = true;
        non_admission_reasons.push("replay_evidence_proof_status_mismatch".to_string());
    }
    match &evidence.solver_transcript {
        Some(artifact) => {
            mismatched |= reject_wrong_replay_evidence_role(
                "solver_transcript",
                artifact,
                "solver-transcript",
                non_admission_reasons,
            );
        }
        None => non_admission_reasons.push("missing_solver_transcript_artifact".to_string()),
    }
    match &evidence.proof {
        Some(artifact) => {
            mismatched |= reject_wrong_replay_evidence_role(
                "proof",
                artifact,
                "proof-certificate",
                non_admission_reasons,
            );
        }
        None => non_admission_reasons.push("missing_proof_artifact".to_string()),
    }
    match &evidence.replay_report {
        Some(artifact) => {
            mismatched |= reject_wrong_replay_evidence_role(
                "replay_report",
                artifact,
                "replay-report",
                non_admission_reasons,
            );
        }
        None => non_admission_reasons.push("missing_checked_replay_report".to_string()),
    }
    if let Some(artifact) = &evidence.replay_log {
        mismatched |= reject_wrong_replay_evidence_role(
            "replay_log",
            artifact,
            "replay-log",
            non_admission_reasons,
        );
    }
    if let Some(artifact) = &evidence.checked_proof_report {
        mismatched |= reject_wrong_replay_evidence_role(
            "checked_proof_report",
            artifact,
            "checked-proof-report",
            non_admission_reasons,
        );
    }
    if let Some(artifact) = &evidence.invariant_model {
        mismatched |= reject_wrong_replay_evidence_role(
            "invariant_model",
            artifact,
            "invariant-model",
            non_admission_reasons,
        );
        if result != "safe" {
            mismatched = true;
            non_admission_reasons.push("invariant_model_artifact_requires_safe_result".to_string());
        }
    }
    if let Some(artifact) = &evidence.counterexample {
        mismatched |= reject_wrong_replay_evidence_role(
            "counterexample",
            artifact,
            "counterexample",
            non_admission_reasons,
        );
        if result != "unsafe" {
            mismatched = true;
            non_admission_reasons
                .push("counterexample_artifact_requires_unsafe_result".to_string());
        }
    }
    if evidence.replay_obligations.is_empty() {
        non_admission_reasons.push("missing_replay_obligation_artifacts".to_string());
    }
    for (index, artifact) in evidence.replay_obligations.iter().enumerate() {
        mismatched |= reject_wrong_replay_evidence_role(
            &format!("replay_obligation[{index}]"),
            &artifact.query,
            "replay-obligation",
            non_admission_reasons,
        );
    }

    if mismatched {
        "mismatched".to_string()
    } else {
        "hash-bound-unchecked".to_string()
    }
}

fn reject_wrong_replay_evidence_role(
    label: &str,
    artifact: &ChcProofArtifactDigest,
    expected_role: &str,
    non_admission_reasons: &mut Vec<String>,
) -> bool {
    if artifact.role == expected_role {
        return false;
    }
    non_admission_reasons.push(format!(
        "{label}_artifact_role_mismatch:expected={},actual={}",
        json_string(expected_role),
        json_string(&artifact.role)
    ));
    true
}

fn checked_replay_summary_rejection_reasons(
    manifest: &ChcProofEvidenceManifest,
    summary: &ChcCheckedReplaySummary,
) -> Vec<String> {
    let mut reasons = Vec::new();
    if !manifest.accepted_as_proof {
        reasons.push("manifest_result_is_non_proof".to_string());
    }
    if !matches!(manifest.result.as_str(), "safe" | "unsafe") {
        reasons.push(format!(
            "checked_replay_admission_requires_proof_result:{}",
            manifest.result
        ));
    }
    if manifest.replay_evidence.is_none() {
        reasons.push("manifest_replay_evidence is missing".to_string());
    }
    for reason in &manifest.non_admission_reasons {
        if !checked_replay_resolves_reason(reason) {
            reasons.push(format!("unresolved_manifest_non_admission_reason:{reason}"));
        }
    }

    validate_checked_replay_summary_status(summary, &mut reasons);
    validate_checked_replay_manifest_binding(manifest, summary, &mut reasons);
    validate_checked_replay_artifacts(manifest, summary, &mut reasons);
    validate_checked_replay_obligations(manifest, summary, &mut reasons);
    reasons
}

fn validate_checked_replay_summary_status(
    summary: &ChcCheckedReplaySummary,
    reasons: &mut Vec<String>,
) {
    if summary.status != "pass" {
        reasons.push(format!(
            "summary.status={}, expected 'pass'",
            json_string(&summary.status)
        ));
    }
    if summary.surface != "CHC certificates" {
        reasons.push(format!(
            "summary.surface={}, expected 'CHC certificates'",
            json_string(&summary.surface)
        ));
    }
    if summary
        .failure_kind
        .as_deref()
        .is_some_and(|failure_kind| !failure_kind.is_empty())
    {
        reasons.push(format!(
            "failure_kind={}",
            json_string(summary.failure_kind.as_deref().unwrap_or_default())
        ));
    }
    if summary.diagnostic_only {
        reasons.push("diagnostic_only is true".to_string());
    }
    if !matches!(summary.verdict.as_str(), "safe" | "unsafe") {
        reasons.push(format!(
            "checked_replay_verdict={}, expected 'safe' or 'unsafe'",
            json_string(&summary.verdict)
        ));
    }
    if summary.checker.name.is_empty() {
        reasons.push("checker.name is missing".to_string());
    }
    if summary.checker.version.is_empty() {
        reasons.push("checker.version is missing".to_string());
    }
    // A checked replay is normally performed by an external checker process.
    // The single sanctioned non-external checker is ay's own in-process
    // checked-replay pass (`ay-chc-replay`), which re-executes every
    // digest-bound obligation query on a fresh SMT context independent of the
    // solving run. Any other non-external checker identity stays rejected.
    if !summary.checker.external && summary.checker.name != CHC_IN_PROCESS_REPLAY_CHECKER_NAME {
        reasons.push("checker.external is not true".to_string());
    }
    if summary.command.is_empty() {
        reasons.push("command is missing".to_string());
    }
    summary.result.validate_pass("result", reasons);
    if !summary.errors.is_empty() {
        reasons.push(format!("errors is not empty: {:?}", summary.errors));
    }
}

fn validate_checked_replay_manifest_binding(
    manifest: &ChcProofEvidenceManifest,
    summary: &ChcCheckedReplaySummary,
    reasons: &mut Vec<String>,
) {
    let expected = manifest.checked_replay_manifest_binding();
    compare_binding_string(
        "manifest_binding.evidence_manifest_schema",
        &summary.manifest_binding.evidence_manifest_schema,
        &expected.evidence_manifest_schema,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.problem_sha256",
        &summary.manifest_binding.problem_sha256,
        &expected.problem_sha256,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.options_sha256",
        &summary.manifest_binding.options_sha256,
        &expected.options_sha256,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.solver_identity_sha256",
        &summary.manifest_binding.solver_identity_sha256,
        &expected.solver_identity_sha256,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.obligation_id",
        &summary.manifest_binding.obligation_id,
        &expected.obligation_id,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.result",
        &summary.manifest_binding.result,
        &expected.result,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.proof_status",
        &summary.manifest_binding.proof_status,
        &expected.proof_status,
        reasons,
    );
    compare_binding_string(
        "manifest_binding.precheck_admission_key_sha256",
        &summary.manifest_binding.precheck_admission_key_sha256,
        &expected.precheck_admission_key_sha256,
        reasons,
    );
    compare_binding_option(
        "manifest_binding.replay_evidence_sha256",
        &summary.manifest_binding.replay_evidence_sha256,
        &expected.replay_evidence_sha256,
        reasons,
    );
    compare_binding_option(
        "manifest_binding.solver_transcript_sha256",
        &summary.manifest_binding.solver_transcript_sha256,
        &expected.solver_transcript_sha256,
        reasons,
    );
    compare_binding_option(
        "manifest_binding.proof_artifact_sha256",
        &summary.manifest_binding.proof_artifact_sha256,
        &expected.proof_artifact_sha256,
        reasons,
    );
    compare_binding_option(
        "manifest_binding.replay_report_sha256",
        &summary.manifest_binding.replay_report_sha256,
        &expected.replay_report_sha256,
        reasons,
    );
    let mut actual_obligations = summary
        .manifest_binding
        .replay_obligation_query_sha256
        .clone();
    let mut expected_obligations = expected.replay_obligation_query_sha256;
    actual_obligations.sort();
    expected_obligations.sort();
    if actual_obligations != expected_obligations {
        reasons.push(format!(
            "manifest_binding.replay_obligation_query_sha256={actual_obligations:?} does not match manifest {expected_obligations:?}"
        ));
    }
    let mut actual_obligation_identities = summary
        .manifest_binding
        .replay_obligation_identity_sha256
        .clone();
    let mut expected_obligation_identities = expected.replay_obligation_identity_sha256;
    actual_obligation_identities.sort();
    expected_obligation_identities.sort();
    if actual_obligation_identities != expected_obligation_identities {
        reasons.push(format!(
            "manifest_binding.replay_obligation_identity_sha256={actual_obligation_identities:?} does not match manifest {expected_obligation_identities:?}"
        ));
    }
    if summary.verdict != manifest.result {
        reasons.push(format!(
            "checked_replay_verdict={} does not match manifest result={}",
            json_string(&summary.verdict),
            json_string(&manifest.result)
        ));
    }
}

fn validate_checked_replay_artifacts(
    manifest: &ChcProofEvidenceManifest,
    summary: &ChcCheckedReplaySummary,
    reasons: &mut Vec<String>,
) {
    validate_artifact_digest("problem", &summary.problem, "problem", reasons);
    validate_artifact_digest(
        "certificate",
        &summary.certificate,
        "proof-certificate",
        reasons,
    );
    validate_artifact_digest("run_log", &summary.run_log, "solver-transcript", reasons);
    validate_artifact_digest("replay_log", &summary.replay_log, "replay-report", reasons);

    let expected = manifest.checked_replay_manifest_binding();
    compare_artifact_to_expected(
        "problem.sha256",
        &summary.problem.sha256,
        Some(&manifest.problem_sha256),
        "manifest problem_sha256",
        reasons,
    );
    compare_artifact_bytes_to_expected(
        "problem.bytes",
        summary.problem.bytes,
        Some(manifest.problem_bytes),
        "manifest problem_bytes",
        reasons,
    );
    compare_artifact_to_expected(
        "run_log.sha256",
        &summary.run_log.sha256,
        expected.solver_transcript_sha256.as_deref(),
        "manifest solver_transcript_sha256",
        reasons,
    );
    compare_artifact_to_expected(
        "certificate.sha256",
        &summary.certificate.sha256,
        expected.proof_artifact_sha256.as_deref(),
        "manifest proof_artifact_sha256",
        reasons,
    );
    compare_artifact_to_expected(
        "replay_log.sha256",
        &summary.replay_log.sha256,
        expected.replay_report_sha256.as_deref(),
        "manifest replay_report_sha256",
        reasons,
    );

    if let Some(evidence) = &manifest.replay_evidence {
        compare_artifact_bytes_to_expected(
            "run_log.bytes",
            summary.run_log.bytes,
            evidence
                .solver_transcript
                .as_ref()
                .map(|artifact| artifact.bytes),
            "manifest solver_transcript_bytes",
            reasons,
        );
        compare_artifact_bytes_to_expected(
            "certificate.bytes",
            summary.certificate.bytes,
            evidence.proof.as_ref().map(|artifact| artifact.bytes),
            "manifest proof_artifact_bytes",
            reasons,
        );
        compare_artifact_bytes_to_expected(
            "replay_log.bytes",
            summary.replay_log.bytes,
            evidence
                .replay_report
                .as_ref()
                .map(|artifact| artifact.bytes),
            "manifest replay_report_bytes",
            reasons,
        );
    }
}

fn validate_checked_replay_obligations(
    manifest: &ChcProofEvidenceManifest,
    summary: &ChcCheckedReplaySummary,
    reasons: &mut Vec<String>,
) {
    if summary.obligations.is_empty() {
        reasons.push("obligations is empty".to_string());
        return;
    }
    let allowed_kinds: &[ChcReplayObligationKind] = match manifest.result.as_str() {
        "safe" => &[
            ChcReplayObligationKind::Initiation,
            ChcReplayObligationKind::Consecution,
            ChcReplayObligationKind::Safety,
        ],
        "unsafe" => &[ChcReplayObligationKind::TraceValidity],
        _ => &[],
    };
    // Required kinds per proof class. A safe proof must ALWAYS discharge a
    // Safety obligation, and an unsafe proof must always discharge
    // trace-validity. Initiation/Consecution are required exactly when the
    // manifest's hash-bound replay evidence carries an obligation of that
    // kind: loop-free clause systems have no consecution clauses, and
    // acyclic-exhaustion certificates replay through synthesized Safety
    // obligations only — demanding kinds the evidence provably has no
    // obligation for would make those genuine proofs unadmittable while
    // adding no checking power (the exact query/kind digest-set matches below
    // already force the summary to cover every evidence obligation).
    let mut expected_kinds: Vec<ChcReplayObligationKind> = match manifest.result.as_str() {
        "safe" => vec![ChcReplayObligationKind::Safety],
        "unsafe" => vec![ChcReplayObligationKind::TraceValidity],
        _ => Vec::new(),
    };
    if let Some(evidence) = &manifest.replay_evidence {
        for artifact in &evidence.replay_obligations {
            if allowed_kinds.contains(&artifact.kind)
                && !expected_kinds.iter().any(|kind| kind == &artifact.kind)
            {
                expected_kinds.push(artifact.kind);
            }
        }
    }
    let mut seen_kinds = Vec::new();
    for (index, obligation) in summary.obligations.iter().enumerate() {
        let label = format!("obligations[{index}]");
        if obligation.name.is_empty() {
            reasons.push(format!("{label}.name is missing"));
        }
        if allowed_kinds.contains(&obligation.kind) {
            if !seen_kinds.iter().any(|seen| seen == &obligation.kind) {
                seen_kinds.push(obligation.kind);
            }
        } else {
            reasons.push(format!(
                "{label}.kind={} is not expected for {} CHC replay",
                json_string(obligation.kind.as_str()),
                manifest.result
            ));
        }
        if obligation.checker_command.is_empty() {
            reasons.push(format!("{label}.checker_command is missing"));
        }
        validate_artifact_digest(
            &format!("{label}.query"),
            &obligation.query,
            "replay-obligation",
            reasons,
        );
        obligation
            .result
            .validate_pass(&format!("{label}.result"), reasons);
    }

    let missing = expected_kinds
        .iter()
        .copied()
        .filter(|kind| !seen_kinds.iter().any(|seen| seen == kind))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        let missing = missing
            .iter()
            .map(|kind| kind.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        reasons.push(format!("missing CHC replay obligation kinds: {}", missing));
    }

    let mut actual_hashes = summary
        .obligations
        .iter()
        .map(|obligation| obligation.query.sha256.clone())
        .collect::<Vec<_>>();
    actual_hashes.sort();
    let expected_hashes = manifest
        .replay_evidence
        .as_ref()
        .map(replay_obligation_query_hashes)
        .unwrap_or_default();
    if actual_hashes != expected_hashes {
        reasons.push(format!(
            "checked_replay_obligation_query_sha256={actual_hashes:?} does not match manifest {expected_hashes:?}"
        ));
    }

    let mut actual_descriptors = summary
        .obligations
        .iter()
        .map(|obligation| (obligation.query.sha256.clone(), obligation.query.bytes))
        .collect::<Vec<_>>();
    actual_descriptors.sort();
    let mut expected_descriptors = manifest
        .replay_evidence
        .as_ref()
        .map(|evidence| {
            evidence
                .replay_obligations
                .iter()
                .map(|artifact| (artifact.query.sha256.clone(), artifact.query.bytes))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    expected_descriptors.sort();
    if actual_descriptors != expected_descriptors {
        reasons.push(format!(
            "checked_replay_obligation_query_descriptors={actual_descriptors:?} does not match manifest {expected_descriptors:?}"
        ));
    }

    let mut actual_kind_descriptors = summary
        .obligations
        .iter()
        .map(|obligation| {
            (
                obligation.kind.as_str().to_string(),
                obligation.query.sha256.clone(),
                obligation.query.bytes,
            )
        })
        .collect::<Vec<_>>();
    actual_kind_descriptors.sort();
    let mut expected_kind_descriptors = manifest
        .replay_evidence
        .as_ref()
        .map(|evidence| {
            evidence
                .replay_obligations
                .iter()
                .map(|artifact| {
                    (
                        artifact.kind.as_str().to_string(),
                        artifact.query.sha256.clone(),
                        artifact.query.bytes,
                    )
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    expected_kind_descriptors.sort();
    if actual_kind_descriptors != expected_kind_descriptors {
        reasons.push(format!(
            "checked_replay_obligation_kind_query_descriptors={actual_kind_descriptors:?} does not match manifest {expected_kind_descriptors:?}"
        ));
    }

    let actual_identities = checked_obligation_artifact_identity_hashes(&summary.obligations);
    let expected_identities = manifest
        .replay_evidence
        .as_ref()
        .map(replay_obligation_identity_hashes)
        .unwrap_or_default();
    if actual_identities != expected_identities {
        reasons.push(format!(
            "checked_replay_obligation_identity_sha256={actual_identities:?} does not match manifest {expected_identities:?}"
        ));
    }
}

fn checked_replay_resolves_reason(reason: &str) -> bool {
    matches!(
        reason,
        "metadata_only_missing_checked_replay_artifacts"
            | "missing_solver_transcript_artifact"
            | "missing_proof_artifact"
            | "missing_checked_replay_report"
            | "missing_replay_obligation_artifacts"
    )
}

fn is_replay_evidence_binding_reason(reason: &str) -> bool {
    matches!(
        reason,
        "missing_replay_evidence"
            | "missing_solver_transcript_artifact"
            | "missing_proof_artifact"
            | "missing_checked_replay_report"
            | "missing_replay_obligation_artifacts"
            | "invariant_model_artifact_requires_safe_result"
            | "counterexample_artifact_requires_unsafe_result"
    ) || reason.starts_with("replay_evidence_")
        || reason.contains("_artifact_role_mismatch")
}

fn replay_obligation_query_hashes(evidence: &ChcReplayEvidence) -> Vec<String> {
    let mut hashes = evidence
        .replay_obligations
        .iter()
        .map(|artifact| artifact.query.sha256.clone())
        .collect::<Vec<_>>();
    hashes.sort();
    hashes
}

fn replay_obligation_identity_hashes(evidence: &ChcReplayEvidence) -> Vec<String> {
    let mut hashes = evidence
        .replay_obligations
        .iter()
        .map(ChcReplayObligationArtifact::identity_sha256)
        .collect::<Vec<_>>();
    hashes.sort();
    hashes
}

fn checked_obligation_artifact_identity_hashes(
    obligations: &[ChcCheckedReplayObligation],
) -> Vec<String> {
    let mut hashes = obligations
        .iter()
        .map(|obligation| {
            ChcReplayObligationArtifact::new(obligation.kind, obligation.query.clone())
                .identity_sha256()
        })
        .collect::<Vec<_>>();
    hashes.sort();
    hashes
}

fn compare_binding_string(label: &str, actual: &str, expected: &str, reasons: &mut Vec<String>) {
    if actual != expected {
        reasons.push(format!(
            "{label}={} does not match manifest {}",
            json_string(actual),
            json_string(expected)
        ));
    }
}

fn compare_binding_option(
    label: &str,
    actual: &Option<String>,
    expected: &Option<String>,
    reasons: &mut Vec<String>,
) {
    if actual != expected {
        reasons.push(format!(
            "{label}={actual:?} does not match manifest {expected:?}"
        ));
    }
}

fn compare_artifact_to_expected(
    label: &str,
    actual: &str,
    expected: Option<&str>,
    expected_label: &str,
    reasons: &mut Vec<String>,
) {
    let Some(expected) = expected else {
        reasons.push(format!("{expected_label} is missing"));
        return;
    };
    if actual != expected {
        reasons.push(format!(
            "{label}={actual} does not match {expected_label}={expected}"
        ));
    }
}

fn compare_artifact_bytes_to_expected(
    label: &str,
    actual: u64,
    expected: Option<u64>,
    expected_label: &str,
    reasons: &mut Vec<String>,
) {
    let Some(expected) = expected else {
        reasons.push(format!("{expected_label} is missing"));
        return;
    };
    if actual != expected {
        reasons.push(format!(
            "{label}={actual} does not match {expected_label}={expected}"
        ));
    }
}

fn validate_artifact_digest(
    label: &str,
    artifact: &ChcProofArtifactDigest,
    expected_role: &str,
    reasons: &mut Vec<String>,
) {
    if artifact.role != expected_role {
        reasons.push(format!(
            "{label}.role={} does not match expected {}",
            json_string(&artifact.role),
            json_string(expected_role)
        ));
    }
    if !is_lower_sha256(&artifact.sha256) {
        reasons.push(format!("{label}.sha256 is not lowercase hex SHA-256"));
    }
}

fn canonical_predicate_names(problem: &ChcProblem) -> BTreeMap<usize, String> {
    let mut signatures: Vec<_> = problem
        .predicates()
        .iter()
        .map(|predicate| {
            let sorts: Vec<_> = predicate.arg_sorts.iter().map(normalized_sort).collect();
            (
                json_string(&predicate.name),
                sorts.join(","),
                predicate.id.index(),
            )
        })
        .collect();
    signatures.sort();

    signatures
        .into_iter()
        .enumerate()
        .map(|(idx, (_, _, original_idx))| (original_idx, format!("p{idx}")))
        .collect()
}

fn sorted_datatypes(problem: &ChcProblem) -> Vec<(String, Vec<(String, Vec<(String, ChcSort)>)>)> {
    let mut datatypes: Vec<_> = problem
        .datatype_defs()
        .iter()
        .map(|(name, constructors)| (name.clone(), constructors.clone()))
        .collect();
    datatypes.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
    datatypes
}

fn normalized_clause(
    problem: &ChcProblem,
    clause: &HornClause,
    pred_names: &BTreeMap<usize, String>,
) -> String {
    let mut body_predicates: Vec<_> = clause
        .body
        .predicates
        .iter()
        .map(|(pred, args)| normalized_predicate_app(*pred, args, pred_names))
        .collect();
    body_predicates.sort();

    let constraint = clause
        .body
        .constraint
        .as_ref()
        .map(|expr| normalized_expr(expr, pred_names))
        .unwrap_or_else(|| "true".to_string());
    let head = match &clause.head {
        ClauseHead::False => "false".to_string(),
        ClauseHead::Predicate(pred, args) => normalized_predicate_app(*pred, args, pred_names),
    };
    let action = clause
        .action_id
        .and_then(|action| problem.action_name(action).map(json_string))
        .unwrap_or_else(|| "none".to_string());

    format!(
        "clause action={action} body=[{}] constraint={constraint} head={head}",
        body_predicates.join(",")
    )
}

fn normalized_predicate_app(
    pred: PredicateId,
    args: &[ChcExpr],
    pred_names: &BTreeMap<usize, String>,
) -> String {
    let pred = pred_names
        .get(&pred.index())
        .cloned()
        .unwrap_or_else(|| fallback_predicate_name(pred));
    let args: Vec<_> = args
        .iter()
        .map(|arg| normalized_expr(arg, pred_names))
        .collect();
    format!("{pred}({})", args.join(","))
}

fn normalized_expr(expr: &ChcExpr, pred_names: &BTreeMap<usize, String>) -> String {
    match expr {
        ChcExpr::Bool(value) => format!("bool:{value}"),
        ChcExpr::Int(value) => format!("int:{value}"),
        ChcExpr::Real(numer, denom) => format!("real:{numer}/{denom}"),
        ChcExpr::BitVec(value, width) => format!("bv{width}:{value}"),
        ChcExpr::Var(var) => {
            format!(
                "var:{}:{}",
                json_string(&var.name),
                normalized_sort(&var.sort)
            )
        }
        ChcExpr::Op(op, args) => {
            let mut children: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            if is_commutative_op(*op) {
                children.sort();
            }
            format!("op:{op:?}({})", children.join(","))
        }
        ChcExpr::PredicateApp(name, pred, args) => {
            let pred = pred_names
                .get(&pred.index())
                .cloned()
                .unwrap_or_else(|| fallback_predicate_name(*pred));
            let args: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            format!("pred-expr:{pred}:{}({})", json_string(name), args.join(","))
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            format!(
                "func:{}:{}({})",
                json_string(name),
                normalized_sort(sort),
                args.join(",")
            )
        }
        ChcExpr::ConstArrayMarker(sort) => {
            format!("const-array-marker:{}", normalized_sort(sort))
        }
        ChcExpr::IsTesterMarker(name) => format!("is-tester:{}", json_string(name)),
        ChcExpr::ConstArray(key_sort, value) => format!(
            "const-array:{}:{}",
            normalized_sort(key_sort),
            normalized_expr(value, pred_names)
        ),
    }
}

fn is_commutative_op(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::And
            | ChcOp::Or
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Mul
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::BvAdd
            | ChcOp::BvMul
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
    )
}

fn normalized_sort(sort: &ChcSort) -> String {
    match sort {
        ChcSort::Bool => "Bool".to_string(),
        ChcSort::Int => "Int".to_string(),
        ChcSort::Real => "Real".to_string(),
        ChcSort::BitVec(width) => format!("BitVec({width})"),
        ChcSort::Array(key, value) => {
            format!("Array({},{})", normalized_sort(key), normalized_sort(value))
        }
        ChcSort::Uninterpreted(name) => format!("Uninterpreted({})", json_string(name)),
        ChcSort::Datatype { name, constructors } => {
            let ctor_parts: Vec<_> = constructors
                .iter()
                .map(|constructor| {
                    let selectors: Vec<_> = constructor
                        .selectors
                        .iter()
                        .map(|selector| {
                            format!(
                                "{}:{}",
                                json_string(&selector.name),
                                normalized_sort(&selector.sort)
                            )
                        })
                        .collect();
                    format!(
                        "{}({})",
                        json_string(&constructor.name),
                        selectors.join(",")
                    )
                })
                .collect();
            format!("Datatype({};{})", json_string(name), ctor_parts.join("|"))
        }
    }
}

fn fallback_predicate_name(pred: PredicateId) -> String {
    format!("p?{}", pred.index())
}

fn string_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<String> {
    match object.get(key).and_then(serde_json::Value::as_str) {
        Some(value) if !value.is_empty() => Some(value.to_string()),
        _ => {
            reasons.push(format!("{label} is missing"));
            None
        }
    }
}

fn obligation_kind_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<ChcReplayObligationKind> {
    let value = string_field(object, key, label, reasons)?;
    match ChcReplayObligationKind::from_label(&value) {
        Some(kind) => Some(kind),
        None => {
            reasons.push(format!(
                "{label}={} is not a known CHC replay obligation kind",
                json_string(&value)
            ));
            None
        }
    }
}

fn optional_string_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<String> {
    match object.get(key) {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => match value.as_str() {
            Some(text) => Some(text.to_string()),
            None => {
                reasons.push(format!("{label} is not a string"));
                None
            }
        },
    }
}

fn bool_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<bool> {
    match object.get(key).and_then(serde_json::Value::as_bool) {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is missing"));
            None
        }
    }
}

fn optional_bool_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<bool> {
    match object.get(key) {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => match value.as_bool() {
            Some(flag) => Some(flag),
            None => {
                reasons.push(format!("{label} is not a bool"));
                None
            }
        },
    }
}

fn optional_u64_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<u64> {
    match object.get(key) {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => match value.as_u64() {
            Some(number) => Some(number),
            None => {
                reasons.push(format!("{label} is not an unsigned integer"));
                None
            }
        },
    }
}

fn i64_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<i64> {
    match object.get(key).and_then(serde_json::Value::as_i64) {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is missing"));
            None
        }
    }
}

fn u64_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<u64> {
    match object.get(key).and_then(serde_json::Value::as_u64) {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is missing"));
            None
        }
    }
}

fn sha256_string_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<String> {
    let value = string_field(object, key, label, reasons)?;
    if is_lower_sha256(&value) {
        Some(value)
    } else {
        reasons.push(format!("{label} is not lowercase hex SHA-256"));
        None
    }
}

fn optional_sha256_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<String> {
    let Some(value) = optional_string_field(object, key, label, reasons) else {
        return None;
    };
    if is_lower_sha256(&value) {
        Some(value)
    } else {
        reasons.push(format!("{label} is not lowercase hex SHA-256"));
        None
    }
}

fn sha256_string_array_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<Vec<String>> {
    let Some(values) = object.get(key).and_then(serde_json::Value::as_array) else {
        reasons.push(format!("{label} is missing"));
        return None;
    };
    let mut out = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let Some(text) = value.as_str() else {
            reasons.push(format!("{label}[{index}] is not a string"));
            continue;
        };
        if is_lower_sha256(text) {
            out.push(text.to_string());
        } else {
            reasons.push(format!("{label}[{index}] is not lowercase hex SHA-256"));
        }
    }
    Some(out)
}

fn string_vec_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Vec<String> {
    let Some(values) = object.get(key) else {
        return Vec::new();
    };
    let Some(values) = values.as_array() else {
        reasons.push(format!("{label} is not an array"));
        return Vec::new();
    };
    let mut out = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        match value.as_str() {
            Some(text) => out.push(text.to_string()),
            None => reasons.push(format!("{label}[{index}] is not a string")),
        }
    }
    out
}

fn string_array_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Vec<String> {
    let Some(values) = object.get(key).and_then(serde_json::Value::as_array) else {
        reasons.push(format!("{label} is missing"));
        return Vec::new();
    };
    let mut out = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        match value.as_str() {
            Some(text) => out.push(text.to_string()),
            None => reasons.push(format!("{label}[{index}] is not a string")),
        }
    }
    out
}

fn artifact_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    role: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<ChcProofArtifactDigest> {
    let Some(value) = object.get(key) else {
        reasons.push(format!("{label} is missing"));
        return None;
    };
    artifact_from_json_value(value, role, label, reasons)
}

fn optional_artifact_field(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    role: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<ChcProofArtifactDigest> {
    match object.get(key) {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => artifact_from_json_value(value, role, label, reasons),
    }
}

fn artifact_from_json_value(
    value: &serde_json::Value,
    role: &str,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<ChcProofArtifactDigest> {
    let Some(row) = value.as_object() else {
        reasons.push(format!("{label} is missing"));
        return None;
    };
    expect_json_string(
        row,
        "schema",
        CHC_PROOF_ARTIFACT_DIGEST_SCHEMA,
        &format!("{label}.schema"),
        reasons,
    );
    expect_json_u64(
        row,
        "schema_version",
        1,
        &format!("{label}.schema_version"),
        reasons,
    );
    let sha256 = sha256_string_field(row, "sha256", &format!("{label}.sha256"), reasons)?;
    let bytes = artifact_bytes_field(row, label, reasons)?;
    let artifact_role = string_field(row, "role", &format!("{label}.role"), reasons)?;
    if artifact_role != role {
        reasons.push(format!(
            "{label}.role={} does not match expected {}",
            json_string(&artifact_role),
            json_string(role)
        ));
        return None;
    }
    let mut artifact = ChcProofArtifactDigest::from_sha256(artifact_role, sha256, bytes);
    if let Some(path) = optional_string_field(row, "path", &format!("{label}.path"), reasons) {
        artifact = artifact.with_path(path);
    }
    check_optional_identity_sha256(
        row,
        "identity_sha256",
        &format!("{label}.identity_sha256"),
        &artifact.identity_sha256(),
        reasons,
    );
    Some(artifact)
}

fn replay_obligations_from_json(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Vec<ChcReplayObligationArtifact> {
    let Some(value) = value else {
        reasons.push("replay_evidence.replay_obligations is missing".to_string());
        return Vec::new();
    };
    let Some(rows) = value.as_array() else {
        reasons.push("replay_evidence.replay_obligations is not an array".to_string());
        return Vec::new();
    };
    let mut obligations = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        let label = format!("replay_evidence.replay_obligations[{index}]");
        let Some(object) = row.as_object() else {
            reasons.push(format!("{label} is not an object"));
            continue;
        };
        let Some(kind) = obligation_kind_field(object, "kind", &format!("{label}.kind"), reasons)
        else {
            continue;
        };
        let Some(query) = artifact_from_json_value(row, "replay-obligation", &label, reasons)
        else {
            continue;
        };
        let obligation = ChcReplayObligationArtifact::new(kind, query);
        check_optional_identity_sha256(
            object,
            "obligation_identity_sha256",
            &format!("{label}.obligation_identity_sha256"),
            &obligation.identity_sha256(),
            reasons,
        );
        obligations.push(obligation);
    }
    obligations
}

fn parse_solver_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcProofSolverIdentity> {
    match value {
        Some(value) => match ChcProofSolverIdentity::from_json_value(value) {
            Ok(solver) => Some(solver),
            Err(error) => {
                reasons.extend(error.reasons().iter().cloned());
                None
            }
        },
        None => {
            reasons.push("solver is missing".to_string());
            None
        }
    }
}

fn parse_options_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcProofEvidenceOptions> {
    match value {
        Some(value) => match ChcProofEvidenceOptions::from_json_value(value) {
            Ok(options) => Some(options),
            Err(error) => {
                reasons.extend(error.reasons().iter().cloned());
                None
            }
        },
        None => {
            reasons.push("options is missing".to_string());
            None
        }
    }
}

fn parse_replay_evidence_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcReplayEvidence> {
    match value {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => match ChcReplayEvidence::from_json_value(value) {
            Ok(evidence) => Some(evidence),
            Err(error) => {
                reasons.extend(error.reasons().iter().cloned());
                None
            }
        },
    }
}

fn parse_checked_replay_summary_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcCheckedReplaySummary> {
    match value {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => match ChcCheckedReplaySummary::from_json_value(value) {
            Ok(summary) => Some(summary),
            Err(error) => {
                reasons.extend(error.reasons().iter().cloned());
                None
            }
        },
    }
}

fn parse_transcript_metadata_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcProofTranscriptMetadata> {
    match value {
        Some(value) => match ChcProofTranscriptMetadata::from_json_value(value) {
            Ok(metadata) => Some(metadata),
            Err(error) => {
                reasons.extend(error.reasons().iter().cloned());
                None
            }
        },
        None => {
            reasons.push("transcript_metadata is missing".to_string());
            None
        }
    }
}

fn parse_cache_policy_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcProofQueryCacheAdmissionPolicy> {
    let Some(value) = value else {
        reasons.push("cache.policy is missing".to_string());
        return None;
    };
    let Some(object) = value.as_object() else {
        reasons.push("cache.policy is not an object".to_string());
        return None;
    };
    let policy = ChcProofQueryCacheAdmissionPolicy::trust_full_verifier();
    expect_json_string(
        object,
        "schema",
        CHC_PROOF_QUERY_CACHE_ADMISSION_POLICY_SCHEMA,
        "cache.policy.schema",
        reasons,
    );
    expect_json_u64(
        object,
        "schema_version",
        1,
        "cache.policy.schema_version",
        reasons,
    );
    check_optional_identity_sha256(
        object,
        "identity_sha256",
        "cache.policy.identity_sha256",
        &policy.identity_sha256(),
        reasons,
    );
    Some(policy)
}

fn parse_cache_metrics_field(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Option<ChcProofQueryCacheMetrics> {
    let Some(value) = value else {
        reasons.push("cache.metrics is missing".to_string());
        return None;
    };
    let Some(object) = value.as_object() else {
        reasons.push("cache.metrics is not an object".to_string());
        return None;
    };
    expect_json_string(
        object,
        "schema",
        CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA,
        "cache.metrics.schema",
        reasons,
    );
    expect_json_u64(
        object,
        "schema_version",
        1,
        "cache.metrics.schema_version",
        reasons,
    );
    Some(ChcProofQueryCacheMetrics {
        schema: CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA,
        lookups: u64_field(object, "lookups", "cache.metrics.lookups", reasons)?,
        hits: u64_field(object, "hits", "cache.metrics.hits", reasons)?,
        misses: u64_field(object, "misses", "cache.metrics.misses", reasons)?,
        stale: u64_field(object, "stale", "cache.metrics.stale", reasons)?,
        replay_failed: u64_field(
            object,
            "replay_failed",
            "cache.metrics.replay_failed",
            reasons,
        )?,
        rejected: u64_field(object, "rejected", "cache.metrics.rejected", reasons)?,
        insertions: u64_field(object, "insertions", "cache.metrics.insertions", reasons)?,
        evictions: u64_field(object, "evictions", "cache.metrics.evictions", reasons)?,
        entries: u64_field(object, "entries", "cache.metrics.entries", reasons)?,
    })
}

fn artifact_bytes_field(
    row: &serde_json::Map<String, serde_json::Value>,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<u64> {
    let bytes = row.get("bytes");
    let size_bytes = row.get("size_bytes");
    match (bytes, size_bytes) {
        (None, None) => {
            reasons.push(format!("{label}.bytes is missing"));
            None
        }
        (Some(value), None) => u64_json_field(value, &format!("{label}.bytes"), reasons),
        (None, Some(value)) => u64_json_field(value, &format!("{label}.size_bytes"), reasons),
        (Some(bytes), Some(size_bytes)) => {
            let bytes = u64_json_field(bytes, &format!("{label}.bytes"), reasons);
            let size_bytes = u64_json_field(size_bytes, &format!("{label}.size_bytes"), reasons);
            match (bytes, size_bytes) {
                (Some(bytes), Some(size_bytes)) if bytes == size_bytes => Some(bytes),
                (Some(bytes), Some(size_bytes)) => {
                    reasons.push(format!(
                        "{label}.bytes={bytes} does not match {label}.size_bytes={size_bytes}"
                    ));
                    None
                }
                _ => None,
            }
        }
    }
}

fn u64_json_field(
    value: &serde_json::Value,
    label: &str,
    reasons: &mut Vec<String>,
) -> Option<u64> {
    match value.as_u64() {
        Some(value) => Some(value),
        None => {
            reasons.push(format!("{label} is not an unsigned integer"));
            None
        }
    }
}

fn obligations_from_json(
    value: Option<&serde_json::Value>,
    reasons: &mut Vec<String>,
) -> Vec<ChcCheckedReplayObligation> {
    let Some(value) = value else {
        reasons.push("obligations is empty".to_string());
        return Vec::new();
    };
    let Some(rows) = value.as_array() else {
        reasons.push("obligations is not an array".to_string());
        return Vec::new();
    };
    rows.iter()
        .enumerate()
        .filter_map(|(index, row)| ChcCheckedReplayObligation::from_json_value(row, index, reasons))
        .collect()
}

fn expect_json_string(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    expected: &str,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match object.get(key).and_then(serde_json::Value::as_str) {
        Some(actual) if actual == expected => {}
        Some(actual) => reasons.push(format!(
            "{label}={} does not match expected {}",
            json_string(actual),
            json_string(expected)
        )),
        None => reasons.push(format!("{label} is missing")),
    }
}

fn expect_json_u64(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    expected: u64,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match object.get(key).and_then(serde_json::Value::as_u64) {
        Some(actual) if actual == expected => {}
        Some(actual) => reasons.push(format!(
            "{label}={actual} does not match expected {expected}"
        )),
        None => reasons.push(format!("{label} is missing")),
    }
}

fn check_optional_identity_sha256(
    object: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    label: &str,
    expected: &str,
    reasons: &mut Vec<String>,
) {
    let Some(value) = object.get(key) else {
        return;
    };
    if value.is_null() {
        return;
    }
    let Some(actual) = value.as_str() else {
        reasons.push(format!("{label} is not a string"));
        return;
    };
    if !is_lower_sha256(actual) {
        reasons.push(format!("{label} is not lowercase hex SHA-256"));
        return;
    }
    if actual != expected {
        reasons.push(format!(
            "{label}={} does not match recomputed {}",
            json_string(actual),
            json_string(expected)
        ));
    }
}

fn json_string(value: &str) -> String {
    serde_json::to_string(value).unwrap_or_else(|_| format!("{value:?}"))
}

fn optional_identity(value: Option<&str>) -> String {
    value.map(json_string).unwrap_or_else(|| "none".to_string())
}

fn push_optional_artifact_identity(
    out: &mut String,
    label: &str,
    artifact: &Option<ChcProofArtifactDigest>,
) {
    out.push_str(label);
    out.push('=');
    out.push_str(
        &artifact
            .as_ref()
            .map(ChcProofArtifactDigest::identity_sha256)
            .unwrap_or_else(|| "none".to_string()),
    );
    out.push('\n');
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn is_lower_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
}

mod proof_run;
mod replay_check;
mod sealed_evidence;
pub use replay_check::ChcCheckedReplayRun;

#[cfg(test)]
mod tests;
