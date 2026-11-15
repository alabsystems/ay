// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public admission requires the opaque capability from fresh original replay.

use super::*;

impl ChcProofEvidenceManifest {
    /// Admit compact Unsafe evidence only after complete original-source replay.
    /// Parsed summaries and matching digests alone never create this authority.
    pub fn try_with_validated_compact_ground_replay_summary(
        self,
        summary: ChcCheckedReplaySummary,
        validated: &crate::ChcValidatedCompactGroundDerivation,
    ) -> Result<Self, ChcCheckedReplaySummaryError> {
        let mut reasons = self.checked_replay_summary_rejection_reasons(&summary);
        match summary.obligations.as_slice() {
            [row] if row.payload_format == ChcReplayPayloadFormat::CompactGroundDerivationV1 => {
                if row.query.schema != CHC_PROOF_ARTIFACT_DIGEST_SCHEMA
                    || validated.artifact_schema() != crate::CHC_COMPACT_GROUND_DERIVATION_SCHEMA
                    || row.query.role != validated.artifact_role()
                    || row.query.sha256 != validated.artifact_sha256()
                    || Some(row.query.bytes) != u64::try_from(validated.artifact_bytes()).ok()
                {
                    reasons.push("validated compact ground artifact descriptor mismatch".into());
                }
            }
            _ => reasons
                .push("validated compact replay requires exactly one compact obligation".into()),
        }
        if self.problem_sha256 != validated.normalized_input_sha256()
            || summary.manifest_binding.problem_sha256 != validated.normalized_input_sha256()
            || self.transcript_metadata.normalized_input_sha256
                != validated.normalized_input_sha256()
        {
            reasons.push("validated compact ground replay normalized problem mismatch".into());
        }
        if self.problem_schema != validated.normalized_input_schema()
            || self.transcript_metadata.normalized_input_schema
                != validated.normalized_input_schema()
        {
            reasons.push("validated compact ground replay normalized schema mismatch".into());
        }
        if self.source_clause_sequence_sha256.as_deref()
            != Some(validated.source_clause_sequence_sha256())
            || summary
                .manifest_binding
                .source_clause_sequence_sha256
                .as_deref()
                != Some(validated.source_clause_sequence_sha256())
        {
            reasons.push("validated compact ground replay source clause sequence mismatch".into());
        }
        if !reasons.is_empty() {
            return Err(ChcCheckedReplaySummaryError::new(reasons));
        }
        Ok(self.admit_checked_replay_summary(summary))
    }
}
