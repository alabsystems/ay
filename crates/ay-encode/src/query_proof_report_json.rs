// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Diagnostic JSON rendering for source-bound query reports.

use super::*;

impl QueryObligationBatchProofReport {
    /// Render a compact diagnostic envelope without embedding artifact bytes.
    ///
    /// The typed object is authoritative. A persisted consumer must revalidate
    /// every digest and checked-replay artifact; JSON booleans are insufficient.
    pub fn to_json_value(&self) -> serde_json::Value {
        let verdict = self.verdict();
        let accepted_as_proof = self.accepted_as_proof();
        let trust_full_verifier_admissible = self.trust_full_verifier_admissible();
        let required_rows_have_identity_binding = self.required_rows_have_identity_binding();
        let has_pruned_queries = !self.source_pruned_false_query_ids.is_empty();
        let first_refuting_row = match verdict {
            QueryObligationBatchVerdict::Unsafe { first_refuting_row } => Some(first_refuting_row),
            _ => None,
        };
        let non_admission_reason = if trust_full_verifier_admissible {
            None
        } else {
            Some(match verdict {
                QueryObligationBatchVerdict::Safe | QueryObligationBatchVerdict::Unsafe { .. }
                    if !required_rows_have_identity_binding =>
                {
                    "one_or_more_required_rows_not_identity_bound"
                }
                QueryObligationBatchVerdict::Safe | QueryObligationBatchVerdict::Unsafe { .. } => {
                    "one_or_more_required_rows_missing_checked_replay"
                }
                QueryObligationBatchVerdict::Unknown => "aggregate_result_is_non_proof",
                QueryObligationBatchVerdict::AllQueriesPruned => "source_vacuity_evidence_rejected",
            })
        };
        let replay_status = if matches!(verdict, QueryObligationBatchVerdict::AllQueriesPruned) {
            "source-vacuity-checked"
        } else if trust_full_verifier_admissible && has_pruned_queries {
            "replayable-with-source-vacuity"
        } else if trust_full_verifier_admissible {
            "replayable"
        } else if accepted_as_proof && !required_rows_have_identity_binding {
            "not-replayable-for-source"
        } else if accepted_as_proof {
            "replay-artifacts-required"
        } else {
            "not-replayable"
        };
        let transcript_status = if matches!(verdict, QueryObligationBatchVerdict::AllQueriesPruned)
        {
            "source-vacuity-only"
        } else if trust_full_verifier_admissible && has_pruned_queries {
            "replayable-with-source-vacuity"
        } else if trust_full_verifier_admissible {
            "replayable"
        } else if accepted_as_proof && !required_rows_have_identity_binding {
            "derived-input-only"
        } else if accepted_as_proof {
            "metadata-only"
        } else {
            "non-proof"
        };

        serde_json::json!({
            "schema": CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA,
            "schema_version": 1,
            "source": {
                "normalized_input_schema": NORMALIZED_CHC_INPUT_SCHEMA,
                "normalized_input_sha256": self.source_normalized_input_sha256,
                "normalized_input_bytes": self.source_normalized_input_bytes,
                "query_count": self.source_query_count,
                "pruned_false_query_count": self.source_pruned_false_query_ids.len(),
                "has_stripped_body_forall": self.source_has_stripped_body_forall,
            },
            "obligation_set": {
                "schema": CHC_QUERY_OBLIGATION_SET_SCHEMA,
                "identity_sha256": self.obligation_set_sha256,
                "count": self.source_query_count,
                "surviving_count": self.rows.len(),
                "pruned_false_count": self.source_pruned_false_query_ids.len(),
                "pruned_false_queries": self.source_pruned_false_query_ids.iter().map(|id| {
                    serde_json::json!({
                        "ordinal": id.ordinal(),
                        "content_schema": id.content_schema(),
                        "content_bytes": id.content_bytes().len(),
                        "content_sha256": id.content_sha256(),
                    })
                }).collect::<Vec<_>>(),
            },
            "result": verdict.result_code(),
            "disposition": verdict.disposition_code(),
            "proof_status": if accepted_as_proof {
                verdict.proof_status()
            } else {
                "non-proof"
            },
            "accepted_as_proof": accepted_as_proof,
            "trust_full_verifier_admissible": trust_full_verifier_admissible,
            "required_rows_identity_bound": required_rows_have_identity_binding,
            "trust_full_verifier_non_admission_reason": non_admission_reason,
            "first_refuting_row": first_refuting_row,
            "total_elapsed_ms": duration_millis(self.total_elapsed),
            "replay": {
                "status": replay_status,
                "row_count": self.rows.len(),
            },
            "transcript": {
                "status": transcript_status,
                "metadata_only": !trust_full_verifier_admissible,
                "row_count": self.rows.len(),
            },
            "serialized_admission": {
                "admissible": false,
                "reason": "diagnostic-json-requires-typed-in-process-revalidation",
            },
            "rows": self
                .rows
                .iter()
                .enumerate()
                .map(|(ordinal, row)| {
                    row.to_json_value(ordinal, !self.source_has_stripped_body_forall)
                })
                .collect::<Vec<_>>(),
        })
    }
}
