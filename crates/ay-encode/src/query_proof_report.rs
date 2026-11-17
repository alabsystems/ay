// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Source-bound proof reporting for independently solved CHC queries.

use std::time::Duration;

use ay_chc::{
    normalized_chc_input_schema_of, ChcCheckedReplayRun, ChcProofArtifactDigest,
    ChcProofRunStopReason, ChcProofRunWithBudgetReport, ChcPrunedQueryObligationId,
    ChcQueryObligationId, VerifiedChcResult,
};

use crate::{EncodeError, Result};

#[path = "query_proof_report_identity.rs"]
mod identity;
#[cfg(test)]
pub(crate) use identity::obligation_set_sha256;
#[path = "query_proof_report_json.rs"]
mod json;

/// Schema for one complete, source-bound batch of CHC query proof reports.
pub const CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA: &str = "ay.chc-query-batch-proof-report/v1";

/// Schema for the ordered source-query identity committed by a batch report.
pub const CHC_QUERY_OBLIGATION_SET_SCHEMA: &str = "ay.chc-query-obligation-set/v1";

/// AY's fail-closed reduction of all independently solved source queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum QueryObligationBatchVerdict {
    /// Every surviving query has definitive, proof-accepted Safe evidence.
    Safe,
    /// At least one query has definitive, proof-accepted Unsafe evidence.
    Unsafe {
        /// Source-order index of the first refuting row.
        first_refuting_row: usize,
    },
    /// No refutation exists, but at least one required row is not proved Safe.
    Unknown,
    /// Every remembered query simplified to false, with source-bound vacuity evidence.
    AllQueriesPruned,
}

impl QueryObligationBatchVerdict {
    /// Stable semantic result code for report consumers.
    pub fn result_code(self) -> &'static str {
        match self {
            Self::Safe => "safe",
            Self::Unsafe { .. } => "unsafe",
            Self::AllQueriesPruned => "safe",
            Self::Unknown => "unknown",
        }
    }

    /// Stable disposition code distinguishing inconclusive and vacuous batches.
    pub fn disposition_code(self) -> &'static str {
        match self {
            Self::Safe => "all-proved",
            Self::Unsafe { .. } => "refuted",
            Self::Unknown => "inconclusive",
            Self::AllQueriesPruned => "all-queries-pruned",
        }
    }

    /// Stable proof classification for the aggregate result.
    pub fn proof_status(self) -> &'static str {
        match self {
            Self::Safe => "verified-conjunction",
            Self::Unsafe { .. } => "verified-counterexample",
            Self::AllQueriesPruned => "verified-vacuity",
            Self::Unknown => "non-proof",
        }
    }
}

/// One source query's authoritative solve report or invocation error.
///
/// Private construction prevents callers from rebinding or omitting rows.
#[derive(Debug)]
#[must_use = "every query-obligation proof row must be inspected"]
pub struct QueryObligationProofReportRow {
    id: ChcQueryObligationId,
    outcome: Result<ChcProofRunWithBudgetReport>,
}

impl QueryObligationProofReportRow {
    pub(crate) fn new(
        id: ChcQueryObligationId,
        outcome: Result<ChcProofRunWithBudgetReport>,
    ) -> Self {
        Self { id, outcome }
    }

    /// Stable identity copied from the exact source-derived query slice.
    pub fn id(&self) -> &ChcQueryObligationId {
        &self.id
    }

    /// Borrow the exact authoritative report or invocation error for this row.
    pub fn outcome(&self) -> &Result<ChcProofRunWithBudgetReport> {
        &self.outcome
    }

    /// Consume this row without discarding its source identity.
    pub fn into_parts(self) -> (ChcQueryObligationId, Result<ChcProofRunWithBudgetReport>) {
        (self.id, self.outcome)
    }

    /// Whether the report was checked against the exact requested query slice.
    ///
    /// A differing solved-input digest has no typed preprocessing certificate
    /// and is never admissible as source-replay evidence.
    pub fn has_identity_input_binding(&self) -> bool {
        self.outcome.as_ref().is_ok_and(|report| {
            report.proof_run().metadata().normalized_input_sha256() == self.id.content_sha256()
        })
    }

    /// Retained checked artifacts, only when bound to the requested slice.
    pub fn checked_replay(&self) -> Option<&ChcCheckedReplayRun> {
        if !self.has_identity_input_binding() {
            return None;
        }
        self.outcome.as_ref().ok()?.checked_replay()
    }

    fn accepted_result(&self) -> Option<&VerifiedChcResult> {
        // Row association is not an equivalence proof. A differing solved
        // input remains diagnostic until a typed certificate exists.
        if !self.has_identity_input_binding() {
            return None;
        }
        let report = self.outcome.as_ref().ok()?;
        if report.stop_reason() != ChcProofRunStopReason::Definitive {
            return None;
        }
        let run = report.proof_run();
        if !run.accepted_as_proof() || !run.metadata().accepted_as_proof() {
            return None;
        }
        Some(run.result())
    }

    fn is_definitive_safe(&self) -> bool {
        self.accepted_result()
            .is_some_and(VerifiedChcResult::is_safe)
    }

    fn is_definitive_unsafe(&self) -> bool {
        self.accepted_result()
            .is_some_and(VerifiedChcResult::is_unsafe)
    }

    fn trust_full_verifier_admissible(&self) -> bool {
        self.accepted_result().is_some()
            && self.checked_replay().is_some_and(|checked| {
                checked.manifest().trust_full_verifier_admissible()
                    && checked
                        .proof_run()
                        .metadata()
                        .trust_full_verifier_admissible()
                    && !checked.problem_bytes().is_empty()
                    && !checked.certificate_bytes().is_empty()
                    && checked
                        .run_log_bytes()
                        .is_some_and(|bytes| !bytes.is_empty())
                    && !checked.replay_log_bytes().is_empty()
                    && !checked.checked_report_bytes().is_empty()
            })
    }

    fn to_json_value(
        &self,
        ordinal: usize,
        source_refutations_admissible: bool,
    ) -> serde_json::Value {
        let obligation = serde_json::json!({
            "ordinal": ordinal,
            "source_query_ordinal": self.id.source_query_ordinal(),
            "query_clause_index": self.id.query_clause_index(),
            "defining_clause_index": self.id.defining_clause_index(),
            "label": self.id.label(),
            "content_sha256": self.id.content_sha256(),
        });

        match &self.outcome {
            Ok(report) => {
                let run = report.proof_run();
                let metadata = run.metadata();
                let accepted_result = self
                    .accepted_result()
                    .filter(|result| source_refutations_admissible || !result.is_unsafe());
                let solved_input_sha256 = metadata.normalized_input_sha256();
                let input_binding = if solved_input_sha256 == self.id.content_sha256() {
                    "identity"
                } else {
                    // Only AY can construct the association, but v1 has no
                    // typed preprocessing certificate that a replay consumer
                    // can check against the requested source slice.
                    "ay-owned-derived-input-unattested-for-source-replay"
                };
                serde_json::json!({
                    "obligation": obligation,
                    "invocation": {
                        "status": "completed",
                        "stop_reason": stop_reason_code(report.stop_reason()),
                        "cancellation_requested_at_return": report.cancellation_requested_at_return(),
                        "elapsed_ms": duration_millis(report.budget_report().total_elapsed),
                        "adaptive_stage_count": report.adaptive_trace().observations().len(),
                    },
                    "input_binding": {
                        "kind": input_binding,
                        "requested_slice_sha256": self.id.content_sha256(),
                        "solved_input_sha256": solved_input_sha256,
                        "identity_bound": self.has_identity_input_binding(),
                    },
                    "result": if accepted_result.is_some() {
                        metadata.result()
                    } else {
                        "unknown"
                    },
                    "solver_result": metadata.result(),
                    "proof_status": if accepted_result.is_some() {
                        metadata.proof_status()
                    } else {
                        "non-proof"
                    },
                    "accepted_as_proof": accepted_result.is_some(),
                    "trust_full_verifier_admissible": accepted_result.is_some()
                        && self.trust_full_verifier_admissible(),
                    "metadata_identity_sha256": metadata.identity_sha256(),
                    "transcript_metadata": metadata.to_json_value(),
                })
            }
            Err(error) => serde_json::json!({
                "obligation": obligation,
                "invocation": {
                    "status": "error",
                    "error_code": encode_error_code(error),
                    "error": error.to_string(),
                },
                "input_binding": {
                    "kind": "not-solved",
                    "requested_slice_sha256": self.id.content_sha256(),
                    "solved_input_sha256": null,
                    "identity_bound": false,
                },
                "result": "unknown",
                "solver_result": "not-invoked",
                "proof_status": "non-proof",
                "accepted_as_proof": false,
                "trust_full_verifier_admissible": false,
                "metadata_identity_sha256": null,
                "transcript_metadata": null,
            }),
        }
    }
}

/// Complete source identity plus every independently solved query report.
///
/// Its private constructor checks the exact ordered ID list captured pre-solve.
#[derive(Debug)]
#[must_use = "multi-query proof reports must be inspected"]
pub struct QueryObligationBatchProofReport {
    source_normalized_input: String,
    source_normalized_input_schema: &'static str,
    source_normalized_input_sha256: String,
    source_normalized_input_bytes: u64,
    source_query_count: usize,
    source_pruned_false_query_ids: Vec<ChcPrunedQueryObligationId>,
    source_has_stripped_body_forall: bool,
    obligation_set_content: String,
    obligation_set_sha256: String,
    rows: Vec<QueryObligationProofReportRow>,
    total_elapsed: Duration,
}

impl QueryObligationBatchProofReport {
    pub(crate) fn new(
        source_normalized_input: String,
        source_pruned_false_query_ids: &[ChcPrunedQueryObligationId],
        source_has_stripped_body_forall: bool,
        expected_ids: &[ChcQueryObligationId],
        rows: Vec<QueryObligationProofReportRow>,
        total_elapsed: Duration,
    ) -> Result<Self> {
        let Some(source_normalized_input_schema) =
            normalized_chc_input_schema_of(&source_normalized_input)
        else {
            return Err(EncodeError::Chc(ay_chc::ChcError::Internal(
                "query proof report source is not canonical normalized CHC input".to_string(),
            )));
        };
        let source_descriptor = ChcProofArtifactDigest::from_bytes(
            "source-normalized-chc-input",
            source_normalized_input.as_bytes(),
        );
        let source_normalized_input_sha256 = source_descriptor.sha256;
        let source_normalized_input_bytes = source_descriptor.bytes;
        if expected_ids.len() != rows.len()
            || expected_ids
                .iter()
                .zip(&rows)
                .any(|(expected, row)| expected != row.id())
        {
            return Err(EncodeError::Chc(ay_chc::ChcError::Internal(
                "query proof report rows do not match the complete ordered source obligation set"
                    .to_string(),
            )));
        }
        if !identity::source_order_is_complete(source_pruned_false_query_ids, expected_ids.iter()) {
            return Err(EncodeError::Chc(ay_chc::ChcError::Internal(
                "query evidence does not form a complete ordered source obligation set".to_string(),
            )));
        }

        let source_query_count = expected_ids
            .len()
            .checked_add(source_pruned_false_query_ids.len())
            .ok_or_else(|| {
                EncodeError::Chc(ay_chc::ChcError::Internal(
                    "source query count overflowed usize".to_string(),
                ))
            })?;
        if source_query_count == 0 {
            return Err(EncodeError::Chc(ay_chc::ChcError::Internal(
                "query proof report cannot represent a source with no query".to_string(),
            )));
        }

        let obligation_set = identity::obligation_set_identity(
            source_normalized_input_schema,
            &source_normalized_input_sha256,
            source_normalized_input_bytes,
            source_pruned_false_query_ids,
            source_has_stripped_body_forall,
            expected_ids,
        );
        Ok(Self {
            source_normalized_input,
            source_normalized_input_schema,
            source_normalized_input_sha256,
            source_normalized_input_bytes,
            source_query_count,
            source_pruned_false_query_ids: source_pruned_false_query_ids.to_vec(),
            source_has_stripped_body_forall,
            obligation_set_content: obligation_set.content,
            obligation_set_sha256: obligation_set.sha256,
            rows,
            total_elapsed,
        })
    }

    /// Schema the normalized aggregate CHC input names on its first line.
    pub fn source_normalized_input_schema(&self) -> &'static str {
        self.source_normalized_input_schema
    }

    /// SHA-256 of the exact aggregate CHC problem supplied to the batch API.
    pub fn source_normalized_input_sha256(&self) -> &str {
        &self.source_normalized_input_sha256
    }

    /// Exact normalized aggregate CHC bytes hashed by this sealed report.
    pub fn source_normalized_input_content(&self) -> &[u8] {
        self.source_normalized_input.as_bytes()
    }

    /// Byte length of the deterministic normalized aggregate CHC input.
    pub fn source_normalized_input_bytes(&self) -> u64 {
        self.source_normalized_input_bytes
    }

    /// Total number of source properties, including vacuously pruned queries.
    pub fn source_query_count(&self) -> usize {
        self.source_query_count
    }

    /// Number of source queries whose bodies simplified to Boolean `false`.
    pub fn source_pruned_false_query_count(&self) -> usize {
        self.source_pruned_false_query_ids.len()
    }

    /// Exact ordered identities for vacuously pruned source queries.
    pub fn source_pruned_false_query_ids(&self) -> &[ChcPrunedQueryObligationId] {
        &self.source_pruned_false_query_ids
    }

    /// Whether parsing weakened a body-position universal quantifier.
    pub fn source_has_stripped_body_forall(&self) -> bool {
        self.source_has_stripped_body_forall
    }

    /// SHA-256 committing to the source and complete ordered obligation list.
    pub fn obligation_set_sha256(&self) -> &str {
        &self.obligation_set_sha256
    }

    /// Exact versioned obligation-set preimage hashed by this sealed report.
    pub fn obligation_set_content(&self) -> &[u8] {
        self.obligation_set_content.as_bytes()
    }

    /// Every source query row, in deterministic source-clause order.
    pub fn rows(&self) -> &[QueryObligationProofReportRow] {
        &self.rows
    }

    /// Whole batch wall-clock time, including slicing and sequential row solves.
    pub fn total_elapsed(&self) -> Duration {
        self.total_elapsed
    }

    /// Fail-closed aggregate verdict derived from immutable row evidence.
    pub fn verdict(&self) -> QueryObligationBatchVerdict {
        if !self.source_has_stripped_body_forall {
            if let Some(first_refuting_row) = self
                .rows
                .iter()
                .position(QueryObligationProofReportRow::is_definitive_unsafe)
            {
                return QueryObligationBatchVerdict::Unsafe { first_refuting_row };
            }
        }
        if self.rows.is_empty() {
            return QueryObligationBatchVerdict::AllQueriesPruned;
        }
        if self
            .rows
            .iter()
            .all(QueryObligationProofReportRow::is_definitive_safe)
        {
            QueryObligationBatchVerdict::Safe
        } else {
            QueryObligationBatchVerdict::Unknown
        }
    }

    /// Whether the aggregate result has complete proof-accepted row evidence.
    pub fn accepted_as_proof(&self) -> bool {
        if !self.pruned_vacuity_evidence_valid() {
            return false;
        }
        match self.verdict() {
            QueryObligationBatchVerdict::Safe
            | QueryObligationBatchVerdict::Unsafe { .. }
            | QueryObligationBatchVerdict::AllQueriesPruned => true,
            QueryObligationBatchVerdict::Unknown => false,
        }
    }

    /// Whether sufficient identity-bound rows carry checked replay.
    pub fn trust_full_verifier_admissible(&self) -> bool {
        if !self.pruned_vacuity_evidence_valid() {
            return false;
        }
        match self.verdict() {
            QueryObligationBatchVerdict::Safe => self
                .rows
                .iter()
                .all(QueryObligationProofReportRow::trust_full_verifier_admissible),
            QueryObligationBatchVerdict::Unsafe { .. } => self
                .rows
                .iter()
                .any(|row| row.is_definitive_unsafe() && row.trust_full_verifier_admissible()),
            QueryObligationBatchVerdict::AllQueriesPruned => true,
            QueryObligationBatchVerdict::Unknown => false,
        }
    }

    fn required_rows_have_identity_binding(&self) -> bool {
        match self.verdict() {
            QueryObligationBatchVerdict::Safe => self
                .rows
                .iter()
                .all(QueryObligationProofReportRow::has_identity_input_binding),
            QueryObligationBatchVerdict::Unsafe { first_refuting_row } => {
                self.rows[first_refuting_row].has_identity_input_binding()
            }
            QueryObligationBatchVerdict::AllQueriesPruned => true,
            QueryObligationBatchVerdict::Unknown => false,
        }
    }

    fn pruned_vacuity_evidence_valid(&self) -> bool {
        identity::source_order_is_complete(
            &self.source_pruned_false_query_ids,
            self.rows.iter().map(QueryObligationProofReportRow::id),
        )
    }
}

fn stop_reason_code(reason: ChcProofRunStopReason) -> &'static str {
    match reason {
        ChcProofRunStopReason::Definitive => "definitive",
        ChcProofRunStopReason::BudgetExhausted => "budget-exhausted",
        ChcProofRunStopReason::ExternallyCancelled => "externally-cancelled",
        ChcProofRunStopReason::Inconclusive => "inconclusive",
        ChcProofRunStopReason::EffortExhausted => "effort-exhausted",
        _ => "unclassified",
    }
}

fn encode_error_code(error: &EncodeError) -> &'static str {
    match error {
        EncodeError::Sort(_) => "sort-error",
        EncodeError::Chc(_) => "chc-error",
        EncodeError::SolverPanicked(_) => "solver-panicked",
        EncodeError::Cancelled => "cancelled-before-start",
        EncodeError::Unimplemented(_) => "unimplemented",
    }
}

fn duration_millis(duration: Duration) -> u64 {
    u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
}
