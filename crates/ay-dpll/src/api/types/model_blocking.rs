// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed model-blocking clause evidence.

use super::{ModelValue, Term};

/// Schema identifier for AY-owned model-blocking clauses.
pub const AY_MODEL_BLOCKING_CLAUSE_SCHEMA: &str = "ay.model-blocking-clause.v1";

/// Schema version for AY-owned model-blocking clauses.
pub const AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for compact model-blocking evidence descriptors.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA: &str = "ay.model-blocking-clause-evidence.v1";

/// Schema version for compact model-blocking evidence descriptors.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Stable status code for an accepted AY-owned model-blocking clause.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS: &str = "accepted";

/// Stable reason code for an accepted model-blocking clause.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON: &str =
    "ay_model_blocking_clause_from_accepted_model";

/// Stable status code for a fail-closed model-blocking evidence descriptor.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS: &str = "fail_closed";

/// Stable reason code for model-blocking evidence that did not cross the
/// consumer boundary.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON: &str =
    "ay_model_blocking_clause_not_accepted_for_consumer";

/// One term assignment captured from an accepted model and blocked by a clause.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ModelBlockingAssignment {
    /// Source term whose current model value is blocked.
    pub term: Term,
    /// Model value observed for `term`.
    pub value: ModelValue,
    /// Stable model value variant name.
    pub value_kind: &'static str,
    /// SMT-LIB rendering of the model value.
    pub value_smtlib: String,
    /// Constant term AY built for `value`.
    pub value_term: Term,
    /// Equality literal `(= term value)`.
    pub equality_term: Term,
    /// Disequality literal `(not (= term value))`.
    pub disequality_term: Term,
}

impl ModelBlockingAssignment {
    /// Render this assignment as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "term": self.term.to_raw(),
            "value_kind": self.value_kind,
            "value_smtlib": self.value_smtlib,
            "value_term": self.value_term.to_raw(),
            "equality_term": self.equality_term.to_raw(),
            "disequality_term": self.disequality_term.to_raw(),
        })
    }
}

/// Compact forwardable evidence for a AY-owned model-blocking clause.
///
/// This descriptor intentionally omits the Boolean clause term and per-term
/// assignment internals. Downstream sidecars can forward it as typed evidence
/// without inspecting raw AY term IDs or parsing the detailed
/// [`ModelBlockingClause`] JSON representation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ModelBlockingClauseEvidence {
    /// Evidence descriptor schema identifier.
    pub schema: &'static str,
    /// Evidence descriptor schema version.
    pub schema_version: u32,
    /// Source model-blocking clause schema identifier.
    pub clause_schema: &'static str,
    /// Source model-blocking clause schema version.
    pub clause_schema_version: u32,
    /// Stable status code for this evidence row.
    pub status_code: &'static str,
    /// Stable reason code for this evidence row.
    pub reason_code: &'static str,
    /// Number of model assignments blocked by the clause.
    pub assignment_count: usize,
    /// Stable value variant names present in the blocked projection.
    pub value_kinds: Vec<&'static str>,
    /// Whether the source model passed AY's consumer boundary.
    pub accepted_for_consumer: bool,
    /// Whether this evidence represents a fail-closed rejection.
    pub fail_closed: bool,
}

impl ModelBlockingClauseEvidence {
    /// Render this descriptor as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "clause_schema": self.clause_schema,
            "clause_schema_version": self.clause_schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "assignment_count": self.assignment_count,
            "value_kinds": self.value_kinds,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
        })
    }

    /// Render this descriptor as deterministic string key/value pairs.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        vec![
            ("schema", self.schema.to_string()),
            ("schema_version", self.schema_version.to_string()),
            ("clause_schema", self.clause_schema.to_string()),
            (
                "clause_schema_version",
                self.clause_schema_version.to_string(),
            ),
            ("status", self.status_code.to_string()),
            ("reason", self.reason_code.to_string()),
            ("assignment_count", self.assignment_count.to_string()),
            ("value_kinds", self.value_kinds.join(",")),
            (
                "accepted_for_consumer",
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed", self.fail_closed.to_string()),
        ]
    }
}

/// AY-owned clause that blocks the current accepted model over selected terms.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ModelBlockingClause {
    /// Clause schema identifier.
    pub schema: &'static str,
    /// Clause schema version.
    pub schema_version: u32,
    /// Final Boolean blocking clause.
    pub clause: Term,
    /// Assignments projected into this blocking clause.
    pub assignments: Vec<ModelBlockingAssignment>,
    /// Whether the source model passed AY's consumer boundary.
    pub accepted_for_consumer: bool,
    /// Whether this clause represents a fail-closed rejection.
    pub fail_closed: bool,
}

impl ModelBlockingClause {
    /// Construct an accepted model-blocking clause evidence record.
    #[must_use]
    pub(crate) fn accepted(clause: Term, assignments: Vec<ModelBlockingAssignment>) -> Self {
        Self {
            schema: AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
            schema_version: AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
            clause,
            assignments,
            accepted_for_consumer: true,
            fail_closed: false,
        }
    }

    /// Number of model assignments blocked by this clause.
    #[must_use]
    pub fn assignment_count(&self) -> usize {
        self.assignments.len()
    }

    /// Return compact forwardable evidence for this model-blocking clause.
    #[must_use]
    pub fn evidence_descriptor(&self) -> ModelBlockingClauseEvidence {
        let accepted = self.accepted_for_consumer && !self.fail_closed;
        ModelBlockingClauseEvidence {
            schema: AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
            schema_version: AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION,
            clause_schema: self.schema,
            clause_schema_version: self.schema_version,
            status_code: if accepted {
                AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS
            } else {
                AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS
            },
            reason_code: if accepted {
                AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON
            } else {
                AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON
            },
            assignment_count: self.assignment_count(),
            value_kinds: self
                .assignments
                .iter()
                .map(|assignment| assignment.value_kind)
                .collect(),
            accepted_for_consumer: self.accepted_for_consumer,
            fail_closed: self.fail_closed,
        }
    }

    /// Return compact deterministic evidence pairs for sidecar row emitters.
    #[must_use]
    pub fn evidence_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        self.evidence_descriptor().to_key_value_pairs()
    }

    /// Render this clause as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "clause": self.clause.to_raw(),
            "assignment_count": self.assignment_count(),
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "assignments": self
                .assignments
                .iter()
                .map(ModelBlockingAssignment::to_json_value)
                .collect::<Vec<_>>(),
        })
    }
}
