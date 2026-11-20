// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Durable, bounded evidence for a fully-ground derivation of `false`.
//!
//! The in-memory [`GroundDerivation`] is deliberately crate-private because a
//! clause index or environment is not authority by itself. This module is the
//! public persistence boundary: AY emits one canonical representation, and a
//! consumer receives an opaque capability only after the bytes are rebound to
//! its own [`ChcProblem`] and the native ground validator decides the complete
//! derivation again.

use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use serde::{Deserialize, Serialize};
#[cfg(test)]
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::control::{GroundValidationControl, GroundValidationInterrupted};
#[cfg(test)]
use super::eval_ground_pub;
#[cfg(any(test, doc))]
use super::validate_ground_derivation;
use super::{
    ground_uf_congruence_key, validate_ground_derivation_with_control, GroundDerivation,
    GroundDerivationError, GroundDerivationStep, GroundSourceSurfaceCache,
    GroundSourceSurfaceError, GroundUfCongruenceKey,
};
#[cfg(test)]
use crate::normalized_chc_input_sha256;
#[cfg(test)]
use crate::proof_metadata::ordered_chc_clause_sequence_sha256;
use crate::{
    ChcError, ChcExpr, ChcPdrProofRun, ChcProblem, ChcProofRunArtifact, ChcResult, ChcSort,
    Counterexample, SmtValue, VerifiedChcResult,
};

#[path = "compact_artifact.rs"]
pub(crate) mod compact_artifact;
mod producer;
mod rebuild;
mod source_identity;
mod transport;
mod view;

pub use view::ChcGroundDerivationStepView;

#[cfg(test)]
mod decoding_progress_tests;

#[cfg(test)]
mod encoding_progress_tests;

/// Schema for a canonical ground-derivation artifact.
pub const CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA: &str = "ay.chc-ground-derivation-artifact/v1";
/// Artifact role for a checked derivation of `false`.
pub const CHC_GROUND_DERIVATION_ARTIFACT_ROLE: &str = "unsafe-ground-derivation";
/// Schema for source-authenticated finite-UF ground evidence.
pub const CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA: &str = "ay.chc-ground-derivation-artifact/v2";
/// Artifact role for v2 finite-UF ground evidence.
pub const CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE: &str = "unsafe-ground-derivation-v2";

/// Maximum complete artifact size (16 MiB).
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES: usize = 16 * 1024 * 1024;
/// Maximum number of source predicates admitted at this boundary.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES: usize = 65_536;
/// Maximum number of source clauses admitted at this boundary.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES: usize = 262_144;
/// Maximum number of derivation steps.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS: usize = 262_144;
/// Maximum total premise edges across all steps.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES: usize = 1_048_576;
/// Maximum total clause-variable bindings across all steps.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_BINDINGS: usize = 1_048_576;
/// Maximum total ordinary-UF observations across all derivation steps.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_UF_OBSERVATIONS: usize = 1_048_576;
/// Maximum total recursively encoded value nodes.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES: usize = 1_048_576;
/// Maximum JSON/value nesting admitted before recursive decoding.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH: usize = 128;
/// Maximum encoded byte length of one JSON string or scalar token.
pub const CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES: usize = 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct GroundDerivationEnvelope {
    schema: String,
    schema_version: u64,
    role: String,
    normalized_input_schema: String,
    normalized_input_sha256: String,
    source_clause_sequence_sha256: String,
    step_count: u64,
    query_step: u32,
    premise_edge_count: u64,
    binding_count: u64,
    value_node_count: u64,
    steps: Vec<WireStep>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct GroundDerivationEnvelopeV2 {
    schema: String,
    schema_version: u64,
    role: String,
    normalized_input_schema: String,
    normalized_input_sha256: String,
    source_clause_sequence_sha256: String,
    step_count: u64,
    query_step: u32,
    premise_edge_count: u64,
    binding_count: u64,
    uf_observation_count: u64,
    value_node_count: u64,
    steps: Vec<WireStepV2>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireStep {
    clause_index: u32,
    premises: Vec<u32>,
    bindings: Vec<WireBinding>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireStepV2 {
    clause_index: u32,
    premises: Vec<u32>,
    bindings: Vec<WireBinding>,
    uf_observations: Vec<WireUfObservation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireUfObservation {
    application_ordinal: u32,
    result: WireValue,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireBinding {
    name: String,
    value: WireValue,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum WireValue {
    Bool {
        value: bool,
    },
    Int {
        decimal: String,
    },
    Real {
        numerator: String,
        denominator: String,
    },
    Bitvector {
        width: u32,
        value_hex: String,
    },
    ConstArray {
        default: Box<Self>,
    },
    ArrayMap {
        default: Box<Self>,
        entries: Vec<WireArrayEntry>,
    },
    Datatype {
        constructor: String,
        fields: Vec<Self>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireArrayEntry {
    index: WireValue,
    value: WireValue,
}

/// Stable reason a ground-derivation artifact was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcGroundDerivationArtifactErrorReason {
    /// The caller refused continuation at a cooperative validation boundary.
    Interrupted,
    /// The counterexample does not carry a candidate ground derivation.
    MissingGroundDerivation,
    /// The complete artifact exceeds the byte bound.
    ArtifactTooLarge,
    /// The supplied problem exceeds the predicate bound.
    TooManyPredicates,
    /// The supplied problem exceeds the source-clause bound.
    TooManyClauses,
    /// The artifact exceeds the derivation-step bound.
    TooManySteps,
    /// The artifact exceeds the premise-edge bound.
    TooManyPremiseEdges,
    /// The artifact exceeds the variable-binding bound.
    TooManyBindings,
    /// The artifact exceeds the finite ordinary-UF observation bound.
    TooManyUfObservations,
    /// Canonical source-clause authentication exceeded the fixed
    /// derivation-wide work envelope.
    SourceWorkLimitExceeded,
    /// The authenticated live problem has an invalid action or predicate
    /// reference, an ill-typed expression, or an inconsistent source namespace.
    InvalidSourceProblem,
    /// The artifact exceeds the recursively encoded value-node bound.
    TooManyValueNodes,
    /// JSON or value nesting exceeds the fixed depth bound.
    NestingTooDeep,
    /// A single JSON string or scalar token exceeds its byte bound.
    StringOrTokenTooLarge,
    /// JSON was malformed, duplicated, or contained unknown fields.
    MalformedEnvelope,
    /// JSON was valid but did not use AY's exact canonical encoding.
    NonCanonicalEnvelope,
    /// The schema or schema version is unsupported.
    SchemaMismatch,
    /// The artifact role is not the unsafe ground-derivation role.
    RoleMismatch,
    /// The artifact is bound to a different normalized problem.
    ProblemHashMismatch,
    /// The positional clause sequence differs from the supplied problem.
    ClauseSequenceHashMismatch,
    /// A declared count differs from the decoded content.
    CountMismatch,
    /// An index cannot be represented or names missing source material.
    IndexOutOfRange,
    /// Bindings were duplicated, reordered, omitted, or padded.
    BindingSetMismatch,
    /// A binding value does not match its source variable sort.
    BindingSortMismatch,
    /// An integer, rational, bitvector, array, or datatype value is malformed.
    InvalidValue,
    /// Opaque solver placeholders are never portable evidence.
    OpaqueValue,
    /// Private UF observations or a non-scalar UF surface are unsupported by
    /// the selected artifact version.
    UnsupportedUninterpretedFunction,
    /// UF observations were omitted, duplicated, padded, or reordered.
    UfObservationSetMismatch,
    /// A source UF application could not be reconstructed as an exact finite
    /// observation.
    UfObservationNotGround,
    /// Equal concrete argument tuples were assigned different UF results.
    UfCongruenceViolation,
    /// The native ground validator rejected the reconstructed derivation.
    DerivationRejected,
    /// The bounded decoder or native validator panicked; the panic was contained.
    ValidationPanicked,
    /// Canonical serialization failed.
    SerializationFailed,
}

impl ChcGroundDerivationArtifactErrorReason {
    /// Stable lower-snake-case reason code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::Interrupted => "interrupted",
            Self::MissingGroundDerivation => "missing_ground_derivation",
            Self::ArtifactTooLarge => "artifact_too_large",
            Self::TooManyPredicates => "too_many_predicates",
            Self::TooManyClauses => "too_many_clauses",
            Self::TooManySteps => "too_many_steps",
            Self::TooManyPremiseEdges => "too_many_premise_edges",
            Self::TooManyBindings => "too_many_bindings",
            Self::TooManyUfObservations => "too_many_uf_observations",
            Self::SourceWorkLimitExceeded => "source_work_limit_exceeded",
            Self::InvalidSourceProblem => "invalid_source_problem",
            Self::TooManyValueNodes => "too_many_value_nodes",
            Self::NestingTooDeep => "nesting_too_deep",
            Self::StringOrTokenTooLarge => "string_or_token_too_large",
            Self::MalformedEnvelope => "malformed_envelope",
            Self::NonCanonicalEnvelope => "non_canonical_envelope",
            Self::SchemaMismatch => "schema_mismatch",
            Self::RoleMismatch => "role_mismatch",
            Self::ProblemHashMismatch => "problem_hash_mismatch",
            Self::ClauseSequenceHashMismatch => "clause_sequence_hash_mismatch",
            Self::CountMismatch => "count_mismatch",
            Self::IndexOutOfRange => "index_out_of_range",
            Self::BindingSetMismatch => "binding_set_mismatch",
            Self::BindingSortMismatch => "binding_sort_mismatch",
            Self::InvalidValue => "invalid_value",
            Self::OpaqueValue => "opaque_value",
            Self::UnsupportedUninterpretedFunction => "unsupported_uninterpreted_function",
            Self::UfObservationSetMismatch => "uf_observation_set_mismatch",
            Self::UfObservationNotGround => "uf_observation_not_ground",
            Self::UfCongruenceViolation => "uf_congruence_violation",
            Self::DerivationRejected => "derivation_rejected",
            Self::ValidationPanicked => "validation_panicked",
            Self::SerializationFailed => "serialization_failed",
        }
    }
}

/// Typed fail-closed artifact error.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{reason_code}: {detail}")]
pub struct ChcGroundDerivationArtifactError {
    /// Stable error classification.
    pub reason: ChcGroundDerivationArtifactErrorReason,
    /// Stable lower-snake-case reason code.
    pub reason_code: &'static str,
    /// Human-readable detail; this field never carries positive authority.
    pub detail: String,
}

impl ChcGroundDerivationArtifactError {
    fn new(reason: ChcGroundDerivationArtifactErrorReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            reason_code: reason.code(),
            detail: detail.into(),
        }
    }
}

/// Opaque proof that exact artifact bytes validated against one supplied problem.
///
/// Construction is private. The capability grants no authority for another
/// problem: callers must invoke the version-matching
/// [`validate_chc_ground_derivation_artifact`] or
/// [`validate_chc_ground_derivation_artifact_v2`] parser again at every
/// deserialization/trust boundary.
#[derive(Debug)]
#[must_use = "validated ground evidence must remain paired with its source problem"]
pub struct ChcValidatedGroundDerivation {
    artifact_schema: &'static str,
    artifact_role: &'static str,
    artifact_sha256: String,
    artifact_bytes: u64,
    normalized_input_sha256: String,
    source_clause_sequence_sha256: String,
    step_count: usize,
    query_step: usize,
    premise_edge_count: usize,
    binding_count: usize,
    uf_observation_count: usize,
    value_node_count: usize,
    derivation: GroundDerivation,
}

impl ChcValidatedGroundDerivation {
    /// Ground-derivation artifact schema that was validated.
    pub fn artifact_schema(&self) -> &'static str {
        self.artifact_schema
    }

    /// Exact artifact role authenticated by the version-specific parser.
    pub fn artifact_role(&self) -> &'static str {
        self.artifact_role
    }

    /// SHA-256 of the exact canonical artifact bytes.
    pub fn artifact_sha256(&self) -> &str {
        &self.artifact_sha256
    }

    /// Exact canonical artifact byte length authenticated by the parser.
    pub fn artifact_bytes(&self) -> u64 {
        self.artifact_bytes
    }

    /// SHA-256 of AY's normalized source problem representation.
    pub fn normalized_input_sha256(&self) -> &str {
        &self.normalized_input_sha256
    }

    /// SHA-256 of the positional source-clause sequence overlay.
    pub fn source_clause_sequence_sha256(&self) -> &str {
        &self.source_clause_sequence_sha256
    }

    /// Number of validated derivation steps.
    pub fn step_count(&self) -> usize {
        self.step_count
    }

    /// Zero-based validated query-root step.
    pub fn query_step(&self) -> usize {
        self.query_step
    }

    /// Total validated premise edges.
    pub fn premise_edge_count(&self) -> usize {
        self.premise_edge_count
    }

    /// Total exact source-variable bindings.
    pub fn binding_count(&self) -> usize {
        self.binding_count
    }

    /// Total source-authenticated ordinary-UF observations.
    pub fn uf_observation_count(&self) -> usize {
        self.uf_observation_count
    }

    /// Total recursively validated concrete value nodes.
    pub fn value_node_count(&self) -> usize {
        self.value_node_count
    }

    pub(crate) fn derivation(&self) -> &GroundDerivation {
        &self.derivation
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct ContentCounts {
    premise_edges: usize,
    bindings: usize,
    uf_observations: usize,
    value_nodes: usize,
}

fn error(
    reason: ChcGroundDerivationArtifactErrorReason,
    detail: impl Into<String>,
) -> ChcGroundDerivationArtifactError {
    ChcGroundDerivationArtifactError::new(reason, detail)
}

fn interruption_error(_: GroundValidationInterrupted) -> ChcGroundDerivationArtifactError {
    error(
        ChcGroundDerivationArtifactErrorReason::Interrupted,
        "ground-derivation validation interrupted by the caller",
    )
}

#[cfg(test)]
fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn checked_u64(value: usize, label: &str) -> Result<u64, ChcGroundDerivationArtifactError> {
    u64::try_from(value).map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::CountMismatch,
            format!("{label} does not fit in u64"),
        )
    })
}

fn checked_u32(value: usize, label: &str) -> Result<u32, ChcGroundDerivationArtifactError> {
    u32::try_from(value).map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
            format!("{label} does not fit in u32"),
        )
    })
}

/// Bound and validate exactly the live source authenticated by ground artifacts
/// and native replay, reusing the caller's sticky cancellation state. Node/edge
/// traversal polls internally; individual sort derivations and semantic
/// validators remain opaque between phase polls.
pub(super) fn validate_ground_source_problem_with_control(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    source_identity::preflight_problem_source_identity(control, problem)?;
    source_identity::validate_source_semantics(problem, control)
}

#[cfg(test)]
fn validate_problem_bounds(problem: &ChcProblem) -> Result<(), ChcGroundDerivationArtifactError> {
    let mut progress = || true;
    let mut control = GroundValidationControl::new(&mut progress);
    validate_problem_bounds_with_control(problem, &mut control)
}

pub(super) fn validate_problem_bounds_with_control(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    validate_problem_cardinality(problem, control)?;
    validate_ground_source_problem_with_control(problem, control)
}

fn validate_wire_problem(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<usize>, ChcGroundDerivationArtifactError> {
    validate_problem_cardinality(problem, control)?;
    let sort_budget = source_identity::preflight(control, problem, true)?;
    source_identity::validate_source_semantics(problem, control)?;
    Ok(sort_budget)
}

fn validate_problem_cardinality(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if problem.predicates().len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManyPredicates,
            format!(
                "problem has {} predicates, maximum is {}",
                problem.predicates().len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES
            ),
        ));
    }
    if problem.clauses().len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManyClauses,
            format!(
                "problem has {} clauses, maximum is {}",
                problem.clauses().len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES
            ),
        ));
    }
    Ok(())
}

#[cfg(test)]
fn validate_json_surface(bytes: &[u8]) -> Result<(), ChcGroundDerivationArtifactError> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut string_bytes = 0usize;
    let mut token_bytes = 0usize;

    for &byte in bytes {
        if in_string {
            string_bytes = string_bytes.checked_add(1).ok_or_else(|| {
                error(
                    ChcGroundDerivationArtifactErrorReason::StringOrTokenTooLarge,
                    "JSON string length overflowed usize",
                )
            })?;
            if string_bytes > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::StringOrTokenTooLarge,
                    format!(
                        "JSON string exceeds {} encoded bytes",
                        CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
                    ),
                ));
            }
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
                string_bytes = 0;
            }
            continue;
        }

        match byte {
            b'"' => {
                in_string = true;
                string_bytes = 0;
                token_bytes = 0;
            }
            b'{' | b'[' => {
                depth = depth.checked_add(1).ok_or_else(|| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::NestingTooDeep,
                        "JSON nesting depth overflowed usize",
                    )
                })?;
                if depth > CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::NestingTooDeep,
                        format!(
                            "JSON nesting exceeds {}",
                            CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH
                        ),
                    ));
                }
                token_bytes = 0;
            }
            b'}' | b']' | b',' | b':' | b' ' | b'\t' | b'\r' | b'\n' => {
                if matches!(byte, b'}' | b']') {
                    depth = depth.saturating_sub(1);
                }
                token_bytes = 0;
            }
            _ => {
                token_bytes = token_bytes.checked_add(1).ok_or_else(|| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::StringOrTokenTooLarge,
                        "JSON scalar token length overflowed usize",
                    )
                })?;
                if token_bytes > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::StringOrTokenTooLarge,
                        format!(
                            "JSON scalar token exceeds {} bytes",
                            CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Count the recursive wire-value occurrences a sort-directed decoder will
/// visit, without consulting datatype constructor tables.
fn wire_value_typecheck_occurrences_with_control(
    root: &WireValue,
    control: &mut GroundValidationControl<'_>,
) -> Result<usize, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let mut occurrences = 0usize;
    let mut stack = vec![root];
    while let Some(value) = stack.pop() {
        control.poll().map_err(interruption_error)?;
        occurrences = occurrences
            .checked_add(1)
            .filter(|count| *count <= CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES)
            .ok_or_else(|| {
                error(
                    ChcGroundDerivationArtifactErrorReason::TooManyValueNodes,
                    "wire binding value exceeds the recursive value-node bound",
                )
            })?;
        match value {
            WireValue::ConstArray { default } => stack.push(default),
            WireValue::ArrayMap { default, entries } => {
                stack.push(default);
                for entry in entries {
                    control.poll().map_err(interruption_error)?;
                    stack.push(&entry.index);
                    stack.push(&entry.value);
                }
            }
            WireValue::Datatype { fields, .. } => {
                for field in fields {
                    control.poll().map_err(interruption_error)?;
                    stack.push(field);
                }
            }
            WireValue::Bool { .. }
            | WireValue::Int { .. }
            | WireValue::Real { .. }
            | WireValue::Bitvector { .. } => {}
        }
    }
    control.poll().map_err(interruption_error)?;
    Ok(occurrences)
}

fn increment_count(
    count: &mut usize,
    maximum: usize,
    reason: ChcGroundDerivationArtifactErrorReason,
    label: &str,
) -> Result<(), ChcGroundDerivationArtifactError> {
    *count = count
        .checked_add(1)
        .ok_or_else(|| error(reason, format!("{label} count overflowed usize")))?;
    if *count > maximum {
        return Err(error(reason, format!("{label} count exceeds {maximum}")));
    }
    Ok(())
}

fn add_count(
    count: &mut usize,
    amount: usize,
    maximum: usize,
    reason: ChcGroundDerivationArtifactErrorReason,
    label: &str,
) -> Result<(), ChcGroundDerivationArtifactError> {
    *count = count
        .checked_add(amount)
        .ok_or_else(|| error(reason, format!("{label} count overflowed usize")))?;
    if *count > maximum {
        return Err(error(reason, format!("{label} count exceeds {maximum}")));
    }
    Ok(())
}

fn validate_value_depth(depth: usize) -> Result<(), ChcGroundDerivationArtifactError> {
    if depth > CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::NestingTooDeep,
            format!(
                "value nesting exceeds {}",
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH
            ),
        ));
    }
    Ok(())
}

fn validate_text_value(value: &str, label: &str) -> Result<(), ChcGroundDerivationArtifactError> {
    if value.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::StringOrTokenTooLarge,
            format!(
                "{label} has {} bytes, maximum is {}",
                value.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES
            ),
        ));
    }
    Ok(())
}

fn validate_array_index_sort(sort: &ChcSort) -> Result<(), ChcGroundDerivationArtifactError> {
    if matches!(
        sort,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)
    ) {
        return Ok(());
    }
    Err(error(
        ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
        format!("artifact v1 supports only Bool/Int/Real/BitVec array indices, found {sort}"),
    ))
}

#[cfg(test)]
fn encode_value(
    value: &SmtValue,
    expected_sort: &ChcSort,
    depth: usize,
    value_nodes: &mut usize,
) -> Result<WireValue, ChcGroundDerivationArtifactError> {
    encode_value_with_control(
        value,
        expected_sort,
        depth,
        value_nodes,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn encode_value_with_control(
    value: &SmtValue,
    expected_sort: &ChcSort,
    depth: usize,
    value_nodes: &mut usize,
    control: &mut GroundValidationControl<'_>,
) -> Result<WireValue, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    validate_value_depth(depth)?;
    increment_count(
        value_nodes,
        CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES,
        ChcGroundDerivationArtifactErrorReason::TooManyValueNodes,
        "value node",
    )?;

    let encoded = match (value, expected_sort) {
        (SmtValue::Bool(value), ChcSort::Bool) => Ok(WireValue::Bool { value: *value }),
        (SmtValue::Int(value), ChcSort::Int) => Ok(WireValue::Int {
            decimal: decoding_phase(control, || value.to_string())?,
        }),
        (SmtValue::BigInt(value), ChcSort::Int) => Ok(WireValue::Int {
            decimal: decoding_phase(control, || value.to_string())?,
        }),
        (SmtValue::Real(value), ChcSort::Real) => Ok(WireValue::Real {
            numerator: decoding_phase(control, || value.numer().to_string())?,
            denominator: decoding_phase(control, || value.denom().to_string())?,
        }),
        (SmtValue::BitVec(_, width) | SmtValue::BigBitVec(_, width), ChcSort::BitVec(expected))
            if width == expected =>
        {
            let Some((value, canonical_width)) =
                decoding_phase(control, || value.bitvec_to_biguint())?
            else {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "bitvector width is outside AY's public bound",
                ));
            };
            Ok(WireValue::Bitvector {
                width: canonical_width,
                value_hex: decoding_phase(control, || value.to_str_radix(16))?,
            })
        }
        (SmtValue::ConstArray(default), ChcSort::Array(index_sort, value_sort)) => {
            decoding_phase(control, || validate_array_index_sort(index_sort))??;
            Ok(WireValue::ConstArray {
                default: Box::new(encode_value_with_control(
                    default,
                    value_sort,
                    depth + 1,
                    value_nodes,
                    control,
                )?),
            })
        }
        (SmtValue::ArrayMap { default, entries }, ChcSort::Array(index_sort, value_sort)) => {
            decoding_phase(control, || validate_array_index_sort(index_sort))??;
            let default = Box::new(encode_value_with_control(
                default,
                value_sort,
                depth + 1,
                value_nodes,
                control,
            )?);
            let entries = entries
                .iter()
                .map(|(index, value)| {
                    Ok(WireArrayEntry {
                        index: encode_value_with_control(
                            index,
                            index_sort,
                            depth + 1,
                            value_nodes,
                            control,
                        )?,
                        value: encode_value_with_control(
                            value,
                            value_sort,
                            depth + 1,
                            value_nodes,
                            control,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
            Ok(WireValue::ArrayMap { default, entries })
        }
        (SmtValue::Datatype(constructor, fields), ChcSort::Datatype { constructors, .. }) => {
            validate_text_value(constructor, "datatype constructor")?;
            let mut definition = None;
            for candidate in constructors.iter() {
                control.poll().map_err(interruption_error)?;
                if decoding_phase(control, || candidate.name == *constructor)? {
                    definition = Some(candidate);
                    break;
                }
            }
            let Some(definition) = definition else {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!("datatype constructor `{constructor}` is not in the source sort"),
                ));
            };
            if fields.len() != definition.selectors.len() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!(
                        "datatype constructor `{constructor}` has {} fields, expected {}",
                        fields.len(),
                        definition.selectors.len()
                    ),
                ));
            }
            let fields = fields
                .iter()
                .zip(&definition.selectors)
                .map(|(field, selector)| {
                    encode_value_with_control(
                        field,
                        &selector.sort,
                        depth + 1,
                        value_nodes,
                        control,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(WireValue::Datatype {
                constructor: decoding_phase(control, || constructor.clone())?,
                fields,
            })
        }
        (SmtValue::Opaque(_), _) => Err(error(
            ChcGroundDerivationArtifactErrorReason::OpaqueValue,
            "opaque solver placeholders are not concrete portable values",
        )),
        (_, ChcSort::Uninterpreted(name)) => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("uninterpreted sort `{name}` has no portable concrete value encoding"),
        )),
        _ => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("value {value:?} does not match source sort {expected_sort}"),
        )),
    };
    control.poll().map_err(interruption_error)?;
    encoded
}

#[cfg(test)]
fn canonical_decimal(value: &str) -> bool {
    if value == "0" {
        return true;
    }
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty()
        && !digits.starts_with('0')
        && digits.as_bytes().iter().all(u8::is_ascii_digit)
}

/// Poll around an individually opaque numeric, hashing or allocation phase.
/// This is cooperative cancellation, not an operation-duration bound.
fn decoding_phase<T>(
    control: &mut GroundValidationControl<'_>,
    phase: impl FnOnce() -> T,
) -> Result<T, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let value = phase();
    control.poll().map_err(interruption_error)?;
    Ok(value)
}

fn canonical_decimal_with_control(
    value: &str,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let digits = value.strip_prefix('-').unwrap_or(value);
    let mut canonical = value == "0" || (!digits.is_empty() && !digits.starts_with('0'));
    if canonical {
        for chunk in digits.as_bytes().chunks(4096) {
            control.poll().map_err(interruption_error)?;
            if !chunk.iter().all(u8::is_ascii_digit) {
                canonical = false;
                break;
            }
        }
    }
    control.poll().map_err(interruption_error)?;
    Ok(canonical)
}

fn parse_canonical_bigint_with_control(
    value: &str,
    label: &str,
    control: &mut GroundValidationControl<'_>,
) -> Result<BigInt, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    validate_text_value(value, label)?;
    if !canonical_decimal_with_control(value, control)? {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            format!("{label} is not canonical decimal"),
        ));
    }
    decoding_phase(control, || BigInt::parse_bytes(value.as_bytes(), 10))?.ok_or_else(|| {
        error(
            ChcGroundDerivationArtifactErrorReason::InvalidValue,
            format!("{label} is not an integer"),
        )
    })
}

#[cfg(test)]
fn canonical_hex(value: &str) -> bool {
    !value.is_empty()
        && (value == "0" || !value.starts_with('0'))
        && value
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn canonical_hex_with_control(
    value: &str,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let mut canonical = !value.is_empty() && (value == "0" || !value.starts_with('0'));
    if canonical {
        for chunk in value.as_bytes().chunks(4096) {
            control.poll().map_err(interruption_error)?;
            if !chunk
                .iter()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
            {
                canonical = false;
                break;
            }
        }
    }
    control.poll().map_err(interruption_error)?;
    Ok(canonical)
}

#[cfg(test)]
fn decode_value(
    value: &WireValue,
    expected_sort: &ChcSort,
    depth: usize,
    value_nodes: &mut usize,
) -> Result<SmtValue, ChcGroundDerivationArtifactError> {
    decode_value_with_control(
        value,
        expected_sort,
        depth,
        value_nodes,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn decode_value_with_control(
    value: &WireValue,
    expected_sort: &ChcSort,
    depth: usize,
    value_nodes: &mut usize,
    control: &mut GroundValidationControl<'_>,
) -> Result<SmtValue, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    validate_value_depth(depth)?;
    increment_count(
        value_nodes,
        CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES,
        ChcGroundDerivationArtifactErrorReason::TooManyValueNodes,
        "value node",
    )?;

    let decoded = match (value, expected_sort) {
        (WireValue::Bool { value }, ChcSort::Bool) => Ok(SmtValue::Bool(*value)),
        (WireValue::Int { decimal }, ChcSort::Int) => {
            let value = parse_canonical_bigint_with_control(decimal, "integer value", control)?;
            decoding_phase(control, || SmtValue::int_from_bigint(value))
        }
        (
            WireValue::Real {
                numerator,
                denominator,
            },
            ChcSort::Real,
        ) => {
            let numerator =
                parse_canonical_bigint_with_control(numerator, "real numerator", control)?;
            let denominator =
                parse_canonical_bigint_with_control(denominator, "real denominator", control)?;
            if denominator.is_zero() || denominator.is_negative() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "real denominator must be positive",
                ));
            }
            let rational = decoding_phase(control, || BigRational::new(numerator, denominator))?;
            let WireValue::Real {
                numerator,
                denominator,
            } = value
            else {
                unreachable!("matched real value above")
            };
            if decoding_phase(control, || rational.numer().to_string())? != *numerator
                || decoding_phase(control, || rational.denom().to_string())? != *denominator
            {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "real value is not reduced canonical rational form",
                ));
            }
            Ok(SmtValue::Real(rational))
        }
        (WireValue::Bitvector { width, value_hex }, ChcSort::BitVec(expected_width)) => {
            validate_text_value(value_hex, "bitvector hexadecimal value")?;
            if width != expected_width || *width == 0 || *width > crate::MAX_BITVECTOR_WIDTH {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!("bitvector width {width} does not match source width {expected_width}"),
                ));
            }
            if !canonical_hex_with_control(value_hex, control)? {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "bitvector value is not canonical lowercase hexadecimal",
                ));
            }
            let parsed =
                decoding_phase(control, || BigUint::parse_bytes(value_hex.as_bytes(), 16))?
                    .ok_or_else(|| {
                        error(
                            ChcGroundDerivationArtifactErrorReason::InvalidValue,
                            "bitvector value is not hexadecimal",
                        )
                    })?;
            if parsed.bits() > u64::from(*width) {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::InvalidValue,
                    "bitvector value has set bits outside its declared width",
                ));
            }
            decoding_phase(control, || SmtValue::bitvec_from_biguint(parsed, *width))
        }
        (WireValue::ConstArray { default }, ChcSort::Array(index_sort, value_sort)) => {
            validate_array_index_sort(index_sort)?;
            Ok(SmtValue::ConstArray(Box::new(decode_value_with_control(
                default,
                value_sort,
                depth + 1,
                value_nodes,
                control,
            )?)))
        }
        (WireValue::ArrayMap { default, entries }, ChcSort::Array(index_sort, value_sort)) => {
            validate_array_index_sort(index_sort)?;
            let default = Box::new(decode_value_with_control(
                default,
                value_sort,
                depth + 1,
                value_nodes,
                control,
            )?);
            let entries = entries
                .iter()
                .map(|entry| {
                    control.poll().map_err(interruption_error)?;
                    Ok((
                        decode_value_with_control(
                            &entry.index,
                            index_sort,
                            depth + 1,
                            value_nodes,
                            control,
                        )?,
                        decode_value_with_control(
                            &entry.value,
                            value_sort,
                            depth + 1,
                            value_nodes,
                            control,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
            Ok(SmtValue::ArrayMap { default, entries })
        }
        (
            WireValue::Datatype {
                constructor,
                fields,
            },
            ChcSort::Datatype { constructors, .. },
        ) => {
            validate_text_value(constructor, "datatype constructor")?;
            let mut matched = None;
            for definition in constructors.iter() {
                control.poll().map_err(interruption_error)?;
                if definition.name == *constructor {
                    matched = Some(definition);
                    break;
                }
            }
            let Some(definition) = matched else {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!("datatype constructor `{constructor}` is not in the source sort"),
                ));
            };
            if fields.len() != definition.selectors.len() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
                    format!(
                        "datatype constructor `{constructor}` has {} fields, expected {}",
                        fields.len(),
                        definition.selectors.len()
                    ),
                ));
            }
            let fields = fields
                .iter()
                .zip(&definition.selectors)
                .map(|(field, selector)| {
                    decode_value_with_control(
                        field,
                        &selector.sort,
                        depth + 1,
                        value_nodes,
                        control,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SmtValue::Datatype(constructor.clone(), fields))
        }
        (_, ChcSort::Uninterpreted(name)) => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("uninterpreted sort `{name}` has no portable concrete value encoding"),
        )),
        _ => Err(error(
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch,
            format!("wire value does not match source sort {expected_sort}"),
        )),
    }?;
    control.poll().map_err(interruption_error)?;
    Ok(decoded)
}

struct SourceSurfacePreflight<'a> {
    cache: GroundSourceSurfaceCache<'a>,
    binding_count: usize,
    uf_observation_count: usize,
}

fn map_source_surface_error(
    step_index: usize,
    clause_index: usize,
    surface_error: GroundSourceSurfaceError,
) -> ChcGroundDerivationArtifactError {
    match surface_error {
        GroundSourceSurfaceError::Interrupted => interruption_error(GroundValidationInterrupted),
        GroundSourceSurfaceError::ClauseOutOfRange => error(
            ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
            format!(
                "step {step_index} clause index {clause_index} is outside the supplied problem"
            ),
        ),
        GroundSourceSurfaceError::SourceWorkLimitExceeded => error(
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded,
            format!(
                "source-surface work exceeds {}",
                super::CHC_GROUND_DERIVATION_MAX_SOURCE_WORK
            ),
        ),
        GroundSourceSurfaceError::InvalidVariableSurface => error(
            ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
            format!("step {step_index} source clause has an invalid variable surface"),
        ),
        GroundSourceSurfaceError::PrivateSourceNamespace => error(
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
            format!("step {step_index} source clause uses AY's private environment namespace"),
        ),
        GroundSourceSurfaceError::InvalidUfSurface => error(
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
            format!("step {step_index} source clause has an invalid ordinary-UF surface"),
        ),
    }
}

#[cfg(test)]
fn preflight_source_surfaces<'a>(
    problem: &'a ChcProblem,
    clause_indices: &[usize],
) -> Result<SourceSurfacePreflight<'a>, ChcGroundDerivationArtifactError> {
    preflight_source_surfaces_with_control(
        problem,
        clause_indices,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn preflight_source_surfaces_with_control<'a>(
    problem: &'a ChcProblem,
    clause_indices: &[usize],
    control: &mut GroundValidationControl<'_>,
) -> Result<SourceSurfacePreflight<'a>, ChcGroundDerivationArtifactError> {
    let mut cache = decoding_phase(control, || GroundSourceSurfaceCache::new(problem))?;
    let mut binding_count = 0usize;
    let mut uf_observation_count = 0usize;
    let mut validated_source_names =
        decoding_phase(control, || vec![false; problem.clauses().len()])?;
    for (step_index, clause_index) in clause_indices.iter().copied().enumerate() {
        control.poll().map_err(interruption_error)?;
        let (variables, applications) = cache
            .charge_step_reuse_with_control(clause_index, control)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?;
        control.poll().map_err(interruption_error)?;
        if !validated_source_names[clause_index] {
            for variable in &cache
                .surface_with_control(clause_index, control)
                .map_err(|surface_error| {
                    map_source_surface_error(step_index, clause_index, surface_error)
                })?
                .variables
            {
                control.poll().map_err(interruption_error)?;
                validate_text_value(&variable.name, "source variable name")?;
            }
            validated_source_names[clause_index] = true;
        }
        add_count(
            &mut binding_count,
            variables,
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_BINDINGS,
            ChcGroundDerivationArtifactErrorReason::TooManyBindings,
            "binding",
        )?;
        add_count(
            &mut uf_observation_count,
            applications,
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_UF_OBSERVATIONS,
            ChcGroundDerivationArtifactErrorReason::TooManyUfObservations,
            "UF observation",
        )?;
    }
    control.poll().map_err(interruption_error)?;
    Ok(SourceSurfacePreflight {
        cache,
        binding_count,
        uf_observation_count,
    })
}

#[cfg(test)]
fn preflight_derivation_scalar_work(
    cache: &mut GroundSourceSurfaceCache<'_>,
    derivation: &GroundDerivation,
) -> Result<(), ChcGroundDerivationArtifactError> {
    for (step_index, step) in derivation.steps.iter().enumerate() {
        cache
            .charge_step_scalar_replay(step.clause_index, &step.env, &[])
            .map_err(|surface_error| {
                map_source_surface_error(step_index, step.clause_index, surface_error)
            })?;
    }
    Ok(())
}

fn private_uf_model_key(name: &str) -> bool {
    use crate::expr::evaluate::UF_APPLICATION_MODEL_MARKER_KEY;

    name == UF_APPLICATION_MODEL_MARKER_KEY
        || name.starts_with("\0ay.uf-application-value:")
        || name.starts_with("\0ay.uf-concrete-application-value:")
}

fn scalar_uf_sort(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)
    )
}

fn scalar_value_matches_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    match (value, sort) {
        (SmtValue::Bool(_), ChcSort::Bool) | (SmtValue::Int(_), ChcSort::Int) => true,
        (SmtValue::BigInt(value), ChcSort::Int) => {
            num_traits::ToPrimitive::to_i128(value.as_ref()).is_none()
        }
        (SmtValue::Real(value), ChcSort::Real) => canonical_real_value(value),
        (SmtValue::BitVec(value, width), ChcSort::BitVec(expected_width)) => {
            if width != expected_width || *width == 0 || *width > 128 {
                return false;
            }
            let normalized = match *width {
                128 => *value,
                _ => *value & ((1u128 << *width) - 1),
            };
            normalized == *value
        }
        (SmtValue::BigBitVec(value, width), ChcSort::BitVec(expected_width)) => {
            width == expected_width
                && *width > 128
                && *width <= crate::MAX_BITVECTOR_WIDTH
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    }
}

fn canonical_real_value(value: &BigRational) -> bool {
    if value.denom().sign() != num_bigint::Sign::Plus {
        return false;
    }
    let reduced = BigRational::new(value.numer().clone(), value.denom().clone());
    reduced.numer() == value.numer() && reduced.denom() == value.denom()
}

#[cfg(test)]
fn install_authenticated_uf_observations(
    step_index: usize,
    applications: &[ChcExpr],
    results: &[SmtValue],
    env: &mut FxHashMap<String, SmtValue>,
    global_congruence: &mut FxHashMap<GroundUfCongruenceKey, SmtValue>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    install_authenticated_uf_observations_with_control(
        step_index,
        applications,
        results,
        env,
        global_congruence,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn install_authenticated_uf_observations_with_control(
    step_index: usize,
    applications: &[ChcExpr],
    results: &[SmtValue],
    env: &mut FxHashMap<String, SmtValue>,
    global_congruence: &mut FxHashMap<GroundUfCongruenceKey, SmtValue>,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    use crate::expr::evaluate::{
        uf_application_model_key, UF_APPLICATION_MODEL_MARKER_KEY,
        UF_APPLICATION_MODEL_MARKER_VALUE,
    };

    control.poll().map_err(interruption_error)?;
    if applications.len() != results.len() {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch,
            format!(
                "step {step_index} has {} UF results for {} source applications",
                results.len(),
                applications.len()
            ),
        ));
    }
    for (application_index, (application, result)) in applications.iter().zip(results).enumerate() {
        control.poll().map_err(interruption_error)?;
        let ChcExpr::FuncApp(_, return_sort, arguments) = application else {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                format!("step {step_index} application {application_index} is not a function"),
            ));
        };
        let mut scalar_signature = scalar_uf_sort(return_sort);
        if scalar_signature {
            for argument in arguments {
                control.poll().map_err(interruption_error)?;
                if !decoding_phase(control, || scalar_uf_sort(&argument.sort()))? {
                    scalar_signature = false;
                    break;
                }
            }
        }
        if !scalar_signature {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                format!(
                    "step {step_index} application {application_index} has a non-scalar signature"
                ),
            ));
        }
        if !decoding_phase(control, || scalar_value_matches_sort(result, return_sort))? {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                format!(
                    "step {step_index} application {application_index} result has the wrong sort"
                ),
            ));
        }
        let Some(key) = decoding_phase(control, || uf_application_model_key(application))? else {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                format!("step {step_index} application {application_index} has no exact key"),
            ));
        };
        if decoding_phase(control, || {
            env.insert(key, result.clone()).is_some_and(|previous| {
                crate::expr::evaluate::smt_values_equal(&previous, result) != Some(true)
            })
        })? {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UfCongruenceViolation,
                format!(
                    "step {step_index} application {application_index} repeats an exact term with a different result"
                ),
            ));
        }
    }
    if !applications.is_empty() {
        decoding_phase(control, || {
            env.insert(
                UF_APPLICATION_MODEL_MARKER_KEY.to_string(),
                SmtValue::Opaque(UF_APPLICATION_MODEL_MARKER_VALUE.to_string()),
            );
        })?;
    }

    for (application_index, (application, result)) in applications.iter().zip(results).enumerate() {
        control.poll().map_err(interruption_error)?;
        let ChcExpr::FuncApp(_, _, arguments) = application else {
            unreachable!("ordinary-UF application shape checked above")
        };
        let mut argument_values = decoding_phase(control, || Vec::with_capacity(arguments.len()))?;
        for argument in arguments {
            control.poll().map_err(interruption_error)?;
            let value = super::eval_ground_with_control(argument, env, control)
                .map_err(map_v2_derivation_error)?
                .ok_or_else(|| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                        format!(
                            "step {step_index} application {application_index} arguments are not ground"
                        ),
                    )
                })?;
            argument_values.push(value);
        }
        let Some(key) = decoding_phase(control, || {
            ground_uf_congruence_key(application, &argument_values)
        })?
        else {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                format!(
                    "step {step_index} application {application_index} has no scalar congruence key"
                ),
            ));
        };
        if decoding_phase(control, || {
            global_congruence.get(&key).is_some_and(|previous| {
                crate::expr::evaluate::smt_values_equal(previous, result) != Some(true)
            })
        })? {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::UfCongruenceViolation,
                format!(
                    "step {step_index} application {application_index} conflicts at equal concrete arguments"
                ),
            ));
        }
        decoding_phase(control, || {
            global_congruence
                .entry(key)
                .or_insert_with(|| result.clone());
        })?;
    }
    control.poll().map_err(interruption_error)?;
    Ok(())
}

#[cfg(test)]
fn wire_steps_from_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(Vec<WireStep>, ContentCounts), ChcGroundDerivationArtifactError> {
    wire_steps_from_derivation_with_control(
        problem,
        derivation,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn wire_steps_from_derivation_with_control(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &mut GroundValidationControl<'_>,
) -> Result<(Vec<WireStep>, ContentCounts), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if derivation.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "derivation has {} steps, maximum is {}",
                derivation.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = derivation
        .steps
        .iter()
        .map(|step| {
            control.poll().map_err(interruption_error)?;
            Ok(step.clause_index)
        })
        .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        ..
    } = preflight_source_surfaces_with_control(problem, &clause_indices, control)?;
    for (step_index, step) in derivation.steps.iter().enumerate() {
        decoding_phase(control, || {
            cache.charge_step_scalar_replay(step.clause_index, &step.env, &[])
        })?
        .map_err(|surface_error| {
            map_source_surface_error(step_index, step.clause_index, surface_error)
        })?;
    }
    let mut counts = ContentCounts {
        bindings: binding_count,
        ..ContentCounts::default()
    };
    for step in &derivation.steps {
        control.poll().map_err(interruption_error)?;
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut steps = decoding_phase(control, || Vec::with_capacity(derivation.steps.len()))?;
    for (step_index, step) in derivation.steps.iter().enumerate() {
        control.poll().map_err(interruption_error)?;
        for name in step.env.keys() {
            control.poll().map_err(interruption_error)?;
            validate_text_value(name, "binding name")?;
            if name.starts_with('\0') {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                    format!(
                        "step {step_index} contains a private UF observation; artifact v1 \
                         supports only ordinary source-variable bindings"
                    ),
                ));
            }
        }

        let variables = &cache
            .surface_with_control(step.clause_index, control)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, step.clause_index, surface_error)
            })?
            .variables;
        if variables.len() != step.env.len() {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                format!(
                    "step {step_index} has {} bindings, source clause {} requires {}",
                    step.env.len(),
                    step.clause_index,
                    variables.len()
                ),
            ));
        }
        let bindings = variables
            .iter()
            .map(|variable| {
                control.poll().map_err(interruption_error)?;
                let Some(value) = decoding_phase(control, || step.env.get(&variable.name))? else {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!(
                            "step {step_index} omits source variable `{}`",
                            variable.name
                        ),
                    ));
                };
                Ok(WireBinding {
                    name: decoding_phase(control, || variable.name.clone())?,
                    value: encode_value_with_control(
                        value,
                        &variable.sort,
                        1,
                        &mut counts.value_nodes,
                        control,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        let premises = step
            .premises
            .iter()
            .map(|premise| {
                control.poll().map_err(interruption_error)?;
                checked_u32(*premise, "premise index")
            })
            .collect::<Result<Vec<_>, _>>()?;
        steps.push(WireStep {
            clause_index: checked_u32(step.clause_index, "clause index")?,
            premises,
            bindings,
        });
    }
    control.poll().map_err(interruption_error)?;
    Ok((steps, counts))
}

#[cfg(test)]
fn wire_steps_v2_from_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(Vec<WireStepV2>, ContentCounts), ChcGroundDerivationArtifactError> {
    wire_steps_v2_from_derivation_with_control(
        problem,
        derivation,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn wire_steps_v2_from_derivation_with_control(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &mut GroundValidationControl<'_>,
) -> Result<(Vec<WireStepV2>, ContentCounts), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if derivation.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "derivation has {} steps, maximum is {}",
                derivation.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = derivation
        .steps
        .iter()
        .map(|step| {
            control.poll().map_err(interruption_error)?;
            Ok(step.clause_index)
        })
        .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        uf_observation_count,
    } = preflight_source_surfaces_with_control(problem, &clause_indices, control)?;
    for (step_index, step) in derivation.steps.iter().enumerate() {
        decoding_phase(control, || {
            cache.charge_step_scalar_replay(step.clause_index, &step.env, &[])
        })?
        .map_err(|surface_error| {
            map_source_surface_error(step_index, step.clause_index, surface_error)
        })?;
    }
    let mut counts = ContentCounts {
        bindings: binding_count,
        uf_observations: uf_observation_count,
        ..ContentCounts::default()
    };
    for step in &derivation.steps {
        control.poll().map_err(interruption_error)?;
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut global_congruence = FxHashMap::default();
    let mut steps = decoding_phase(control, || Vec::with_capacity(derivation.steps.len()))?;
    for (step_index, step) in derivation.steps.iter().enumerate() {
        control.poll().map_err(interruption_error)?;
        let surface = cache
            .surface_with_control(step.clause_index, control)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, step.clause_index, surface_error)
            })?;
        let variables = &surface.variables;
        let applications = &surface.uf_applications;
        let mut variable_names: FxHashSet<&str> = FxHashSet::default();
        for variable in variables {
            decoding_phase(control, || variable_names.insert(variable.name.as_str()))?;
        }
        for name in step.env.keys() {
            control.poll().map_err(interruption_error)?;
            validate_text_value(name, "binding name")?;
            if !decoding_phase(control, || variable_names.contains(name.as_str()))?
                && !private_uf_model_key(name)
            {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                    format!(
                        "step {step_index} environment entry `{name}` is neither a source variable nor finite-UF metadata"
                    ),
                ));
            }
        }
        let mut authenticated_env = FxHashMap::default();
        let bindings = variables
            .iter()
            .map(|variable| {
                control.poll().map_err(interruption_error)?;
                let Some(value) = decoding_phase(control, || step.env.get(&variable.name))? else {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!(
                            "step {step_index} omits source variable `{}`",
                            variable.name
                        ),
                    ));
                };
                decoding_phase(control, || {
                    authenticated_env.insert(variable.name.clone(), value.clone())
                })?;
                Ok(WireBinding {
                    name: decoding_phase(control, || variable.name.clone())?,
                    value: encode_value_with_control(
                        value,
                        &variable.sort,
                        1,
                        &mut counts.value_nodes,
                        control,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;

        let results = applications
            .iter()
            .enumerate()
            .map(|(application_index, application)| {
                control.poll().map_err(interruption_error)?;
                super::eval_ground_with_control(application, &step.env, control)
                    .map_err(map_v2_derivation_error)?
                    .ok_or_else(|| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::UfObservationNotGround,
                        format!(
                            "step {step_index} application {application_index} has no exact source observation"
                        ),
                    )
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        install_authenticated_uf_observations_with_control(
            step_index,
            applications,
            &results,
            &mut authenticated_env,
            &mut global_congruence,
            control,
        )?;
        let uf_observations = applications
            .iter()
            .zip(&results)
            .enumerate()
            .map(|(application_index, (application, result))| {
                control.poll().map_err(interruption_error)?;
                let ChcExpr::FuncApp(_, return_sort, _) = application else {
                    unreachable!("ordinary-UF collector returned a function application")
                };
                Ok(WireUfObservation {
                    application_ordinal: checked_u32(application_index, "UF application ordinal")?,
                    result: encode_value_with_control(
                        result,
                        return_sort,
                        1,
                        &mut counts.value_nodes,
                        control,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
        let premises = step
            .premises
            .iter()
            .map(|premise| {
                control.poll().map_err(interruption_error)?;
                checked_u32(*premise, "premise index")
            })
            .collect::<Result<Vec<_>, _>>()?;
        steps.push(WireStepV2 {
            clause_index: checked_u32(step.clause_index, "clause index")?,
            premises,
            bindings,
            uf_observations,
        });
    }
    control.poll().map_err(interruption_error)?;
    Ok((steps, counts))
}

#[cfg(test)]
fn derivation_from_wire_steps(
    problem: &ChcProblem,
    steps: &[WireStep],
    query_step: u32,
) -> Result<(GroundDerivation, ContentCounts), ChcGroundDerivationArtifactError> {
    derivation_from_wire_steps_with_control(
        problem,
        steps,
        query_step,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn derivation_from_wire_steps_with_control(
    problem: &ChcProblem,
    steps: &[WireStep],
    query_step: u32,
    control: &mut GroundValidationControl<'_>,
) -> Result<(GroundDerivation, ContentCounts), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "artifact has {} steps, maximum is {}",
                steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = steps
        .iter()
        .enumerate()
        .map(|(step_index, step)| {
            control.poll().map_err(interruption_error)?;
            usize::try_from(step.clause_index).map_err(|_| {
                error(
                    ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
                    format!("step {step_index} clause index does not fit usize"),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        ..
    } = preflight_source_surfaces_with_control(problem, &clause_indices, control)?;
    let mut counts = ContentCounts {
        bindings: binding_count,
        ..ContentCounts::default()
    };
    for step in steps {
        control.poll().map_err(interruption_error)?;
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut decoded_steps = decoding_phase(control, || Vec::with_capacity(steps.len()))?;
    for (step_index, (step, clause_index)) in steps.iter().zip(clause_indices).enumerate() {
        control.poll().map_err(interruption_error)?;
        let variable_count = cache
            .surface(clause_index)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?
            .variables
            .len();
        control.poll().map_err(interruption_error)?;
        if step.bindings.len() != variable_count {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                format!(
                    "step {step_index} has {} bindings, source clause {clause_index} requires {}",
                    step.bindings.len(),
                    variable_count
                ),
            ));
        }
        let value_occurrences = step
            .bindings
            .iter()
            .map(|binding| wire_value_typecheck_occurrences_with_control(&binding.value, control))
            .collect::<Result<Vec<_>, _>>()?;
        control.poll().map_err(interruption_error)?;
        cache
            .charge_step_wire_type_replay(clause_index, &value_occurrences)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?;
        control.poll().map_err(interruption_error)?;
        let variables = &cache
            .surface(clause_index)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?
            .variables;
        control.poll().map_err(interruption_error)?;
        let mut env = FxHashMap::default();
        for (binding, variable) in step.bindings.iter().zip(variables) {
            control.poll().map_err(interruption_error)?;
            validate_text_value(&binding.name, "binding name")?;
            if binding.name.starts_with('\0') {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                    format!("step {step_index} binding uses AY's private UF namespace"),
                ));
            }
            if binding.name != variable.name {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                    format!(
                        "step {step_index} binding `{}` is not canonical source variable `{}`",
                        binding.name, variable.name
                    ),
                ));
            }
            let value = decode_value_with_control(
                &binding.value,
                &variable.sort,
                1,
                &mut counts.value_nodes,
                control,
            )?;
            if decoding_phase(control, || env.insert(binding.name.clone(), value))?.is_some() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                    format!("step {step_index} repeats binding `{}`", binding.name),
                ));
            }
        }
        control.poll().map_err(interruption_error)?;
        cache
            .charge_step_scalar_replay(clause_index, &env, &[])
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?;
        control.poll().map_err(interruption_error)?;
        let premises = step
            .premises
            .iter()
            .map(|premise| {
                control.poll().map_err(interruption_error)?;
                usize::try_from(*premise).map_err(|_| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
                        format!("step {step_index} premise index does not fit usize"),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        decoded_steps.push(GroundDerivationStep {
            clause_index,
            env,
            premises,
        });
    }
    let query_step = usize::try_from(query_step).map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
            "query step does not fit usize",
        )
    })?;
    control.poll().map_err(interruption_error)?;
    Ok((
        GroundDerivation {
            steps: decoded_steps,
            query_step,
        },
        counts,
    ))
}

#[cfg(test)]
fn derivation_from_wire_steps_v2(
    problem: &ChcProblem,
    steps: &[WireStepV2],
    query_step: u32,
) -> Result<(GroundDerivation, ContentCounts), ChcGroundDerivationArtifactError> {
    derivation_from_wire_steps_v2_with_control(
        problem,
        steps,
        query_step,
        &mut GroundValidationControl::new(&mut || true),
    )
}

fn derivation_from_wire_steps_v2_with_control(
    problem: &ChcProblem,
    steps: &[WireStepV2],
    query_step: u32,
    control: &mut GroundValidationControl<'_>,
) -> Result<(GroundDerivation, ContentCounts), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "artifact has {} steps, maximum is {}",
                steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }

    let clause_indices = steps
        .iter()
        .enumerate()
        .map(|(step_index, step)| {
            control.poll().map_err(interruption_error)?;
            usize::try_from(step.clause_index).map_err(|_| {
                error(
                    ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
                    format!("step {step_index} clause index does not fit usize"),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let SourceSurfacePreflight {
        mut cache,
        binding_count,
        uf_observation_count,
    } = preflight_source_surfaces_with_control(problem, &clause_indices, control)?;
    let mut counts = ContentCounts {
        bindings: binding_count,
        uf_observations: uf_observation_count,
        ..ContentCounts::default()
    };
    for step in steps {
        control.poll().map_err(interruption_error)?;
        add_count(
            &mut counts.premise_edges,
            step.premises.len(),
            CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES,
            ChcGroundDerivationArtifactErrorReason::TooManyPremiseEdges,
            "premise edge",
        )?;
    }
    let mut global_congruence = FxHashMap::default();
    let mut decoded_steps = decoding_phase(control, || Vec::with_capacity(steps.len()))?;
    for (step_index, (step, clause_index)) in steps.iter().zip(clause_indices).enumerate() {
        control.poll().map_err(interruption_error)?;
        let mut env = {
            let variable_count = cache
                .surface(clause_index)
                .map_err(|surface_error| {
                    map_source_surface_error(step_index, clause_index, surface_error)
                })?
                .variables
                .len();
            control.poll().map_err(interruption_error)?;
            if step.bindings.len() != variable_count {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                    format!(
                        "step {step_index} has {} bindings, source clause {clause_index} requires {}",
                        step.bindings.len(),
                        variable_count
                    ),
                ));
            }
            let value_occurrences = step
                .bindings
                .iter()
                .map(|binding| {
                    wire_value_typecheck_occurrences_with_control(&binding.value, control)
                })
                .collect::<Result<Vec<_>, _>>()?;
            control.poll().map_err(interruption_error)?;
            cache
                .charge_step_wire_type_replay(clause_index, &value_occurrences)
                .map_err(|surface_error| {
                    map_source_surface_error(step_index, clause_index, surface_error)
                })?;
            control.poll().map_err(interruption_error)?;
            let variables = &cache
                .surface(clause_index)
                .map_err(|surface_error| {
                    map_source_surface_error(step_index, clause_index, surface_error)
                })?
                .variables;
            control.poll().map_err(interruption_error)?;
            let mut env = FxHashMap::default();
            for (binding, variable) in step.bindings.iter().zip(variables) {
                control.poll().map_err(interruption_error)?;
                validate_text_value(&binding.name, "binding name")?;
                if binding.name.starts_with('\0') {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!("step {step_index} binding uses a private namespace"),
                    ));
                }
                if binding.name != variable.name {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!(
                            "step {step_index} binding `{}` is not canonical source variable `{}`",
                            binding.name, variable.name
                        ),
                    ));
                }
                let value = decode_value_with_control(
                    &binding.value,
                    &variable.sort,
                    1,
                    &mut counts.value_nodes,
                    control,
                )?;
                if decoding_phase(control, || env.insert(binding.name.clone(), value))?.is_some() {
                    return Err(error(
                        ChcGroundDerivationArtifactErrorReason::BindingSetMismatch,
                        format!("step {step_index} repeats binding `{}`", binding.name),
                    ));
                }
            }
            env
        };

        let (results, application_count, argument_occurrences, value_replay_occurrences) = {
            control.poll().map_err(interruption_error)?;
            let surface = cache.surface(clause_index).map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?;
            control.poll().map_err(interruption_error)?;
            let applications = &surface.uf_applications;
            if step.uf_observations.len() != applications.len() {
                return Err(error(
                    ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch,
                    format!(
                        "step {step_index} has {} UF observations, source clause requires {}",
                        step.uf_observations.len(),
                        applications.len()
                    ),
                ));
            }
            let results = step
                .uf_observations
                .iter()
                .zip(applications)
                .enumerate()
                .map(|(application_index, (observation, application))| {
                    control.poll().map_err(interruption_error)?;
                    if usize::try_from(observation.application_ordinal).ok()
                        != Some(application_index)
                    {
                        return Err(error(
                            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch,
                            format!(
                                "step {step_index} UF observation {application_index} has ordinal {}",
                                observation.application_ordinal
                            ),
                        ));
                    }
                    let ChcExpr::FuncApp(_, return_sort, _) = application else {
                        return Err(error(
                            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
                            format!(
                                "step {step_index} application {application_index} is not a function"
                            ),
                        ));
                    };
                    decode_value_with_control(
                        &observation.result,
                        return_sort,
                        1,
                        &mut counts.value_nodes,
                        control,
                    )
                })
                .collect::<Result<Vec<_>, ChcGroundDerivationArtifactError>>()?;
            (
                results,
                applications.len(),
                surface.uf_argument_occurrences,
                surface.value_replay_occurrences,
            )
        };
        control.poll().map_err(interruption_error)?;
        cache
            .charge_scalar_replay(
                application_count,
                argument_occurrences,
                value_replay_occurrences,
                &env,
                &results,
            )
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?;
        control.poll().map_err(interruption_error)?;
        let applications = &cache
            .surface(clause_index)
            .map_err(|surface_error| {
                map_source_surface_error(step_index, clause_index, surface_error)
            })?
            .uf_applications;
        control.poll().map_err(interruption_error)?;
        install_authenticated_uf_observations_with_control(
            step_index,
            applications,
            &results,
            &mut env,
            &mut global_congruence,
            control,
        )?;

        let premises = step
            .premises
            .iter()
            .map(|premise| {
                control.poll().map_err(interruption_error)?;
                usize::try_from(*premise).map_err(|_| {
                    error(
                        ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
                        format!("step {step_index} premise index does not fit usize"),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        decoded_steps.push(GroundDerivationStep {
            clause_index,
            env,
            premises,
        });
    }
    let query_step = usize::try_from(query_step).map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::IndexOutOfRange,
            "query step does not fit usize",
        )
    })?;
    control.poll().map_err(interruption_error)?;
    Ok((
        GroundDerivation {
            steps: decoded_steps,
            query_step,
        },
        counts,
    ))
}

#[cfg(test)]
fn test_normalized_input_schema(problem: &ChcProblem) -> &'static str {
    crate::normalized_chc_input_schema_of(&crate::normalized_chc_input(problem))
        .expect("normalized input names its schema")
}

#[cfg(test)]
fn envelope_for_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<GroundDerivationEnvelope, ChcGroundDerivationArtifactError> {
    validate_problem_bounds(problem)?;
    let (steps, counts) = wire_steps_from_derivation(problem, derivation)?;
    GroundDerivationEnvelope::from_parts(
        steps,
        counts,
        derivation.query_step,
        test_normalized_input_schema(problem),
        normalized_chc_input_sha256(problem),
        ordered_chc_clause_sequence_sha256(problem),
    )
}

#[cfg(test)]
fn envelope_v2_for_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<GroundDerivationEnvelopeV2, ChcGroundDerivationArtifactError> {
    validate_problem_bounds(problem)?;
    let (steps, counts) = wire_steps_v2_from_derivation(problem, derivation)?;
    GroundDerivationEnvelopeV2::from_parts(
        steps,
        counts,
        derivation.query_step,
        test_normalized_input_schema(problem),
        normalized_chc_input_sha256(problem),
        ordered_chc_clause_sequence_sha256(problem),
    )
}

fn map_derivation_error(error_value: GroundDerivationError) -> ChcGroundDerivationArtifactError {
    if matches!(error_value, GroundDerivationError::Interrupted) {
        return interruption_error(GroundValidationInterrupted);
    }
    error(
        ChcGroundDerivationArtifactErrorReason::DerivationRejected,
        error_value.to_string(),
    )
}

fn map_v2_derivation_error(error_value: GroundDerivationError) -> ChcGroundDerivationArtifactError {
    let reason = match &error_value {
        GroundDerivationError::Interrupted => ChcGroundDerivationArtifactErrorReason::Interrupted,
        GroundDerivationError::UfSurfaceInvalid { .. } => {
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
        }
        GroundDerivationError::UfObservationNotGround { .. } => {
            ChcGroundDerivationArtifactErrorReason::UfObservationNotGround
        }
        GroundDerivationError::UfCongruenceViolation { .. } => {
            ChcGroundDerivationArtifactErrorReason::UfCongruenceViolation
        }
        GroundDerivationError::SourceWorkLimitExceeded => {
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
        }
        GroundDerivationError::InvalidSourceProblem => {
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        }
        GroundDerivationError::Empty
        | GroundDerivationError::RootOutOfRange
        | GroundDerivationError::ClauseOutOfRange { .. }
        | GroundDerivationError::PremiseNotWellFounded { .. }
        | GroundDerivationError::PremiseArityMismatch { .. }
        | GroundDerivationError::PremisePredicateMismatch { .. }
        | GroundDerivationError::RootNotQuery { .. }
        | GroundDerivationError::NonRootIsQuery { .. }
        | GroundDerivationError::ConstraintNotGround { .. }
        | GroundDerivationError::ConstraintFalse { .. }
        | GroundDerivationError::VariableBindingMissing { .. }
        | GroundDerivationError::VariableBindingSortMismatch { .. }
        | GroundDerivationError::ArgumentNotGround { .. }
        | GroundDerivationError::ArgumentMismatch { .. }
        | GroundDerivationError::UnreachableStep { .. } => {
            ChcGroundDerivationArtifactErrorReason::DerivationRejected
        }
    };
    error(reason, error_value.to_string())
}

pub(crate) fn encode_ground_derivation_artifact(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    producer::encode_v1_with_control(
        problem,
        derivation,
        &mut GroundValidationControl::new(&mut || true),
    )
}

pub(crate) fn encode_ground_derivation_artifact_v2(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
    producer::encode_v2_with_control(
        problem,
        derivation,
        &mut GroundValidationControl::new(&mut || true),
    )
}

impl Counterexample {
    /// Serialize this counterexample's checked, fully-ground Unsafe derivation.
    ///
    /// Presence is not trusted: the candidate is first validated against
    /// `problem`, and the canonical bytes must then pass the same public
    /// consumer boundary before they are returned.
    pub fn ground_derivation_artifact(
        &self,
        problem: &ChcProblem,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        let Some(derivation) = &self.ground_derivation else {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation,
                "counterexample carries no fully-ground derivation",
            ));
        };
        encode_ground_derivation_artifact(problem, derivation)
    }

    /// Serialize source-authenticated finite-UF ground evidence using v2.
    pub fn ground_derivation_artifact_v2(
        &self,
        problem: &ChcProblem,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        let Some(derivation) = &self.ground_derivation else {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation,
                "counterexample carries no fully-ground derivation",
            ));
        };
        encode_ground_derivation_artifact_v2(problem, derivation)
    }
}

impl ChcPdrProofRun {
    /// Return canonical deciding Unsafe evidence when this run carries it.
    ///
    /// Safe/Unknown runs and legacy Unsafe runs without a fully-ground
    /// derivation return `Ok(None)`. A present but invalid or non-portable
    /// candidate is an error: callers may choose an independently sound legacy
    /// replay path, but must not mistake rejected evidence for absence.
    pub fn unsafe_ground_derivation_artifact_bytes(&self) -> ChcResult<Option<Vec<u8>>> {
        let VerifiedChcResult::Unsafe(verified) = self.result() else {
            return Ok(None);
        };
        match verified
            .counterexample()
            .ground_derivation_artifact(self.problem())
        {
            Ok(artifact) => Ok(Some(artifact.into_bytes())),
            Err(artifact_error)
                if artifact_error.reason
                    == ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation =>
            {
                Ok(None)
            }
            Err(artifact_error) => Err(ChcError::Verification(format!(
                "cannot serialize unsafe ground derivation: {artifact_error}"
            ))),
        }
    }

    /// Return canonical v2 deciding Unsafe evidence, including finite ordinary
    /// UF observations authenticated by the exact source clauses.
    pub fn unsafe_ground_derivation_artifact_v2_bytes(&self) -> ChcResult<Option<Vec<u8>>> {
        let VerifiedChcResult::Unsafe(verified) = self.result() else {
            return Ok(None);
        };
        match verified
            .counterexample()
            .ground_derivation_artifact_v2(self.problem())
        {
            Ok(artifact) => Ok(Some(artifact.into_bytes())),
            Err(artifact_error)
                if artifact_error.reason
                    == ChcGroundDerivationArtifactErrorReason::MissingGroundDerivation =>
            {
                Ok(None)
            }
            Err(artifact_error) => Err(ChcError::Verification(format!(
                "cannot serialize v2 unsafe ground derivation: {artifact_error}"
            ))),
        }
    }
}

/// Strictly parse, source-bind, and decide a durable ground derivation.
///
/// The returned capability is opaque and exists only after the reconstructed
/// derivation has passed [`validate_ground_derivation`] against `problem`.
/// Parsing is bounded before serde allocation/recursion, unknown fields and
/// non-canonical bytes are rejected, and bindings must exactly cover each
/// selected source clause's variables.
pub fn validate_chc_ground_derivation_artifact(
    problem: &ChcProblem,
    bytes: &[u8],
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    validate_chc_ground_derivation_artifact_with_progress(problem, bytes, &mut || true)
}

/// Validate v1 evidence with caller-owned cooperative cancellation.
///
/// The callback returns `true` to continue. A refusal is sticky and returns
/// [`ChcGroundDerivationArtifactErrorReason::Interrupted`], never validated
/// evidence. JSON transport and artifact hashing poll at bounded byte chunks;
/// source traversal/hashing, typed decoding and reconstruction poll nodes and
/// edges. Individual semantic validators, arithmetic, sorting and allocation
/// still have opaque intervals. Native checking supplies its own cooperative
/// boundaries. This is not a wall-clock latency guarantee or
/// an allocation-accounting API. No partial result is published on refusal.
/// Reader-based parsing may cost more than slice parsing; deployment throughput
/// and cancellation latency require measurement.
pub fn validate_chc_ground_derivation_artifact_with_progress(
    problem: &ChcProblem,
    bytes: &[u8],
    progress: &mut dyn FnMut() -> bool,
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    let mut control = GroundValidationControl::new(progress);
    validate_ground_artifact_with_control(problem, bytes, &mut control)
}

fn validate_ground_artifact_with_control(
    problem: &ChcProblem,
    bytes: &[u8],
    control: &mut GroundValidationControl<'_>,
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if bytes.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::ArtifactTooLarge,
            format!(
                "artifact has {} bytes, maximum is {}",
                bytes.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES
            ),
        ));
    }
    let sort_budget = validate_wire_problem(problem, control)?;
    control.poll().map_err(interruption_error)?;
    transport::validate_json_surface(bytes, control)?;
    let envelope: GroundDerivationEnvelope = transport::parse_envelope(bytes, control)?;
    transport::check_canonical_json(
        &envelope,
        bytes,
        "artifact JSON differs from AY's canonical field order/escaping",
        control,
    )?;
    if envelope.schema != CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA || envelope.schema_version != 1 {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
            format!(
                "unsupported schema/version `{}`/{}",
                envelope.schema, envelope.schema_version
            ),
        ));
    }
    if envelope.role != CHC_GROUND_DERIVATION_ARTIFACT_ROLE {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::RoleMismatch,
            format!("unexpected artifact role `{}`", envelope.role),
        ));
    }
    if crate::proof_metadata::normalized_chc_input_schema(&envelope.normalized_input_schema)
        .is_none()
    {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
            format!(
                "unsupported normalized-input schema `{}`",
                envelope.normalized_input_schema
            ),
        ));
    }
    control.poll().map_err(interruption_error)?;
    let identity = rebuild::AuthenticatedSource::check(
        problem,
        &envelope.normalized_input_schema,
        &envelope.normalized_input_sha256,
        &envelope.source_clause_sequence_sha256,
        "artifact",
        sort_budget,
        control,
    )?;
    if envelope.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "artifact has {} steps, maximum is {}",
                envelope.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }
    if envelope.step_count != checked_u64(envelope.steps.len(), "decoded step count")? {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::CountMismatch,
            "declared step count differs from decoded steps",
        ));
    }

    control.poll().map_err(interruption_error)?;
    let decoded = catch_unwind(AssertUnwindSafe(|| {
        derivation_from_wire_steps_with_control(
            problem,
            &envelope.steps,
            envelope.query_step,
            control,
        )
    }));
    control.poll().map_err(interruption_error)?;
    let decoded = decoded.map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
            "bounded ground-derivation decoding panicked",
        )
    })??;
    control.poll().map_err(interruption_error)?;
    let (derivation, counts) = decoded;
    if envelope.premise_edge_count != checked_u64(counts.premise_edges, "premise edge count")?
        || envelope.binding_count != checked_u64(counts.bindings, "binding count")?
        || envelope.value_node_count != checked_u64(counts.value_nodes, "value node count")?
    {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::CountMismatch,
            "one or more declared content counts differ from decoded content",
        ));
    }

    // Re-encode the typed values as well as the JSON envelope. This catches
    // non-canonical decimal/rational/BV spellings and any future decoder form
    // that serde's field-order round trip alone cannot normalize.
    control.poll().map_err(interruption_error)?;
    let rebuilt = identity.rebuild_v1(&derivation, control)?;
    control.poll().map_err(interruption_error)?;
    transport::check_canonical_json(
        &rebuilt,
        bytes,
        "decoded derivation does not round-trip to AY's canonical value encoding",
        control,
    )?;

    // The artifact digest is bookkeeping over the input bytes, so it is paid
    // BEFORE the decision: the derivation check is then the last work that
    // consults the caller (#completed-check-accepted).
    let artifact_sha256 = transport::sha256_hex(bytes, control)?;
    control.poll().map_err(interruption_error)?;
    let checked = catch_unwind(AssertUnwindSafe(|| {
        validate_ground_derivation_with_control(problem, &derivation, control)
    }));
    // #completed-check-accepted: consult the LATCH, not the caller. A refusal
    // the check observed stays final even if a validator swallowed it, but a
    // stop that arrives after its last poll neither discards a derivation it
    // accepted nor masks one it rejected.
    if control.is_stopped() {
        return Err(interruption_error(GroundValidationInterrupted));
    }
    checked
        .map_err(|_| {
            error(
                ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
                "native ground-derivation validation panicked",
            )
        })?
        .map_err(map_derivation_error)?;

    Ok(ChcValidatedGroundDerivation {
        artifact_schema: CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA,
        artifact_role: CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
        artifact_sha256,
        artifact_bytes: checked_u64(bytes.len(), "artifact byte length")?,
        normalized_input_sha256: envelope.normalized_input_sha256,
        source_clause_sequence_sha256: envelope.source_clause_sequence_sha256,
        step_count: derivation.steps.len(),
        query_step: derivation.query_step,
        premise_edge_count: counts.premise_edges,
        binding_count: counts.bindings,
        uf_observation_count: 0,
        value_node_count: counts.value_nodes,
        derivation,
    })
}

/// Strictly parse, source-bind, and decide a v2 finite-UF ground derivation.
///
/// V2 observations name no private evaluator keys. Each result is positionally
/// bound to the canonical ordinary-UF applications re-derived from the selected
/// source clause, and one derivation-wide congruence table is checked before
/// native validation can return positive authority.
pub fn validate_chc_ground_derivation_artifact_v2(
    problem: &ChcProblem,
    bytes: &[u8],
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    validate_chc_ground_derivation_artifact_v2_with_progress(problem, bytes, &mut || true)
}

/// Validate v2 finite-UF evidence with caller-owned cooperative cancellation.
///
/// This has the same sticky-refusal and phase-boundary limitations as
/// [`validate_chc_ground_derivation_artifact_with_progress`]. The callback is
/// not a proof assumption; refusal always prevents capability publication.
pub fn validate_chc_ground_derivation_artifact_v2_with_progress(
    problem: &ChcProblem,
    bytes: &[u8],
    progress: &mut dyn FnMut() -> bool,
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    let mut control = GroundValidationControl::new(progress);
    validate_ground_artifact_v2_with_control(problem, bytes, &mut control)
}

fn validate_ground_artifact_v2_with_control(
    problem: &ChcProblem,
    bytes: &[u8],
    control: &mut GroundValidationControl<'_>,
) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    if bytes.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::ArtifactTooLarge,
            format!(
                "artifact has {} bytes, maximum is {}",
                bytes.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES
            ),
        ));
    }
    let sort_budget = validate_wire_problem(problem, control)?;
    control.poll().map_err(interruption_error)?;
    transport::validate_json_surface(bytes, control)?;
    let envelope: GroundDerivationEnvelopeV2 = transport::parse_envelope(bytes, control)?;
    transport::check_canonical_json(
        &envelope,
        bytes,
        "v2 artifact JSON differs from AY's canonical field order/escaping",
        control,
    )?;
    if envelope.schema != CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA || envelope.schema_version != 2 {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
            format!(
                "unsupported v2 schema/version `{}`/{}",
                envelope.schema, envelope.schema_version
            ),
        ));
    }
    if envelope.role != CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::RoleMismatch,
            format!("unexpected v2 artifact role `{}`", envelope.role),
        ));
    }
    if crate::proof_metadata::normalized_chc_input_schema(&envelope.normalized_input_schema)
        .is_none()
    {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
            format!(
                "unsupported normalized-input schema `{}`",
                envelope.normalized_input_schema
            ),
        ));
    }
    control.poll().map_err(interruption_error)?;
    let identity = rebuild::AuthenticatedSource::check(
        problem,
        &envelope.normalized_input_schema,
        &envelope.normalized_input_sha256,
        &envelope.source_clause_sequence_sha256,
        "v2 artifact",
        sort_budget,
        control,
    )?;
    if envelope.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::TooManySteps,
            format!(
                "artifact has {} steps, maximum is {}",
                envelope.steps.len(),
                CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            ),
        ));
    }
    if envelope.step_count != checked_u64(envelope.steps.len(), "decoded step count")? {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::CountMismatch,
            "declared v2 step count differs from decoded steps",
        ));
    }

    control.poll().map_err(interruption_error)?;
    let decoded = catch_unwind(AssertUnwindSafe(|| {
        derivation_from_wire_steps_v2_with_control(
            problem,
            &envelope.steps,
            envelope.query_step,
            control,
        )
    }));
    control.poll().map_err(interruption_error)?;
    let decoded = decoded.map_err(|_| {
        error(
            ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
            "bounded v2 ground-derivation decoding panicked",
        )
    })??;
    control.poll().map_err(interruption_error)?;
    let (derivation, counts) = decoded;
    if envelope.premise_edge_count != checked_u64(counts.premise_edges, "premise edge count")?
        || envelope.binding_count != checked_u64(counts.bindings, "binding count")?
        || envelope.uf_observation_count
            != checked_u64(counts.uf_observations, "UF observation count")?
        || envelope.value_node_count != checked_u64(counts.value_nodes, "value node count")?
    {
        return Err(error(
            ChcGroundDerivationArtifactErrorReason::CountMismatch,
            "one or more declared v2 content counts differ from decoded content",
        ));
    }

    control.poll().map_err(interruption_error)?;
    let rebuilt = identity.rebuild_v2(&derivation, control)?;
    control.poll().map_err(interruption_error)?;
    transport::check_canonical_json(
        &rebuilt,
        bytes,
        "decoded v2 derivation does not round-trip to AY's canonical encoding",
        control,
    )?;

    // The artifact digest is bookkeeping over the input bytes, so it is paid
    // BEFORE the decision: the derivation check is then the last work that
    // consults the caller (#completed-check-accepted).
    let artifact_sha256 = transport::sha256_hex(bytes, control)?;
    control.poll().map_err(interruption_error)?;
    let checked = catch_unwind(AssertUnwindSafe(|| {
        validate_ground_derivation_with_control(problem, &derivation, control)
    }));
    // #completed-check-accepted: consult the LATCH, not the caller. A refusal
    // the check observed stays final even if a validator swallowed it, but a
    // stop that arrives after its last poll neither discards a derivation it
    // accepted nor masks one it rejected.
    if control.is_stopped() {
        return Err(interruption_error(GroundValidationInterrupted));
    }
    checked
        .map_err(|_| {
            error(
                ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
                "native v2 ground-derivation validation panicked",
            )
        })?
        .map_err(map_v2_derivation_error)?;

    Ok(ChcValidatedGroundDerivation {
        artifact_schema: CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
        artifact_role: CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
        artifact_sha256,
        artifact_bytes: checked_u64(bytes.len(), "artifact byte length")?,
        normalized_input_sha256: envelope.normalized_input_sha256,
        source_clause_sequence_sha256: envelope.source_clause_sequence_sha256,
        step_count: derivation.steps.len(),
        query_step: derivation.query_step,
        premise_edge_count: counts.premise_edges,
        binding_count: counts.bindings,
        uf_observation_count: counts.uf_observations,
        value_node_count: counts.value_nodes,
        derivation,
    })
}

#[cfg(test)]
mod metered_identity_tests;

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::ground_derivation::CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH;
    use crate::{
        ChcDtConstructor, ChcDtSelector, ChcExpr, ChcVar, ClauseBody, ClauseHead, HornClause,
    };

    fn int_var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    fn int_env(bindings: &[(&str, i128)]) -> FxHashMap<String, SmtValue> {
        bindings
            .iter()
            .map(|(name, value)| ((*name).to_string(), SmtValue::Int(*value)))
            .collect()
    }

    pub(super) fn fixture() -> (ChcProblem, GroundDerivation) {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(int_var("x"), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![int_var("x")]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![int_var("x")])],
                Some(ChcExpr::eq(
                    int_var("y"),
                    ChcExpr::add(int_var("x"), ChcExpr::int(1)),
                )),
            ),
            ClauseHead::Predicate(q, vec![int_var("y")]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![int_var("z")])],
                Some(ChcExpr::eq(int_var("z"), ChcExpr::int(1))),
            ),
            ClauseHead::False,
        ));
        let derivation = GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: int_env(&[("x", 0)]),
                    premises: vec![],
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: int_env(&[("x", 0), ("y", 1)]),
                    premises: vec![0],
                },
                GroundDerivationStep {
                    clause_index: 2,
                    env: int_env(&[("z", 1)]),
                    premises: vec![1],
                },
            ],
            query_step: 2,
        };
        (problem, derivation)
    }

    fn artifact_bytes(problem: &ChcProblem, derivation: &GroundDerivation) -> Vec<u8> {
        encode_ground_derivation_artifact(problem, derivation)
            .expect("fixture derivation should encode")
            .into_bytes()
    }

    #[test]
    fn frozen_v1_literal_remains_byte_and_reader_compatible() {
        const GOLDEN_BYTES: &[u8] = br#"{"schema":"ay.chc-ground-derivation-artifact/v1","schema_version":1,"role":"unsafe-ground-derivation","normalized_input_schema":"ay.chc.normalized-input/v1","normalized_input_sha256":"23bbc1e41eb6a113b212c79466863072b8e1e2986ef3cb95b9cf31d4ecfa830c","source_clause_sequence_sha256":"11659dc4a46960942dc609b403a74433e3c1039e1e890e33d23b21cf3099c0b1","step_count":1,"query_step":0,"premise_edge_count":0,"binding_count":0,"value_node_count":0,"steps":[{"clause_index":0,"premises":[],"bindings":[]}]}"#;
        const GOLDEN_SHA256: &str =
            "86322ccf122e4d90c978de17294302f04bb4644cbe3de1eda337e5dbe8efe651";

        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
            true,
        ))));
        let derivation = GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: Vec::new(),
            }],
            query_step: 0,
        };

        let validated = validate_chc_ground_derivation_artifact(&problem, GOLDEN_BYTES)
            .expect("frozen v1 literal must remain readable");
        assert_eq!(validated.artifact_sha256(), GOLDEN_SHA256);
        assert_eq!(validated.artifact_bytes(), GOLDEN_BYTES.len() as u64);
        assert_eq!(artifact_bytes(&problem, &derivation), GOLDEN_BYTES);
        assert_eq!(sha256_hex(GOLDEN_BYTES), GOLDEN_SHA256);
    }

    #[test]
    fn public_artifacts_reject_unselected_cross_clause_uf_overload() {
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
            true,
        ))));
        let reachable = problem.declare_predicate("Reachable", Vec::new());
        for argument in [ChcExpr::Int(0), ChcExpr::Bool(false)] {
            let application = ChcExpr::FuncApp(
                "conflicting".to_string(),
                ChcSort::Int,
                vec![Arc::new(argument)],
            );
            problem.add_clause(HornClause::new(
                ClauseBody::constraint(ChcExpr::eq(application, ChcExpr::Int(0))),
                ClauseHead::Predicate(reachable, Vec::new()),
            ));
        }
        let derivation = GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: Vec::new(),
            }],
            query_step: 0,
        };

        assert_eq!(
            encode_ground_derivation_artifact(&problem, &derivation)
                .expect_err("cross-clause UF overload must fail before v1 encoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            encode_ground_derivation_artifact_v2(&problem, &derivation)
                .expect_err("cross-clause UF overload must fail before encoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            validate_chc_ground_derivation_artifact(&problem, b"{}")
                .expect_err("cross-clause UF overload must fail before v1 decoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(&problem, b"{}")
                .expect_err("cross-clause UF overload must fail before decoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
    }

    fn two_step_ground_link() -> GroundDerivation {
        GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: FxHashMap::default(),
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: FxHashMap::default(),
                    premises: vec![0],
                },
            ],
            query_step: 1,
        }
    }

    fn one_step_ground_query() -> GroundDerivation {
        GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: Vec::new(),
            }],
            query_step: 0,
        }
    }

    fn assert_v1_v2_source_boundaries_reject(problem: &ChcProblem, derivation: &GroundDerivation) {
        assert_eq!(
            encode_ground_derivation_artifact(problem, derivation)
                .expect_err("invalid source must fail before v1 encoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            encode_ground_derivation_artifact_v2(problem, derivation)
                .expect_err("invalid source must fail before v2 encoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            validate_chc_ground_derivation_artifact(problem, b"{}")
                .expect_err("invalid source must fail before v1 decoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(problem, b"{}")
                .expect_err("invalid source must fail before v2 decoding")
                .reason,
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem
        );
    }

    #[test]
    fn v1_v2_boundaries_reject_bool_int_predicate_coercion() {
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(predicate, vec![ChcExpr::Bool(true)]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            predicate,
            vec![ChcExpr::Int(1)],
        )])));

        assert_v1_v2_source_boundaries_reject(&problem, &two_step_ground_link());
    }

    #[test]
    fn v1_v2_boundaries_reject_undefined_predicate_ids() {
        let mut problem = ChcProblem::new();
        let undefined = crate::PredicateId::new(17);
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(undefined, Vec::new()),
        ));
        problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            undefined,
            Vec::new(),
        )])));

        assert_v1_v2_source_boundaries_reject(&problem, &two_step_ground_link());
    }

    #[test]
    fn v1_v2_boundaries_reject_mixed_bool_int_constraint_equality() {
        let mixed_equality = ChcExpr::Op(
            crate::ChcOp::Eq,
            vec![
                Arc::new(ChcExpr::Var(ChcVar::new("b", ChcSort::Bool))),
                Arc::new(ChcExpr::Var(ChcVar::new("i", ChcSort::Int))),
            ],
        );
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(mixed_equality)));

        assert_v1_v2_source_boundaries_reject(&problem, &one_step_ground_query());
    }

    #[test]
    fn v1_v2_boundaries_reject_ite_operator_arity_and_constraint_sort_misuse() {
        let condition = ChcExpr::Var(ChcVar::new("condition", ChcSort::Bool));
        let malformed_ite = ChcExpr::Op(
            crate::ChcOp::Ite,
            vec![
                Arc::new(condition),
                Arc::new(ChcExpr::Int(0)),
                Arc::new(ChcExpr::Bool(false)),
            ],
        );
        let ite_constraint = ChcExpr::Op(
            crate::ChcOp::Eq,
            vec![Arc::new(malformed_ite), Arc::new(ChcExpr::Int(0))],
        );
        let wrong_arity = ChcExpr::Op(
            crate::ChcOp::Not,
            vec![
                Arc::new(ChcExpr::Var(ChcVar::new("a", ChcSort::Bool))),
                Arc::new(ChcExpr::Var(ChcVar::new("b", ChcSort::Bool))),
            ],
        );

        for constraint in [ite_constraint, wrong_arity, ChcExpr::Int(1)] {
            let mut problem = ChcProblem::new();
            problem.add_clause(HornClause::query(ClauseBody::constraint(constraint)));
            assert_v1_v2_source_boundaries_reject(&problem, &one_step_ground_query());
        }
    }

    #[test]
    fn v1_v2_boundaries_reject_undefined_action_id() {
        let mut problem = ChcProblem::new();
        problem.add_clause_with_action(
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(true))),
            crate::ActionId::new(7),
        );

        assert_v1_v2_source_boundaries_reject(&problem, &one_step_ground_query());
    }

    #[test]
    fn unselected_max_width_bv_source_does_not_pay_evaluator_allocation() {
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
            true,
        ))));
        let unused = problem.declare_predicate("UnusedWide", Vec::new());
        let wide_zero = ChcExpr::Op(
            crate::ChcOp::Int2Bv(crate::MAX_BITVECTOR_WIDTH),
            vec![Arc::new(ChcExpr::Int(0))],
        );
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(wide_zero.clone(), wide_zero)),
            ClauseHead::Predicate(unused, Vec::new()),
        ));
        let derivation = GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: Vec::new(),
            }],
            query_step: 0,
        };

        encode_ground_derivation_artifact_v2(&problem, &derivation)
            .expect("unselected wide values are hashed, not evaluated");
    }

    fn int_uf(name: &str, argument: ChcExpr) -> ChcExpr {
        ChcExpr::FuncApp(name.to_string(), ChcSort::Int, vec![Arc::new(argument)])
    }

    fn nullary_int_uf(name: &str) -> ChcExpr {
        ChcExpr::FuncApp(name.to_string(), ChcSort::Int, Vec::new())
    }

    fn install_observations(
        env: &mut FxHashMap<String, SmtValue>,
        observations: &[(ChcExpr, SmtValue)],
    ) {
        assert!(
            crate::smt::executor_adapter::install_observed_uf_application_values(env, observations,),
            "fixture UF observations should install"
        );
    }

    fn observed_env(
        binding: (&str, i128),
        observations: &[(ChcExpr, SmtValue)],
    ) -> FxHashMap<String, SmtValue> {
        let mut env = int_env(&[binding]);
        install_observations(&mut env, observations);
        env
    }

    pub(super) fn uf_fixture() -> (ChcProblem, GroundDerivation) {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let fx = int_uf("f", int_var("x"));
        let fy = int_uf("f", int_var("y"));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(int_var("x"), ChcExpr::int(0)),
                ChcExpr::eq(fx.clone(), ChcExpr::int(7)),
            )),
            ClauseHead::Predicate(p, vec![int_var("x")]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![int_var("y")])],
            Some(ChcExpr::and(
                ChcExpr::eq(int_var("y"), ChcExpr::int(0)),
                ChcExpr::eq(fy.clone(), ChcExpr::int(7)),
            )),
        )));
        let derivation = GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: observed_env(("x", 0), &[(fx, SmtValue::Int(7))]),
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: observed_env(("y", 0), &[(fy, SmtValue::Int(7))]),
                    premises: vec![0],
                },
            ],
            query_step: 1,
        };
        (problem, derivation)
    }

    #[test]
    fn multi_predicate_derivation_round_trips_to_opaque_validated_evidence() {
        let (problem, derivation) = fixture();
        let counterexample = Counterexample::new(Vec::new()).with_ground_derivation(derivation);
        let artifact = counterexample
            .ground_derivation_artifact(&problem)
            .expect("valid carried derivation should serialize");
        assert_eq!(artifact.schema(), CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA);
        assert_eq!(artifact.role(), CHC_GROUND_DERIVATION_ARTIFACT_ROLE);

        let validated = validate_chc_ground_derivation_artifact(&problem, artifact.bytes())
            .expect("canonical artifact should validate");
        assert_eq!(validated.step_count(), 3);
        assert_eq!(validated.query_step(), 2);
        assert_eq!(validated.premise_edge_count(), 2);
        assert_eq!(validated.binding_count(), 4);
        assert_eq!(validated.value_node_count(), 4);
        assert_eq!(
            validated.artifact_role(),
            CHC_GROUND_DERIVATION_ARTIFACT_ROLE
        );
        assert_eq!(validated.artifact_bytes(), artifact.bytes().len() as u64);
        assert_eq!(validated.artifact_sha256(), artifact.sha256());
        assert!(validated.derivation.steps.iter().all(|step| step
            .env
            .keys()
            .all(|name| !name.starts_with("\0ay.uf-concrete-application-value:"))));
        assert_eq!(
            validate_ground_derivation(&problem, validated.derivation()),
            Ok(())
        );
    }

    #[test]
    fn positional_clause_hash_rejects_reordered_source_with_same_normalized_hash() {
        let (problem, derivation) = fixture();
        let bytes = artifact_bytes(&problem, &derivation);
        let mut reordered = problem.clone();
        reordered.clauses_mut().swap(0, 1);
        assert_eq!(
            normalized_chc_input_sha256(&problem),
            normalized_chc_input_sha256(&reordered),
            "normalized identity deliberately treats clause order as semantic noise"
        );
        let rejection = validate_chc_ground_derivation_artifact(&reordered, &bytes)
            .expect_err("positional evidence must reject reordered clauses");
        assert_eq!(
            rejection.reason,
            ChcGroundDerivationArtifactErrorReason::ClauseSequenceHashMismatch
        );
    }

    #[test]
    fn positional_clause_hash_binds_body_premise_order() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(q, vec![ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![
            (p, vec![int_var("x")]),
            (q, vec![int_var("x")]),
        ])));
        let mut reordered = problem.clone();
        reordered.clauses_mut()[2].body.predicates.swap(0, 1);

        assert_eq!(
            normalized_chc_input_sha256(&problem),
            normalized_chc_input_sha256(&reordered),
            "normalized identity deliberately sorts conjunction members"
        );
        assert_ne!(
            ordered_chc_clause_sequence_sha256(&problem),
            ordered_chc_clause_sequence_sha256(&reordered),
            "premise positions must remain source-authenticated"
        );
    }

    #[test]
    fn canonical_boundary_rejects_whitespace_unknown_fields_and_trailing_bytes() {
        let (problem, derivation) = fixture();
        let bytes = artifact_bytes(&problem, &derivation);

        let mut wrong_input_schema: GroundDerivationEnvelope =
            serde_json::from_slice(&bytes).expect("fixture envelope");
        wrong_input_schema.normalized_input_schema = "ay.chc-normalized-input/v0".to_string();
        assert_eq!(
            validate_chc_ground_derivation_artifact(
                &problem,
                &serde_json::to_vec(&wrong_input_schema).expect("mutated input schema serializes"),
            )
            .expect_err("wrong normalized-input schema must fail")
            .reason,
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch
        );

        let mut whitespace = bytes.clone();
        whitespace.insert(1, b' ');
        assert_eq!(
            validate_chc_ground_derivation_artifact(&problem, &whitespace)
                .expect_err("non-canonical whitespace must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::NonCanonicalEnvelope
        );

        let mut object: serde_json::Value = serde_json::from_slice(&bytes).expect("fixture JSON");
        object["unknown"] = serde_json::Value::Bool(true);
        let unknown = serde_json::to_vec(&object).expect("mutated JSON serializes");
        assert_eq!(
            validate_chc_ground_derivation_artifact(&problem, &unknown)
                .expect_err("unknown fields must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::MalformedEnvelope
        );

        let mut trailing = bytes;
        trailing.extend_from_slice(b"\n");
        assert_eq!(
            validate_chc_ground_derivation_artifact(&problem, &trailing)
                .expect_err("trailing material must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::NonCanonicalEnvelope
        );
    }

    #[test]
    fn binding_and_derivation_mutations_fail_closed() {
        let (problem, derivation) = fixture();
        let bytes = artifact_bytes(&problem, &derivation);
        let envelope: GroundDerivationEnvelope =
            serde_json::from_slice(&bytes).expect("fixture envelope");

        let mut missing = envelope.clone();
        missing.steps[1].bindings.pop();
        missing.binding_count -= 1;
        missing.value_node_count -= 1;
        let rejection = validate_chc_ground_derivation_artifact(
            &problem,
            &serde_json::to_vec(&missing).expect("mutated envelope serializes"),
        )
        .expect_err("missing binding must fail");
        assert_eq!(
            rejection.reason,
            ChcGroundDerivationArtifactErrorReason::BindingSetMismatch
        );

        let mut unsorted = envelope.clone();
        unsorted.steps[1].bindings.swap(0, 1);
        let rejection = validate_chc_ground_derivation_artifact(
            &problem,
            &serde_json::to_vec(&unsorted).expect("mutated envelope serializes"),
        )
        .expect_err("unsorted binding must fail");
        assert_eq!(
            rejection.reason,
            ChcGroundDerivationArtifactErrorReason::BindingSetMismatch
        );

        let mut wrong_premise = envelope.clone();
        wrong_premise.steps[2].premises[0] = 0;
        let rejection = validate_chc_ground_derivation_artifact(
            &problem,
            &serde_json::to_vec(&wrong_premise).expect("mutated envelope serializes"),
        )
        .expect_err("wrong premise must fail");
        assert_eq!(
            rejection.reason,
            ChcGroundDerivationArtifactErrorReason::DerivationRejected
        );

        let mut wrong_value = envelope;
        wrong_value.steps[2].bindings[0].value = WireValue::Int {
            decimal: "2".to_string(),
        };
        let rejection = validate_chc_ground_derivation_artifact(
            &problem,
            &serde_json::to_vec(&wrong_value).expect("mutated envelope serializes"),
        )
        .expect_err("wrong concrete value must fail");
        assert_eq!(
            rejection.reason,
            ChcGroundDerivationArtifactErrorReason::DerivationRejected
        );
    }

    #[test]
    fn value_codec_round_trips_all_supported_recursive_forms() {
        let datatype_sort = ChcSort::Datatype {
            name: "Pair".to_string(),
            constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
                name: "mk-pair".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "first".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "second".to_string(),
                        sort: ChcSort::Bool,
                    },
                ],
            }]),
        };
        let cases = vec![
            (
                ChcSort::Int,
                SmtValue::int_from_bigint(BigInt::from(i128::MAX) + 1),
            ),
            (
                ChcSort::Real,
                SmtValue::Real(BigRational::new(BigInt::from(-7), BigInt::from(11))),
            ),
            (
                ChcSort::BitVec(129),
                SmtValue::bitvec_from_biguint(
                    (BigUint::from(1u8) << 128) + BigUint::from(3u8),
                    129,
                ),
            ),
            (
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
                SmtValue::ArrayMap {
                    default: Box::new(SmtValue::Bool(false)),
                    entries: vec![(SmtValue::Int(4), SmtValue::Bool(true))],
                },
            ),
            (
                datatype_sort,
                SmtValue::Datatype(
                    "mk-pair".to_string(),
                    vec![SmtValue::Int(9), SmtValue::Bool(true)],
                ),
            ),
        ];

        for (sort, value) in cases {
            let mut encoded_nodes = 0;
            let wire = encode_value(&value, &sort, 1, &mut encoded_nodes)
                .expect("supported value should encode");
            let mut decoded_nodes = 0;
            let decoded = decode_value(&wire, &sort, 1, &mut decoded_nodes)
                .expect("supported value should decode");
            assert_eq!(decoded, value);
            assert_eq!(decoded_nodes, encoded_nodes);
        }
    }

    #[test]
    fn nested_array_indices_are_rejected_until_key_equality_is_canonical() {
        let nested_index = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let sort = ChcSort::Array(Box::new(nested_index), Box::new(ChcSort::Int));
        let value = SmtValue::ConstArray(Box::new(SmtValue::Int(0)));
        let mut nodes = 0;
        assert_eq!(
            encode_value(&value, &sort, 1, &mut nodes)
                .expect_err("non-canonical array-key equality must fail closed")
                .reason,
            ChcGroundDerivationArtifactErrorReason::BindingSortMismatch
        );
    }

    #[test]
    fn opaque_and_private_uf_environment_values_never_serialize() {
        let (problem, mut derivation) = fixture();
        derivation.steps[0]
            .env
            .insert("x".to_string(), SmtValue::Opaque("@x".to_string()));
        assert_eq!(
            encode_ground_derivation_artifact(&problem, &derivation)
                .expect_err("opaque values must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::OpaqueValue
        );

        let (_, mut derivation) = fixture();
        derivation.steps[0].env.insert(
            "\0ay.uf-application-model\0".to_string(),
            SmtValue::Opaque("exact-v1".to_string()),
        );
        assert_eq!(
            encode_ground_derivation_artifact(&problem, &derivation)
                .expect_err("private UF observations must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
        );
    }

    #[test]
    fn v2_round_trips_source_authenticated_uf_observations_while_v1_rejects_them() {
        let (problem, derivation) = uf_fixture();
        assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
        assert_eq!(
            encode_ground_derivation_artifact(&problem, &derivation)
                .expect_err("artifact v1 must keep rejecting private UF metadata")
                .reason,
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
        );

        let artifact = encode_ground_derivation_artifact_v2(&problem, &derivation)
            .expect("artifact v2 should encode finite ordinary-UF observations");
        assert_eq!(artifact.schema(), CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA);
        assert_eq!(artifact.role(), CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE);
        assert!(
            !String::from_utf8_lossy(artifact.bytes()).contains("\\u0000ay.uf-"),
            "private evaluator keys must never cross the portable boundary"
        );

        let validated = validate_chc_ground_derivation_artifact_v2(&problem, artifact.bytes())
            .expect("canonical artifact v2 should validate");
        assert_eq!(
            validated.artifact_schema(),
            CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA
        );
        assert_eq!(validated.step_count(), 2);
        assert_eq!(validated.uf_observation_count(), 2);
        assert_eq!(
            validated.artifact_role(),
            CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE
        );
        assert_eq!(validated.artifact_bytes(), artifact.bytes().len() as u64);
        assert_eq!(validated.artifact_sha256(), artifact.sha256());
        assert_eq!(
            validate_ground_derivation(&problem, validated.derivation()),
            Ok(())
        );

        assert!(
            validate_chc_ground_derivation_artifact(&problem, artifact.bytes()).is_err(),
            "artifact v1 parser must fail closed on v2 bytes"
        );
        let (v1_problem, v1_derivation) = fixture();
        let v1_bytes = artifact_bytes(&v1_problem, &v1_derivation);
        assert!(
            validate_chc_ground_derivation_artifact_v2(&v1_problem, &v1_bytes).is_err(),
            "artifact v2 parser must fail closed on v1 bytes"
        );
    }

    #[test]
    fn v2_producer_rejects_noncanonical_bindings_before_uf_encoding() {
        let (problem, mut derivation) = uf_fixture();
        derivation.steps[0]
            .env
            .insert("x".to_string(), SmtValue::BigInt(Arc::new(BigInt::from(0))));

        assert_eq!(
            encode_ground_derivation_artifact_v2(&problem, &derivation)
                .expect_err("v2 producer must authenticate bindings before evaluating UFs")
                .reason,
            ChcGroundDerivationArtifactErrorReason::DerivationRejected
        );
    }

    #[test]
    fn v2_rejects_missing_reordered_and_incongruent_uf_observations() {
        let (problem, derivation) = uf_fixture();
        let artifact = encode_ground_derivation_artifact_v2(&problem, &derivation)
            .expect("fixture v2 artifact should encode");
        let envelope: GroundDerivationEnvelopeV2 =
            serde_json::from_slice(artifact.bytes()).expect("fixture v2 envelope");

        let mut missing = envelope.clone();
        missing.steps[0].uf_observations.clear();
        missing.uf_observation_count -= 1;
        missing.value_node_count -= 1;
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&missing).expect("missing observation mutation serializes"),
            )
            .expect_err("missing source observation must fail")
            .reason,
            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch
        );

        let mut wrong_ordinal = envelope.clone();
        wrong_ordinal.steps[0].uf_observations[0].application_ordinal = 1;
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&wrong_ordinal).expect("ordinal mutation should serialize"),
            )
            .expect_err("non-canonical source ordinal must fail")
            .reason,
            ChcGroundDerivationArtifactErrorReason::UfObservationSetMismatch
        );

        let mut incongruent = envelope;
        incongruent.steps[1].uf_observations[0].result = WireValue::Int {
            decimal: "8".to_string(),
        };
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&incongruent)
                    .expect("incongruent observation mutation serializes"),
            )
            .expect_err("one function cannot change value at the same arguments")
            .reason,
            ChcGroundDerivationArtifactErrorReason::UfCongruenceViolation
        );

        let mut wrong_count: GroundDerivationEnvelopeV2 =
            serde_json::from_slice(artifact.bytes()).expect("fixture v2 envelope");
        wrong_count.uf_observation_count += 1;
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&wrong_count).expect("count mutation serializes"),
            )
            .expect_err("false UF count must fail")
            .reason,
            ChcGroundDerivationArtifactErrorReason::CountMismatch
        );

        let mut wrong_role: GroundDerivationEnvelopeV2 =
            serde_json::from_slice(artifact.bytes()).expect("fixture v2 envelope");
        wrong_role.role = CHC_GROUND_DERIVATION_ARTIFACT_ROLE.to_string();
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&wrong_role).expect("role mutation serializes"),
            )
            .expect_err("v1 role must not label v2 bytes")
            .reason,
            ChcGroundDerivationArtifactErrorReason::RoleMismatch
        );

        let mut wrong_schema: GroundDerivationEnvelopeV2 =
            serde_json::from_slice(artifact.bytes()).expect("fixture v2 envelope");
        wrong_schema.schema = CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA.to_string();
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(
                &problem,
                &serde_json::to_vec(&wrong_schema).expect("schema mutation serializes"),
            )
            .expect_err("v1 schema must not label v2 bytes")
            .reason,
            ChcGroundDerivationArtifactErrorReason::SchemaMismatch
        );
    }

    #[test]
    fn v2_authenticates_nested_uf_observations_independently_of_wire_order() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let gx = int_uf("g", int_var("x"));
        let fgx = int_uf("f", gx.clone());
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::eq(gx.clone(), ChcExpr::int(3)),
                ChcExpr::eq(fgx.clone(), ChcExpr::int(7)),
            )),
            ClauseHead::Predicate(p, vec![int_var("x")]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            p,
            vec![int_var("y")],
        )])));
        let derivation = GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: observed_env(("x", 0), &[(fgx, SmtValue::Int(7)), (gx, SmtValue::Int(3))]),
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: int_env(&[("y", 0)]),
                    premises: vec![0],
                },
            ],
            query_step: 1,
        };

        let artifact = encode_ground_derivation_artifact_v2(&problem, &derivation)
            .expect("nested UF observations should encode canonically");
        let validated = validate_chc_ground_derivation_artifact_v2(&problem, artifact.bytes())
            .expect("nested UF observations should round-trip");
        assert_eq!(validated.uf_observation_count(), 2);
    }

    #[test]
    fn v2_authenticates_nullary_and_body_argument_only_ufs() {
        let mut nullary_problem = ChcProblem::new();
        let p = nullary_problem.declare_predicate("P", vec![ChcSort::Int]);
        let k = nullary_int_uf("k");
        nullary_problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(p, vec![k.clone()]),
        ));
        nullary_problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            p,
            vec![int_var("y")],
        )])));
        let mut fact_env = FxHashMap::default();
        install_observations(&mut fact_env, &[(k, SmtValue::Int(9))]);
        let nullary_derivation = GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: fact_env,
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: int_env(&[("y", 9)]),
                    premises: vec![0],
                },
            ],
            query_step: 1,
        };
        let nullary = encode_ground_derivation_artifact_v2(&nullary_problem, &nullary_derivation)
            .expect("nullary UF observation should encode");
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(&nullary_problem, nullary.bytes())
                .expect("nullary UF observation should validate")
                .uf_observation_count(),
            1
        );

        let mut body_problem = ChcProblem::new();
        let p = body_problem.declare_predicate("P", vec![ChcSort::Int]);
        let f_zero = int_uf("f", ChcExpr::int(0));
        body_problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(p, vec![ChcExpr::int(4)]),
        ));
        body_problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            p,
            vec![f_zero.clone()],
        )])));
        let mut query_env = FxHashMap::default();
        install_observations(&mut query_env, &[(f_zero, SmtValue::Int(4))]);
        let body_derivation = GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: 0,
                    env: FxHashMap::default(),
                    premises: Vec::new(),
                },
                GroundDerivationStep {
                    clause_index: 1,
                    env: query_env,
                    premises: vec![0],
                },
            ],
            query_step: 1,
        };
        let body = encode_ground_derivation_artifact_v2(&body_problem, &body_derivation)
            .expect("body-argument-only UF observation should encode");
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(&body_problem, body.bytes())
                .expect("body-argument-only UF observation should validate")
                .uf_observation_count(),
            1
        );
    }

    #[test]
    fn v2_rejects_private_source_names_and_ignores_unused_private_poison() {
        let private = ChcVar::new("\0ay.source-collision", ChcSort::Int);
        let mut private_problem = ChcProblem::new();
        private_problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(private.clone()),
            ChcExpr::int(0),
        ))));
        let private_derivation = GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index: 0,
                env: [(private.name, SmtValue::Int(0))].into_iter().collect(),
                premises: Vec::new(),
            }],
            query_step: 0,
        };
        assert_eq!(
            encode_ground_derivation_artifact_v2(&private_problem, &private_derivation)
                .expect_err("source names may not enter AY's private namespace")
                .reason,
            ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
        );

        let (problem, clean_derivation) = uf_fixture();
        let clean = encode_ground_derivation_artifact_v2(&problem, &clean_derivation)
            .expect("clean UF fixture should encode");
        let mut poisoned_derivation = clean_derivation;
        poisoned_derivation.steps[0].env.insert(
            "\0ay.uf-application-value:unused-poison".to_string(),
            SmtValue::Opaque("hostile-unused-value".to_string()),
        );
        let poisoned = encode_ground_derivation_artifact_v2(&problem, &poisoned_derivation)
            .expect("unused private metadata must not influence source-authenticated evidence");
        assert_eq!(
            poisoned.bytes(),
            clean.bytes(),
            "unused private metadata must be omitted from canonical bytes"
        );

        let (poisoned_problem, mut poisoned_marker) = uf_fixture();
        poisoned_marker.steps[0].env.insert(
            crate::expr::evaluate::UF_APPLICATION_MODEL_MARKER_KEY.to_string(),
            SmtValue::Opaque("poisoned-marker".to_string()),
        );
        assert_eq!(
            encode_ground_derivation_artifact_v2(&poisoned_problem, &poisoned_marker)
                .expect_err("a poisoned marker must disable private observation lookup")
                .reason,
            ChcGroundDerivationArtifactErrorReason::UfObservationNotGround
        );

        let (unknown_problem, mut unknown_private) = uf_fixture();
        unknown_private.steps[0].env.insert(
            "\0ay.unrecognized-private-key".to_string(),
            SmtValue::Int(0),
        );
        assert_eq!(
            encode_ground_derivation_artifact_v2(&unknown_problem, &unknown_private)
                .expect_err("unrecognized private metadata must fail closed")
                .reason,
            ChcGroundDerivationArtifactErrorReason::BindingSetMismatch
        );
    }

    #[test]
    fn declared_counts_and_resource_surface_are_checked_before_authority() {
        let (problem, derivation) = fixture();
        let bytes = artifact_bytes(&problem, &derivation);
        let mut envelope: GroundDerivationEnvelope =
            serde_json::from_slice(&bytes).expect("fixture envelope");
        envelope.value_node_count += 1;
        assert_eq!(
            validate_chc_ground_derivation_artifact(
                &problem,
                &serde_json::to_vec(&envelope).expect("mutated envelope serializes"),
            )
            .expect_err("false count must fail")
            .reason,
            ChcGroundDerivationArtifactErrorReason::CountMismatch
        );

        let nested = vec![b'['; CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH + 1];
        assert_eq!(
            validate_json_surface(&nested)
                .expect_err("over-deep JSON must fail")
                .reason,
            ChcGroundDerivationArtifactErrorReason::NestingTooDeep
        );

        let source_work =
            map_source_surface_error(0, 0, GroundSourceSurfaceError::SourceWorkLimitExceeded);
        assert_eq!(
            source_work.reason,
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
        );
        assert_eq!(source_work.reason_code, "source_work_limit_exceeded");
    }

    #[test]
    fn unselected_deep_source_is_rejected_before_whole_problem_hashing() {
        let (mut problem, derivation) = fixture();
        let unused = problem.declare_predicate("Unused", Vec::new());
        let deep_clause_index = problem.clauses().len();
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(unused, Vec::new()),
        ));
        assert_eq!(problem.clauses().len(), deep_clause_index + 1);

        let mut deep = ChcExpr::Bool(true);
        for _ in 0..=CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            deep = ChcExpr::Op(crate::ChcOp::Not, vec![Arc::new(deep)]);
        }
        // Install the hostile raw AST only after `add_clause` has run. Its
        // normal constant simplifier deliberately collapses double negations,
        // which would otherwise erase the depth this boundary must reject.
        problem.clauses_mut()[deep_clause_index].body.constraint = Some(deep);

        assert_eq!(
            encode_ground_derivation_artifact_v2(&problem, &derivation)
                .expect_err("unselected deep source must fail before hashing")
                .reason,
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
        );
        assert_eq!(
            validate_chc_ground_derivation_artifact_v2(&problem, b"{}")
                .expect_err("public decode must preflight source before hashing")
                .reason,
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
        );
    }
}
