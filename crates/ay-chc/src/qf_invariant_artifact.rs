// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Bounded, canonical serialization for replayable quantifier-free CHC invariants.
//!
//! The older `ChcProofRunArtifacts::model` payload is consumer-status metadata;
//! it does not contain predicate interpretations. This module is the distinct
//! producer/consumer boundary for the actual model used by Trust's S3 replay
//! gate. Parsing is deliberately stricter than [`InvariantModel::parse_smtlib`]:
//! only byte-canonical AY output is admitted, so ignored commands, unknown or
//! duplicate predicates, missing definitions, type drift, and trailing material
//! all fail closed before replay.

use std::collections::HashSet;
use std::panic::{catch_unwind, AssertUnwindSafe};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    normalized_chc_input_sha256, ChcPdrProofRun, ChcProblem, ChcProofRunArtifact, ChcSort,
    InvariantModel, VerifiedChcResult,
};

/// Schema for the actual, replayable QF invariant-model artifact.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA: &str = "ay.chc-qf-invariant-model-artifact/v1";
/// Role for the actual, replayable QF invariant-model artifact.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE: &str = "quantifier-free-inductive-invariant";
/// Canonical representation used inside the versioned envelope.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT: &str = "ay.smtlib2-define-fun-model/v1";

/// Maximum total serialized artifact size (16 MiB).
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES: usize = 16 * 1024 * 1024;
/// Maximum size of the embedded canonical SMT-LIB model (8 MiB).
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_MODEL_BYTES: usize = 8 * 1024 * 1024;
/// Maximum number of predicate interpretations in one artifact.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES: usize = 4_096;
/// Maximum total number of predicate parameters in one artifact.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PARAMETERS: usize = 65_536;
/// Maximum parenthesis nesting accepted before invoking AY's recursive parser.
pub const CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH: usize = 256;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct QfInvariantModelEnvelope {
    schema: String,
    schema_version: u64,
    role: String,
    model_format: String,
    normalized_input_sha256: String,
    predicate_count: u64,
    model_sha256: String,
    model_smtlib: String,
}

/// Stable reason a QF invariant artifact could not be produced or parsed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcQfInvariantModelArtifactErrorReason {
    /// The proof run is not a Safe result carrying a verified invariant.
    ResultNotSafe,
    /// Quantified ghost-pair certificates are a distinct evidence class.
    GhostPairCertificate,
    /// Empty models belong to the acyclic-exhaustive BMC evidence class.
    EmptyModel,
    /// The complete artifact exceeds the public hard bound.
    ArtifactTooLarge,
    /// The embedded model text exceeds the public hard bound.
    ModelTooLarge,
    /// The model/problem exceeds the predicate-count bound.
    TooManyPredicates,
    /// The model/problem exceeds the total-parameter bound.
    TooManyParameters,
    /// The model exceeds the parser nesting-depth bound.
    NestingTooDeep,
    /// The artifact JSON is malformed, duplicated, or has unknown fields.
    MalformedEnvelope,
    /// The JSON envelope is valid but not in AY's byte-canonical encoding.
    NonCanonicalEnvelope,
    /// The schema or schema version is unsupported.
    SchemaMismatch,
    /// The artifact role is not the QF invariant role.
    RoleMismatch,
    /// The embedded model format is unsupported.
    ModelFormatMismatch,
    /// The artifact is bound to a different normalized CHC problem.
    ProblemHashMismatch,
    /// The embedded model digest is incorrect.
    ModelHashMismatch,
    /// The declared predicate count disagrees with the parsed model.
    PredicateCountMismatch,
    /// A problem predicate has no interpretation.
    MissingPredicate,
    /// A predicate interpretation has the wrong arity.
    PredicateArityMismatch,
    /// A predicate parameter has the wrong sort.
    PredicateSortMismatch,
    /// A predicate interpretation does not have Boolean result sort.
    PredicateReturnSortMismatch,
    /// A model body is not closed, declared, recursively well-sorted QF syntax.
    InvalidModelExpression,
    /// A predicate interpretation repeats a bound parameter name.
    DuplicateParameter,
    /// AY's model parser rejected the embedded SMT-LIB.
    ModelParseFailed,
    /// AY's model parser panicked; the panic was contained and rejected.
    ModelParserPanicked,
    /// The parsed model does not round-trip byte-for-byte to AY's canonical output.
    NonCanonicalModel,
    /// Serialization failed while producing a solver-owned artifact.
    SerializationFailed,
}

impl ChcQfInvariantModelArtifactErrorReason {
    /// Stable lower-snake-case reason code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::ResultNotSafe => "result_not_safe",
            Self::GhostPairCertificate => "ghost_pair_certificate",
            Self::EmptyModel => "empty_model",
            Self::ArtifactTooLarge => "artifact_too_large",
            Self::ModelTooLarge => "model_too_large",
            Self::TooManyPredicates => "too_many_predicates",
            Self::TooManyParameters => "too_many_parameters",
            Self::NestingTooDeep => "nesting_too_deep",
            Self::MalformedEnvelope => "malformed_envelope",
            Self::NonCanonicalEnvelope => "non_canonical_envelope",
            Self::SchemaMismatch => "schema_mismatch",
            Self::RoleMismatch => "role_mismatch",
            Self::ModelFormatMismatch => "model_format_mismatch",
            Self::ProblemHashMismatch => "problem_hash_mismatch",
            Self::ModelHashMismatch => "model_hash_mismatch",
            Self::PredicateCountMismatch => "predicate_count_mismatch",
            Self::MissingPredicate => "missing_predicate",
            Self::PredicateArityMismatch => "predicate_arity_mismatch",
            Self::PredicateSortMismatch => "predicate_sort_mismatch",
            Self::PredicateReturnSortMismatch => "predicate_return_sort_mismatch",
            Self::InvalidModelExpression => "invalid_model_expression",
            Self::DuplicateParameter => "duplicate_parameter",
            Self::ModelParseFailed => "model_parse_failed",
            Self::ModelParserPanicked => "model_parser_panicked",
            Self::NonCanonicalModel => "non_canonical_model",
            Self::SerializationFailed => "serialization_failed",
        }
    }
}

/// Typed fail-closed QF invariant artifact error.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{reason_code}: {detail}")]
pub struct ChcQfInvariantModelArtifactError {
    /// Stable error classification.
    pub reason: ChcQfInvariantModelArtifactErrorReason,
    /// Stable lower-snake-case reason code.
    pub reason_code: &'static str,
    /// Human-readable diagnostic detail; it never carries positive authority.
    pub detail: String,
}

impl ChcQfInvariantModelArtifactError {
    fn new(reason: ChcQfInvariantModelArtifactErrorReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            reason_code: reason.code(),
            detail: detail.into(),
        }
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn checked_u64(value: usize, label: &str) -> Result<u64, ChcQfInvariantModelArtifactError> {
    u64::try_from(value).map_err(|_| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::TooManyPredicates,
            format!("{label} does not fit in u64"),
        )
    })
}

fn validate_model_shape(
    problem: &ChcProblem,
    model: &InvariantModel,
) -> Result<(), ChcQfInvariantModelArtifactError> {
    if model.has_quantified_array_certificate() {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::GhostPairCertificate,
            "quantified ghost-pair certificates are not QF invariant models",
        ));
    }
    if model.is_empty() {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::EmptyModel,
            "empty models are acyclic-exhaustive BMC evidence, not QF invariants",
        ));
    }
    if problem.predicates().len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES
        || model.len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES
    {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::TooManyPredicates,
            format!(
                "problem/model predicate counts are {}/{}, maximum is {}",
                problem.predicates().len(),
                model.len(),
                CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES
            ),
        ));
    }

    let mut total_parameters = 0usize;
    for predicate in problem.predicates() {
        let Some(interpretation) = model.get(&predicate.id) else {
            return Err(ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::MissingPredicate,
                format!("missing interpretation for predicate `{}`", predicate.name),
            ));
        };
        if interpretation.vars.len() != predicate.arg_sorts.len() {
            return Err(ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::PredicateArityMismatch,
                format!(
                    "predicate `{}` has {} parameters, expected {}",
                    predicate.name,
                    interpretation.vars.len(),
                    predicate.arg_sorts.len()
                ),
            ));
        }
        total_parameters = total_parameters
            .checked_add(interpretation.vars.len())
            .ok_or_else(|| {
                ChcQfInvariantModelArtifactError::new(
                    ChcQfInvariantModelArtifactErrorReason::TooManyParameters,
                    "total predicate parameter count overflowed usize",
                )
            })?;
        if total_parameters > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PARAMETERS {
            return Err(ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::TooManyParameters,
                format!(
                    "total predicate parameter count exceeds {}",
                    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PARAMETERS
                ),
            ));
        }

        let mut names = HashSet::with_capacity(interpretation.vars.len());
        for (index, (variable, expected_sort)) in interpretation
            .vars
            .iter()
            .zip(&predicate.arg_sorts)
            .enumerate()
        {
            if &variable.sort != expected_sort {
                return Err(ChcQfInvariantModelArtifactError::new(
                    ChcQfInvariantModelArtifactErrorReason::PredicateSortMismatch,
                    format!(
                        "predicate `{}` parameter {index} has sort {}, expected {}",
                        predicate.name, variable.sort, expected_sort
                    ),
                ));
            }
            if !names.insert(variable.name.as_str()) {
                return Err(ChcQfInvariantModelArtifactError::new(
                    ChcQfInvariantModelArtifactErrorReason::DuplicateParameter,
                    format!(
                        "predicate `{}` repeats parameter name `{}`",
                        predicate.name, variable.name
                    ),
                ));
            }
        }
        let formula_sort = crate::pdr::validate_qf_expression(
            problem,
            &interpretation.vars,
            &interpretation.formula,
        )
        .map_err(|error| {
            ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::InvalidModelExpression,
                format!("predicate `{}`: {error}", predicate.name),
            )
        })?;
        if formula_sort != ChcSort::Bool {
            return Err(ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::PredicateReturnSortMismatch,
                format!("predicate `{}` interpretation is not Bool", predicate.name),
            ));
        }
    }

    if model.len() != problem.predicates().len() {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::PredicateCountMismatch,
            format!(
                "model contains {} interpretations for {} problem predicates",
                model.len(),
                problem.predicates().len()
            ),
        ));
    }
    Ok(())
}

fn validate_syntax_bounds(model: &str) -> Result<(), ChcQfInvariantModelArtifactError> {
    if model.len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_MODEL_BYTES {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelTooLarge,
            format!(
                "model has {} bytes, maximum is {}",
                model.len(),
                CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_MODEL_BYTES
            ),
        ));
    }

    let mut depth = 0usize;
    let mut in_comment = false;
    let mut in_quoted_symbol = false;
    for character in model.chars() {
        if in_comment {
            if character == '\n' {
                in_comment = false;
            }
            continue;
        }
        if in_quoted_symbol {
            if character == '|' {
                in_quoted_symbol = false;
            }
            continue;
        }
        match character {
            ';' => in_comment = true,
            '|' => in_quoted_symbol = true,
            '(' => {
                depth = depth.checked_add(1).ok_or_else(|| {
                    ChcQfInvariantModelArtifactError::new(
                        ChcQfInvariantModelArtifactErrorReason::NestingTooDeep,
                        "parenthesis depth overflowed usize",
                    )
                })?;
                if depth > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH {
                    return Err(ChcQfInvariantModelArtifactError::new(
                        ChcQfInvariantModelArtifactErrorReason::NestingTooDeep,
                        format!(
                            "model nesting exceeds {}",
                            CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH
                        ),
                    ));
                }
            }
            ')' => {
                depth = depth.checked_sub(1).ok_or_else(|| {
                    ChcQfInvariantModelArtifactError::new(
                        ChcQfInvariantModelArtifactErrorReason::ModelParseFailed,
                        "model contains an unmatched closing parenthesis",
                    )
                })?;
            }
            _ => {}
        }
    }
    if in_quoted_symbol || depth != 0 {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelParseFailed,
            "model has an unterminated quoted symbol or unbalanced parentheses",
        ));
    }
    Ok(())
}

fn envelope_for_model(
    problem: &ChcProblem,
    model_smtlib: String,
    predicate_count: usize,
) -> Result<QfInvariantModelEnvelope, ChcQfInvariantModelArtifactError> {
    validate_syntax_bounds(&model_smtlib)?;
    Ok(QfInvariantModelEnvelope {
        schema: CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA.to_string(),
        schema_version: 1,
        role: CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE.to_string(),
        model_format: CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT.to_string(),
        normalized_input_sha256: normalized_chc_input_sha256(problem),
        predicate_count: checked_u64(predicate_count, "predicate count")?,
        model_sha256: sha256_hex(model_smtlib.as_bytes()),
        model_smtlib,
    })
}

fn parse_bounded_model_smtlib(
    problem: &ChcProblem,
    model_smtlib: &str,
) -> Result<InvariantModel, ChcQfInvariantModelArtifactError> {
    validate_syntax_bounds(model_smtlib)?;
    catch_unwind(AssertUnwindSafe(|| {
        InvariantModel::parse_smtlib(model_smtlib, problem)
    }))
    .map_err(|_| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelParserPanicked,
            "AY invariant parser panicked while parsing bounded artifact",
        )
    })?
    .map_err(|error| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelParseFailed,
            error.to_string(),
        )
    })
}

fn encode_qf_invariant_model_artifact(
    problem: &ChcProblem,
    model: &InvariantModel,
) -> Result<ChcProofRunArtifact, ChcQfInvariantModelArtifactError> {
    validate_model_shape(problem, model)?;
    // Models produced by solver internals may contain semantically valid but
    // non-normalized expression nodes (for example, a raw `not (not x)`).
    // Canonicalize through the same bounded parser used by the consumer before
    // sealing bytes. The final strict self-parse below still requires this text
    // to be a byte-for-byte fixed point and independently validates its shape.
    let emitted_model = model.to_smtlib(problem);
    let canonical_model = parse_bounded_model_smtlib(problem, &emitted_model)?;
    validate_model_shape(problem, &canonical_model)?;
    let envelope = envelope_for_model(
        problem,
        canonical_model.to_smtlib(problem),
        canonical_model.len(),
    )?;
    let bytes = serde_json::to_vec(&envelope).map_err(|error| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::SerializationFailed,
            error.to_string(),
        )
    })?;
    if bytes.len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ArtifactTooLarge,
            format!(
                "artifact has {} bytes, maximum is {}",
                bytes.len(),
                CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES
            ),
        ));
    }

    // The producer accepts its own bytes only if the exact consumer boundary
    // can parse them. This prevents emitting a nominal model that already fails
    // strict canonical replay.
    parse_qf_invariant_model_artifact(problem, &bytes)?;
    Ok(ChcProofRunArtifact::new(
        CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA,
        CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE,
        bytes,
    ))
}

impl ChcPdrProofRun {
    /// Serialize the actual verified QF invariant for independent replay.
    ///
    /// Only a Safe, non-empty, non-ghost, complete model can produce this
    /// artifact. Every other evidence class returns a typed rejection.
    pub fn quantifier_free_invariant_model_artifact(
        &self,
    ) -> Result<ChcProofRunArtifact, ChcQfInvariantModelArtifactError> {
        let VerifiedChcResult::Safe(invariant) = self.result() else {
            return Err(ChcQfInvariantModelArtifactError::new(
                ChcQfInvariantModelArtifactErrorReason::ResultNotSafe,
                "only a Safe proof run carries an inductive invariant",
            ));
        };
        let problem = self.problem();
        encode_qf_invariant_model_artifact(problem, invariant.model())
    }
}

/// Strictly parse and re-bind an actual QF invariant-model artifact.
///
/// This function grants no proof authority: it returns an untrusted candidate
/// [`InvariantModel`] which a consumer must independently discharge against the
/// exact problem. It does guarantee bounded parsing, exact schema/problem/hash
/// binding, complete predicate coverage and byte-canonical AY round-trip.
pub fn parse_qf_invariant_model_artifact(
    problem: &ChcProblem,
    bytes: &[u8],
) -> Result<InvariantModel, ChcQfInvariantModelArtifactError> {
    if bytes.len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ArtifactTooLarge,
            format!(
                "artifact has {} bytes, maximum is {}",
                bytes.len(),
                CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES
            ),
        ));
    }
    let envelope: QfInvariantModelEnvelope = serde_json::from_slice(bytes).map_err(|error| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::MalformedEnvelope,
            error.to_string(),
        )
    })?;
    let canonical_envelope = serde_json::to_vec(&envelope).map_err(|error| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::SerializationFailed,
            error.to_string(),
        )
    })?;
    if canonical_envelope != bytes {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::NonCanonicalEnvelope,
            "artifact JSON differs from AY's canonical field order/escaping",
        ));
    }
    if envelope.schema != CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA || envelope.schema_version != 1 {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::SchemaMismatch,
            format!(
                "unsupported schema/version `{}`/{}",
                envelope.schema, envelope.schema_version
            ),
        ));
    }
    if envelope.role != CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::RoleMismatch,
            format!("unexpected artifact role `{}`", envelope.role),
        ));
    }
    if envelope.model_format != CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelFormatMismatch,
            format!("unsupported model format `{}`", envelope.model_format),
        ));
    }
    let expected_problem_hash = normalized_chc_input_sha256(problem);
    if envelope.normalized_input_sha256 != expected_problem_hash {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ProblemHashMismatch,
            "artifact normalized-input hash does not match the supplied problem",
        ));
    }
    validate_syntax_bounds(&envelope.model_smtlib)?;
    if sha256_hex(envelope.model_smtlib.as_bytes()) != envelope.model_sha256 {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelHashMismatch,
            "embedded model digest does not match its bytes",
        ));
    }

    let parsed = parse_bounded_model_smtlib(problem, &envelope.model_smtlib)?;

    let canonical_model = catch_unwind(AssertUnwindSafe(|| {
        validate_model_shape(problem, &parsed)?;
        Ok::<_, ChcQfInvariantModelArtifactError>(parsed.to_smtlib(problem))
    }))
    .map_err(|_| {
        ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::ModelParserPanicked,
            "AY invariant validation or canonical serialization panicked",
        )
    })??;
    if envelope.predicate_count != checked_u64(parsed.len(), "parsed predicate count")? {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::PredicateCountMismatch,
            format!(
                "envelope declares {} predicates, parsed model contains {}",
                envelope.predicate_count,
                parsed.len()
            ),
        ));
    }
    if canonical_model != envelope.model_smtlib {
        return Err(ChcQfInvariantModelArtifactError::new(
            ChcQfInvariantModelArtifactErrorReason::NonCanonicalModel,
            "model contains ignored, duplicate, unknown, reordered, or trailing syntax",
        ));
    }
    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use crate::{ChcExpr, ChcOp, ChcParser, ChcVar, PredicateInterpretation};

    fn fixture() -> (ChcProblem, InvariantModel) {
        let problem = ChcParser::parse(
            r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(declare-fun Aux (Int Bool) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (b Bool)) (=> (and (Inv x) b) (Aux x b))))
(assert (forall ((x Int) (b Bool)) (=> (and (Aux x b) (< x 0)) false)))
(check-sat)
"#,
        )
        .expect("fixture problem parses");
        let model = InvariantModel::parse_smtlib(
            r#"
(define-fun Inv ((x Int)) Bool (>= x 0))
(define-fun Aux ((x Int) (b Bool)) Bool (and (>= x 0) b))
"#,
            &problem,
        )
        .expect("fixture model parses");
        (problem, model)
    }

    fn artifact_bytes_with_model(
        problem: &ChcProblem,
        model_smtlib: String,
        predicate_count: usize,
    ) -> Vec<u8> {
        let envelope = envelope_for_model(problem, model_smtlib, predicate_count)
            .expect("test envelope should be within bounds");
        serde_json::to_vec(&envelope).expect("test envelope serializes")
    }

    #[test]
    fn actual_qf_model_artifact_round_trips_canonically() {
        let (problem, model) = fixture();
        let artifact = encode_qf_invariant_model_artifact(&problem, &model)
            .expect("complete QF model should serialize");
        assert_eq!(artifact.schema(), CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA);
        assert_eq!(artifact.role(), CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE);
        let parsed = parse_qf_invariant_model_artifact(&problem, artifact.bytes())
            .expect("solver-owned bytes should parse strictly");
        assert_eq!(parsed.to_smtlib(&problem), model.to_smtlib(&problem));
    }

    #[test]
    fn actual_bitvector_qf_model_artifact_round_trips_canonically() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![ChcSort::Bool, ChcSort::BitVec(64)]);
        let model = InvariantModel::parse_smtlib(
            r#"
(define-fun Inv ((flag Bool) (count (_ BitVec 64))) Bool
  (and
    (or flag (not (= ((_ extract 0 0) count) (_ bv1 1))))
    (= (bvand (bvsub count (_ bv1 64)) (_ bv1 64)) (_ bv1 64))))
"#,
            &problem,
        )
        .expect("BV model should parse");
        let artifact = encode_qf_invariant_model_artifact(&problem, &model)
            .expect("BV QF model should serialize");
        let parsed = parse_qf_invariant_model_artifact(&problem, artifact.bytes())
            .expect("BV QF artifact should parse strictly");
        assert_eq!(parsed.to_smtlib(&problem), model.to_smtlib(&problem));
    }

    #[test]
    fn producer_canonicalizes_solver_owned_double_negation() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Bool]);
        let flag = ChcVar::new("flag", ChcSort::Bool);
        let inner_not = ChcExpr::Op(ChcOp::Not, vec![Arc::new(ChcExpr::Var(flag.clone()))]);
        let raw_double_not = ChcExpr::Op(ChcOp::Not, vec![Arc::new(inner_not)]);
        let mut model = InvariantModel::new();
        model.set(
            inv,
            PredicateInterpretation::new(vec![flag], raw_double_not),
        );

        let artifact = encode_qf_invariant_model_artifact(&problem, &model)
            .expect("producer must canonicalize its valid solver-owned model");
        let parsed = parse_qf_invariant_model_artifact(&problem, artifact.bytes())
            .expect("canonicalized producer bytes must pass strict replay parsing");
        let canonical = parsed.to_smtlib(&problem);
        assert!(canonical.contains("\n  flag)"));
        assert!(!canonical.contains("(not (not flag))"));
    }

    #[test]
    fn actual_datatype_qf_model_artifact_round_trips_qualified_functions() {
        let mut problem = ChcProblem::new();
        problem.add_datatype_def(
            "List".to_string(),
            vec![
                ("nil".to_string(), Vec::new()),
                (
                    "cons".to_string(),
                    vec![
                        ("head".to_string(), ChcSort::Int),
                        (
                            "tail".to_string(),
                            ChcSort::Uninterpreted("List".to_string()),
                        ),
                    ],
                ),
            ],
        );
        problem.declare_predicate("Inv", vec![ChcSort::Uninterpreted("List".to_string())]);
        let model = InvariantModel::parse_smtlib(
            "(define-fun Inv ((x List)) Bool (= (tail x) nil))",
            &problem,
        )
        .expect("datatype model should parse");

        let artifact = encode_qf_invariant_model_artifact(&problem, &model)
            .expect("qualified datatype functions should round-trip");
        let parsed = parse_qf_invariant_model_artifact(&problem, artifact.bytes())
            .expect("datatype artifact should pass strict parsing");
        assert_eq!(parsed.to_smtlib(&problem), model.to_smtlib(&problem));
    }

    #[test]
    fn free_unknown_marker_and_ill_sorted_models_fail_closed() {
        let (problem, _) = fixture();
        let invalid_inv_bodies = [
            "(and (= x 0) 1)",
            "(= (attacker x) 0)",
            "(= attacker 0)",
            "(_ is attacker)",
        ];
        for body in invalid_inv_bodies {
            let source = format!(
                "(define-fun Inv ((x Int)) Bool {body})\n\
                 (define-fun Aux ((x Int) (b Bool)) Bool (and (>= x 0) b))\n"
            );
            let bytes = artifact_bytes_with_model(&problem, source, 2);
            let error = parse_qf_invariant_model_artifact(&problem, &bytes)
                .expect_err("invalid QF expression must fail closed");
            assert!(
                matches!(
                    error.reason,
                    ChcQfInvariantModelArtifactErrorReason::InvalidModelExpression
                        | ChcQfInvariantModelArtifactErrorReason::ModelParseFailed
                ),
                "body `{body}` failed with unexpected reason: {error:?}"
            );
        }
    }

    #[test]
    fn ill_sorted_and_unbounded_bitvector_models_fail_closed() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
        let invalid_bodies = [
            "(= (bvadd x (_ bv1 16)) x)",
            "(= ((_ extract 8 0) x) (_ bv0 9))",
            "(= ((_ repeat 1048576) x) (_ bv0 8))",
            "(bvult 0 1)",
        ];
        for body in invalid_bodies {
            let source = format!("(define-fun Inv ((x (_ BitVec 8))) Bool {body})\n");
            let bytes = artifact_bytes_with_model(&problem, source, 1);
            let error = parse_qf_invariant_model_artifact(&problem, &bytes)
                .expect_err("ill-sorted BV expression must fail closed");
            assert_eq!(
                error.reason,
                ChcQfInvariantModelArtifactErrorReason::InvalidModelExpression,
                "body `{body}`"
            );
        }
    }

    #[test]
    fn producer_and_parser_remain_bound_to_the_solved_problem() {
        let input = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (< x 5) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))
(check-sat)
"#;
        let problem = ChcParser::parse(input).expect("problem parses");
        let run = crate::engines::solve_pdr_proof(problem, crate::PdrConfig::default())
            .expect("PDR solve succeeds");
        assert!(run.accepted_as_proof(), "fixture must be proof-grade");

        let different_problem = ChcParser::parse(&input.replace("(> x 10)", "(> x 11)"))
            .expect("different problem parses");
        let artifact = run
            .quantifier_free_invariant_model_artifact()
            .expect("sealed run should emit its own invariant artifact");
        parse_qf_invariant_model_artifact(run.problem(), artifact.bytes())
            .expect("artifact must replay against the stored solved problem");
        let error = parse_qf_invariant_model_artifact(&different_problem, artifact.bytes())
            .expect_err("artifact cannot replay against another problem");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::ProblemHashMismatch
        );
    }

    #[test]
    fn empty_and_incomplete_models_are_not_replayable_qf_artifacts() {
        let (problem, model) = fixture();
        let empty = encode_qf_invariant_model_artifact(&problem, &InvariantModel::new())
            .expect_err("empty BMC-class model must be excluded");
        assert_eq!(
            empty.reason,
            ChcQfInvariantModelArtifactErrorReason::EmptyModel
        );

        let only_inv = model
            .to_smtlib(&problem)
            .split("(define-fun Aux")
            .next()
            .expect("prefix exists")
            .to_string();
        let bytes = artifact_bytes_with_model(&problem, only_inv, 1);
        let missing = parse_qf_invariant_model_artifact(&problem, &bytes)
            .expect_err("missing predicate must fail closed");
        assert_eq!(
            missing.reason,
            ChcQfInvariantModelArtifactErrorReason::MissingPredicate
        );
    }

    #[test]
    fn duplicate_unknown_command_unknown_predicate_and_trailing_text_are_rejected() {
        let (problem, model) = fixture();
        let canonical = model.to_smtlib(&problem);
        let attacks = [
            format!("{canonical}(define-fun Inv ((x Int)) Bool (= x 7))\n"),
            format!("{canonical}(check-sat)\n"),
            format!("{canonical}(define-fun Attacker ((x Int)) Bool true)\n"),
            format!("{canonical}attacker-trailing-material"),
        ];
        for attack in attacks {
            let bytes = artifact_bytes_with_model(&problem, attack, 2);
            let error = parse_qf_invariant_model_artifact(&problem, &bytes)
                .expect_err("ignored/duplicate/trailing syntax must fail closed");
            assert!(matches!(
                error.reason,
                ChcQfInvariantModelArtifactErrorReason::NonCanonicalModel
                    | ChcQfInvariantModelArtifactErrorReason::ModelParseFailed
            ));
        }
    }

    #[test]
    fn wrong_arity_sort_and_return_sort_are_rejected() {
        let (problem, model) = fixture();
        let canonical = model.to_smtlib(&problem);
        let attacks = [
            canonical.replacen("((x Int)) Bool", "((x Int) (z Int)) Bool", 1),
            canonical.replacen("((x Int)) Bool", "((x Bool)) Bool", 1),
            canonical.replacen("((x Int)) Bool", "((x Int)) Int", 1),
        ];
        for attack in attacks {
            let bytes = artifact_bytes_with_model(&problem, attack, 2);
            parse_qf_invariant_model_artifact(&problem, &bytes)
                .expect_err("arity/sort/return drift must fail closed");
        }
    }

    #[test]
    fn envelope_duplicate_unknown_and_noncanonical_json_are_rejected() {
        let (problem, model) = fixture();
        let valid = artifact_bytes_with_model(&problem, model.to_smtlib(&problem), 2);

        let mut noncanonical = valid.clone();
        noncanonical.push(b'\n');
        let error = parse_qf_invariant_model_artifact(&problem, &noncanonical)
            .expect_err("JSON whitespace drift must fail closed");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::NonCanonicalEnvelope
        );

        let text = String::from_utf8(valid).expect("artifact is UTF-8 JSON");
        let duplicate = text.replacen("{\"schema\":", "{\"schema\":\"forged\",\"schema\":", 1);
        let error = parse_qf_invariant_model_artifact(&problem, duplicate.as_bytes())
            .expect_err("duplicate JSON field must fail closed");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::MalformedEnvelope
        );

        let unknown = text.replacen("{\"schema\":", "{\"attacker\":true,\"schema\":", 1);
        let error = parse_qf_invariant_model_artifact(&problem, unknown.as_bytes())
            .expect_err("unknown JSON field must fail closed");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::MalformedEnvelope
        );
    }

    #[test]
    fn artifact_and_parser_depth_bounds_are_enforced_before_parsing() {
        let (problem, _) = fixture();
        let oversized = vec![b' '; CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES + 1];
        let error = parse_qf_invariant_model_artifact(&problem, &oversized)
            .expect_err("oversized artifact must be rejected before JSON parsing");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::ArtifactTooLarge
        );

        let nested = format!(
            "{}true{}",
            "(not ".repeat(CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH + 1),
            ")".repeat(CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH + 1)
        );
        let error = envelope_for_model(&problem, nested, 2)
            .expect_err("deep model must be rejected before recursive parsing");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::NestingTooDeep
        );
    }

    #[test]
    fn exact_problem_hash_is_required() {
        let (problem, model) = fixture();
        let bytes = artifact_bytes_with_model(&problem, model.to_smtlib(&problem), 2);
        let other_problem = ChcParser::parse(
            r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(declare-fun Aux (Int Bool) Bool)
(assert (forall ((x Int)) (=> (= x 1) (Inv x))))
(assert (forall ((x Int) (b Bool)) (=> (and (Aux x b) (< x 0)) false)))
(check-sat)
"#,
        )
        .expect("other problem parses");
        let error = parse_qf_invariant_model_artifact(&other_problem, &bytes)
            .expect_err("artifact must bind the exact normalized problem");
        assert_eq!(
            error.reason,
            ChcQfInvariantModelArtifactErrorReason::ProblemHashMismatch
        );
    }
}
