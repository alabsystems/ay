// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use ay_dpll::api::{AssumptionSolveDetails, SolveDetails, UnsatProofArtifact, VerifiedSolveResult};
use thiserror::Error;

use super::ModelValue;

pub type ExecuteValueMap<V> = ay_core::kani_compat::DetHashMap<String, V>;

/// Error type for direct execution.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExecuteError {
    /// Solver initialization failed.
    #[error("solver initialization failed: {0}")]
    SolverInit(String),

    /// Unsupported logic.
    #[error("unsupported logic: {0}")]
    UnsupportedLogic(String),

    /// Sort translation failed.
    #[error("sort translation failed: {0}")]
    SortTranslation(String),

    /// Expression translation failed.
    #[error("expression translation failed: {0}")]
    ExprTranslation(String),

    /// Constraint execution failed.
    #[error("constraint execution failed: {0}")]
    ConstraintExecution(String),

    /// Internal error.
    #[error("internal error: {0}")]
    Internal(String),
}

/// Result of direct program execution.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ExecuteResult {
    /// All assertions verified (UNSAT - no counterexample exists).
    Verified,

    /// Counterexample found (SAT - assertions can be violated).
    Counterexample {
        /// Variable assignments in the counterexample model.
        /// Map from variable name to string representation of value.
        model: ExecuteValueMap<String>,
        /// Values requested via get-value commands.
        /// Map from expression string to value string (SMT-LIB format).
        values: ExecuteValueMap<String>,
    },

    /// Execution requires fallback to SMT-LIB file path.
    ///
    /// This occurs when the program contains constructs not supported
    /// by the direct API (CHC commands, quantifiers, etc.).
    NeedsFallback(String),

    /// Solver returned unknown.
    Unknown(String),
}

/// Structured counterexample from direct execution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExecuteCounterexample {
    /// Variable assignments in the counterexample model.
    pub model: ExecuteValueMap<ModelValue>,
    /// Values requested via get-value commands.
    pub values: ExecuteValueMap<ModelValue>,
}

impl ExecuteCounterexample {
    /// Create a typed counterexample payload for `execute_typed()`.
    #[must_use]
    pub fn new(model: ExecuteValueMap<ModelValue>, values: ExecuteValueMap<ModelValue>) -> Self {
        Self { model, values }
    }
}

/// Typed result of direct program execution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExecuteTypedResult {
    /// All assertions verified (UNSAT - no counterexample exists).
    Verified,

    /// Counterexample found (SAT - assertions can be violated).
    Counterexample(ExecuteCounterexample),

    /// Execution requires fallback to SMT-LIB file path.
    NeedsFallback(String),

    /// Solver returned unknown or typed extraction failed.
    Unknown(String),
}

/// Typed classification for direct-execution fallback before any solve occurs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExecuteFallbackKind {
    SoftAssertions,
    OptimizationObjectives,
    ChcRelationDeclaration,
    ChcRule,
    ChcQuery,
    UnsupportedExpression,
}

/// Structured fallback detail for execute_direct pre-solve exits.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExecuteFallback {
    pub kind: ExecuteFallbackKind,
    pub message: String,
}

/// Typed classification for Unknown/degraded execute_direct outcomes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExecuteDegradationKind {
    ConstraintTranslationPanic,
    SolverPanic,
    SolverUnknown,
    UnvalidatedSatBoundary,
    ModelExtractionFailure,
    ModelExtractionPanic,
    GetValueExtractionFailure,
    GetValueExtractionPanic,
}

/// Structured degradation detail for execute_direct Unknown outcomes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExecuteDegradation {
    pub kind: ExecuteDegradationKind,
    pub message: String,
}

/// Typed envelope for direct execution with provenance metadata.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ExecuteTypedDetails {
    pub result: ExecuteTypedResult,
    pub fallback: Option<ExecuteFallback>,
    pub degradation: Option<ExecuteDegradation>,
    pub solve_details: Option<SolveDetails>,
    pub assumption_solve_details: Option<AssumptionSolveDetails>,
    /// UNSAT proof artifact, when available (#6778).
    ///
    /// Populated only on the UNSAT path when proof production is enabled
    /// (`:produce-proofs true`). Contains rendered Alethe text, diagnostic
    /// quality metrics, the strict proof verdict, and restricted-rule-subset status.
    pub unsat_proof: Option<UnsatProofArtifact>,
}

/// Untyped projection of [`ExecuteTypedDetails`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ExecuteDetails {
    pub result: ExecuteResult,
    pub fallback: Option<ExecuteFallback>,
    pub degradation: Option<ExecuteDegradation>,
    pub solve_details: Option<SolveDetails>,
    pub assumption_solve_details: Option<AssumptionSolveDetails>,
    /// UNSAT proof artifact, when available (#6778).
    ///
    /// Carries the same acceptance boundary as `ExecuteTypedDetails`:
    /// strict-verdict state plus the restricted rule subset marker.
    pub unsat_proof: Option<UnsatProofArtifact>,
}

/// Per-check-sat outcome for incremental execution (#8154).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CheckSatOutcome {
    /// Typed result (Verified/Counterexample/Unknown).
    pub result: ExecuteTypedResult,
    /// Degradation detail, when the result was downgraded.
    pub degradation: Option<ExecuteDegradation>,
    /// Solve details from the solver, when available.
    pub solve_details: Option<SolveDetails>,
    /// UNSAT proof artifact, when available.
    pub unsat_proof: Option<UnsatProofArtifact>,
    /// Zero-based index of this check-sat in the program.
    pub check_sat_index: usize,
    /// Unsat core names, when the result is UNSAT and cores are available.
    pub unsat_core: Option<Vec<String>>,
}

pub(super) enum DirectSolveEnvelope {
    Solve(SolveDetails),
    Assumptions(AssumptionSolveDetails),
}

impl DirectSolveEnvelope {
    pub(super) fn verified_result(&self) -> &VerifiedSolveResult {
        match self {
            Self::Solve(details) => &details.result,
            Self::Assumptions(details) => &details.solve.result,
        }
    }

    pub(super) fn solve_details(&self) -> Option<&SolveDetails> {
        match self {
            Self::Solve(details) => Some(details),
            Self::Assumptions(_) => None,
        }
    }

    pub(super) fn assumption_solve_details(&self) -> Option<&AssumptionSolveDetails> {
        match self {
            Self::Solve(_) => None,
            Self::Assumptions(details) => Some(details),
        }
    }

    pub(super) fn unknown_reason(&self) -> Option<ay_dpll::UnknownReason> {
        match self {
            Self::Solve(details) => details.unknown_reason,
            Self::Assumptions(details) => details.solve.unknown_reason,
        }
    }
}
