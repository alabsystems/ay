// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model validation pipeline.
//!
//! Originally a single file (`validation.rs`), split into submodules for code health:
//! - `observation`: Per-term observation logic (validate_term_observation, etc.)
//! - `pipeline`: Core validation methods (validate_model, finalize_sat_model_validation, etc.)
//! - `term_analysis`: Term classification helpers (contains_internal_symbol, etc.)

mod definitive_eval;
mod observation;
mod pipeline;
mod term_analysis;

pub(crate) use definitive_eval::{
    check_definitive_false, dt_axiom_bool, dt_equality_decidable_by_reduction,
    dt_equality_operands_fully_ground,
};

use ay_core::{
    TermId, VerificationBoundary, VerificationEvidenceKind, VerificationFailure,
    VerificationVerdict,
};

use crate::executor_types::ModelValidationError;

/// Result of boolean skeleton verification (#7912).
///
/// When `skip_model_eval` is set (temporary inner solves via
/// incremental_scope.rs), full model evaluation is intentionally deferred. This
/// struct reports how many assertions were verified at the SAT boolean
/// skeleton level (term_to_var mapping exists and SAT model value is true),
/// how many had no mapping (unverifiable at this level), and how many had a
/// mapping but the SAT model said false (violations indicating a real
/// soundness bug).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SkeletonVerificationResult {
    /// Assertions whose Tseitin variable is assigned true in the SAT model.
    pub(crate) verified: usize,
    /// Assertions without a term_to_var mapping (cannot be checked at SAT level).
    pub(crate) unmapped: usize,
    /// Assertions whose Tseitin variable is assigned false — boolean skeleton violations.
    pub(crate) violations: usize,
    /// Total assertions inspected.
    pub(crate) total: usize,
}

/// Statistics from `validate_model` showing how many assertions were checked
/// vs skipped per category. Provides observability into silent skip sites
/// that would otherwise hide partial validation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ValidationStats {
    /// Assertions accepted as verified evidence at this layer.
    pub checked: usize,

    /// Assertions accepted via theory-solver delegation.
    pub delegated_checks: usize,
    /// Delegated checks whose assertion contains array terms.
    pub array_delegated_checks: usize,
    /// Assertions skipped (contain internal encoding symbols).
    pub skipped_internal: usize,
    /// Assertions skipped (contain quantifiers).
    pub skipped_quantifier: usize,
    /// Assertions skipped (contain datatype terms).
    pub skipped_datatype: usize,
    /// Assertions skipped (datatype with BV comparisons).
    pub skipped_dtbv: usize,

    /// Assertions skipped (mixed arithmetic+array terms).
    pub skipped_arith_array_mix: usize,

    /// Number of SAT-model-agrees fallbacks.
    /// When the evaluator returns true but the domain is arithmetic/BV or the
    /// term contains nested quantifiers, we record a Fallback observation.
    pub sat_fallback_count: usize,
    /// Total assertions processed (checked + skipped + fallback).
    pub total: usize,
}

impl ValidationStats {
    /// Return (independent_count, delegated_count, incomplete_count) tuple for
    /// the consumer-facing SAT verification provenance counters.
    pub(crate) fn verification_evidence_counts(&self) -> (u64, u64, u64) {
        let independent = self.checked.saturating_sub(self.delegated_checks) as u64;
        let delegated = self.delegated_checks as u64;
        let incomplete = (self.skipped_internal
            + self.skipped_quantifier
            + self.skipped_datatype
            + self.skipped_dtbv
            + self.skipped_arith_array_mix
            + self.sat_fallback_count) as u64;
        (independent, delegated, incomplete)
    }
}

struct ValidationAttempt {
    stats: Option<ValidationStats>,
    error: Option<ModelValidationError>,
    /// Exact ground assertion whose observation failed. `None` for aggregate
    /// pipeline failures (for example, the circular-fallback proportion guard).
    failed_assertion: Option<TermId>,
}

impl ValidationAttempt {
    fn success(stats: ValidationStats) -> Self {
        Self {
            stats: Some(stats),
            error: None,
            failed_assertion: None,
        }
    }

    fn failure(stats: Option<ValidationStats>, error: ModelValidationError) -> Self {
        Self {
            stats,
            error: Some(error),
            failed_assertion: None,
        }
    }

    fn assertion_failure(
        stats: Option<ValidationStats>,
        error: ModelValidationError,
        assertion: TermId,
    ) -> Self {
        Self {
            stats,
            error: Some(error),
            failed_assertion: Some(assertion),
        }
    }

    fn into_result(self) -> Result<ValidationStats, ModelValidationError> {
        match (self.stats, self.error) {
            (Some(stats), None) => Ok(stats),
            (_, Some(error)) => Err(error),
            (None, None) => unreachable!("validation attempt must contain stats or an error"),
        }
    }
}

/// Bit flags for precomputed term classification in `precompute_term_flags`.
/// Shared between producer (`precompute_term_flags`) and consumer (`validate_model`)
/// to prevent silent flag drift (#5567).
pub(super) const TERM_FLAG_INTERNAL: u8 = 1;
pub(super) const TERM_FLAG_QUANTIFIER: u8 = 2;
pub(super) const TERM_FLAG_DATATYPE: u8 = 4;
pub(super) const TERM_FLAG_ARRAY: u8 = 8;
pub(super) const TERM_FLAG_BV_CMP: u8 = 16;
pub(super) const TERM_FLAG_SEQ: u8 = 32;
pub(super) const TERM_FLAG_STRING: u8 = 64;
pub(super) const TERM_FLAG_FP: u8 = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ValidationTarget {
    GroundAssertion,
    Assumption,
}

impl ValidationTarget {
    fn boundary(self) -> VerificationBoundary {
        match self {
            Self::GroundAssertion => VerificationBoundary::SmtGroundAssertion,
            Self::Assumption => VerificationBoundary::SmtAssumption,
        }
    }

    fn entry(self, index: usize) -> String {
        match self {
            Self::GroundAssertion => format!("Assertion {index}"),
            Self::Assumption => format!("Assumption {index}"),
        }
    }

    fn violated_entry(self, index: usize) -> String {
        match self {
            Self::GroundAssertion => format!("Assertion {index} violated"),
            Self::Assumption => format!("Assumption {index} violated"),
        }
    }

    fn kind_name(self) -> &'static str {
        match self {
            Self::GroundAssertion => "assertion",
            Self::Assumption => "assumption",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ValidationSkipKind {
    Internal,
    Quantifier,
    Datatype,
    Dtbv,
    ArithArrayMix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ValidationObservation {
    Skip(ValidationSkipKind),
    Fallback(VerificationFailure),
    Verdict {
        verdict: VerificationVerdict,
        dt_only: bool,
    },
}

impl ValidationObservation {
    fn verified_at(
        boundary: VerificationBoundary,
        evidence: VerificationEvidenceKind,
        dt_only: bool,
    ) -> Self {
        Self::Verdict {
            verdict: VerificationVerdict::Verified { boundary, evidence },
            dt_only,
        }
    }

    fn independent(target: ValidationTarget, dt_only: bool) -> Self {
        Self::verified_at(
            target.boundary(),
            VerificationEvidenceKind::Independent,
            dt_only,
        )
    }

    fn delegated() -> Self {
        Self::verified_at(
            VerificationBoundary::SmtTheoryDelegation,
            VerificationEvidenceKind::DelegatedSolver,
            false,
        )
    }

    fn incomplete_at(boundary: VerificationBoundary, detail: impl Into<String>) -> Self {
        Self::Verdict {
            verdict: VerificationVerdict::Incomplete(VerificationFailure {
                boundary,
                detail: detail.into(),
            }),
            dt_only: false,
        }
    }

    fn incomplete(target: ValidationTarget, detail: impl Into<String>) -> Self {
        Self::incomplete_at(target.boundary(), detail)
    }

    fn violated(target: ValidationTarget, detail: impl Into<String>) -> Self {
        Self::Verdict {
            verdict: VerificationVerdict::Violated(VerificationFailure {
                boundary: target.boundary(),
                detail: detail.into(),
            }),
            dt_only: false,
        }
    }

    fn fallback(detail: impl Into<String>) -> Self {
        Self::Fallback(VerificationFailure {
            boundary: VerificationBoundary::SmtCircularSatFallback,
            detail: detail.into(),
        })
    }
}
