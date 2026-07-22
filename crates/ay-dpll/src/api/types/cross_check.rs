// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-check replay report types.

use super::{Logic, SolveResult, VerificationSummary};

/// Variant override for a replayed SMT-LIB cross-check run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CrossCheckVariant {
    /// Human-readable label used in the report and disagreement summary.
    pub label: String,
    /// Optional logic override applied for this replay run.
    pub logic: Option<Logic>,
    /// Optional SAT random seed override applied for this replay run.
    pub random_seed: Option<u64>,
}

impl CrossCheckVariant {
    /// Create a new variant with the given label and no overrides.
    pub fn new(label: impl Into<String>) -> Self {
        Self {
            label: label.into(),
            logic: None,
            random_seed: None,
        }
    }

    /// Override the logic for this variant.
    #[must_use]
    pub fn with_logic(mut self, logic: Logic) -> Self {
        self.logic = Some(logic);
        self
    }

    /// Override the SAT random seed for this variant.
    #[must_use]
    pub fn with_random_seed(mut self, seed: u64) -> Self {
        self.random_seed = Some(seed);
        self
    }
}

/// Result of one replayed cross-check run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CrossCheckRun {
    /// Human-readable label for this run.
    pub label: String,
    /// Raw solve result from the replayed run.
    pub result: SolveResult,
    /// Verification/provenance summary captured from the same run.
    pub verification: VerificationSummary,
    /// Structured unknown reason rendered as text when the run returned `unknown`.
    pub unknown_reason: Option<String>,
}

/// Trusted SAT/UNSAT contradiction found across cross-check runs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CrossCheckDisagreement {
    /// Label for the left-hand run in the contradiction.
    pub lhs_label: String,
    /// Label for the right-hand run in the contradiction.
    pub rhs_label: String,
    /// Consumer-acceptable definite result from the left-hand run.
    pub lhs: SolveResult,
    /// Consumer-acceptable definite result from the right-hand run.
    pub rhs: SolveResult,
}

/// Full report for a baseline replay plus zero or more variants.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CrossCheckReport {
    /// Replay result for the unmodified baseline script.
    pub baseline: CrossCheckRun,
    /// Replay results for each requested variant.
    pub variants: Vec<CrossCheckRun>,
    /// First trusted SAT/UNSAT contradiction found across the runs, if any.
    pub disagreement: Option<CrossCheckDisagreement>,
}
