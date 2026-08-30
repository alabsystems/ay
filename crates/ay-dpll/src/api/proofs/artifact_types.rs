// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small consumer-facing payload types used by proof artifacts.

use num_rational::BigRational;

/// Consumer-facing acceptance mode for an UNSAT proof artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofAcceptanceMode {
    /// Require AY's native strict proof validation to have succeeded.
    Strict,
    /// Require strict validation plus the restricted-rule-subset strict subset.
    RestrictedRuleSubset,
}

/// Structured Farkas payload for a theory lemma in the exported proof.
///
/// Coefficients are promoted to [`BigRational`] so downstream consumers can
/// use the certificate without depending on ay-core's internal `Rational64`
/// representation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct FarkasCertificate {
    /// Index of the `TheoryLemma` step in the exported proof DAG.
    pub proof_step_index: u32,
    /// Non-negative coefficients for the lemma's input constraints.
    pub coefficients: Vec<BigRational>,
}
