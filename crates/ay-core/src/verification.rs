// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed verification contract for SAT/SMT model validation.
//!
//! Every internal verification site in the SAT/SMT pipeline returns one of
//! three typed outcomes: [`Verified`](VerificationVerdict::Verified),
//! [`Incomplete`](VerificationVerdict::Incomplete), or
//! [`Violated`](VerificationVerdict::Violated). No caller should infer these
//! states from English substrings.
//!
//! See the development design notes for the
//! full design rationale.

/// Which verification layer produced the verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationBoundary {
    /// SAT clause database check (all clauses satisfied by model).
    SatClauseDb,
    /// SAT original formula check (pre-preprocessing clauses).
    SatOriginalFormula,
    /// SAT theory callback check (`TheoryCallback::check_model`).
    SatTheoryCallback,
    /// SMT ground assertion evaluation (independent evaluator proof).
    SmtGroundAssertion,
    /// SMT assumption evaluation (check_sat_assuming path).
    SmtAssumption,
    /// SMT theory delegation (theory solver verified during solving).
    SmtTheoryDelegation,
    /// SMT circular SAT fallback (SAT model validates itself — not evidence).
    SmtCircularSatFallback,
}

/// How the verification evidence was obtained.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationEvidenceKind {
    /// The evaluator independently proved the assertion.
    Independent,
    /// A theory solver established the invariant during solving.
    DelegatedSolver,
}

/// Structured detail for a verification failure or incompleteness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationFailure {
    /// Which boundary detected the problem.
    pub boundary: VerificationBoundary,
    /// Human-readable detail (assertion index, term description, etc.).
    pub detail: String,
}

impl std::fmt::Display for VerificationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {}", self.boundary, self.detail)
    }
}

/// Typed outcome of a single verification check.
///
/// Replaces the previous `Result<(), String>` / `Result<Stats, String>` return
/// convention where `Incomplete` vs `Violated` was inferred by substring
/// matching on `"could not be model-validated"`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationVerdict {
    /// The property was proven at this layer.
    Verified {
        /// Which boundary produced the proof.
        boundary: VerificationBoundary,
        /// How the evidence was obtained.
        evidence: VerificationEvidenceKind,
    },
    /// This layer could not prove the property. Caller must degrade to
    /// `Unknown` or consult a higher-level oracle.
    ///
    /// Circular SAT fallback MUST use this variant, never `Verified`.
    Incomplete(VerificationFailure),
    /// A concrete contradiction was found — the model definitely violates
    /// the property.
    Violated(VerificationFailure),
}

impl VerificationVerdict {
    /// Returns `true` if this verdict is `Verified`.
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified { .. })
    }

    /// Returns `true` if this verdict is `Incomplete`.
    pub fn is_incomplete(&self) -> bool {
        matches!(self, Self::Incomplete(_))
    }

    /// Returns `true` if this verdict is `Violated`.
    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated(_))
    }
}

impl std::fmt::Display for VerificationVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Verified { boundary, evidence } => {
                write!(f, "verified ({boundary:?}, {evidence:?})")
            }
            Self::Incomplete(failure) => write!(f, "incomplete: {failure}"),
            Self::Violated(failure) => write!(f, "violated: {failure}"),
        }
    }
}

#[cfg(test)]
#[path = "verification_tests.rs"]
mod tests;
