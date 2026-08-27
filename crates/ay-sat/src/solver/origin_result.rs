// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sealed wrappers for results returned by an [`ay_sat::Solver`](crate::Solver).

use crate::{AssumeResult, Literal, ProofCertificate, SatResult};

/// A [`SatResult`] returned by an `ay-sat` solver entry point.
///
/// The private constructor records solver origin; it does not independently
/// check the enclosed verdict. Authority is variant- and entry-point-specific:
///
/// - `Sat` models pass the solver's model-finalization gates for the active SAT
///   semantics. Correctness of caller-provided theory or extension semantics
///   remains the caller's responsibility.
/// - `Unsat` records a solver derivation. Its [`ProofCertificate`] may be empty,
///   incomplete, or unchecked; reconstruction completeness is not a checker
///   verdict.
/// - `Unknown` makes no satisfiability claim.
///
/// Safe external code cannot construct this wrapper, but should not treat that
/// provenance seal as an independently checked proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct SolverSatResult {
    result: SatResult,
}

impl SolverSatResult {
    /// Record a result produced by a solver entry point.
    ///
    /// Validation belongs to the producing solve path; this constructor only
    /// seals provenance within the crate.
    #[inline]
    pub(crate) fn from_solver_result(result: SatResult) -> Self {
        Self { result }
    }

    /// Borrow the underlying result for pattern matching.
    #[inline]
    pub fn result(&self) -> &SatResult {
        &self.result
    }

    /// Consume the provenance wrapper and return the underlying result.
    #[inline]
    pub fn into_inner(self) -> SatResult {
        self.result
    }

    /// Whether the solver returned `Sat`.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self.result, SatResult::Sat(_))
    }

    /// Whether the solver returned `Unsat`.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self.result, SatResult::Unsat(_))
    }

    /// Whether the solver returned `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self.result, SatResult::Unknown)
    }

    /// Borrow the model when the solver returned `Sat`.
    #[inline]
    pub fn model(&self) -> Option<&[bool]> {
        match &self.result {
            SatResult::Sat(model) => Some(model),
            SatResult::Unsat(_) | SatResult::Unknown => None,
        }
    }

    /// Consume and return the model when the solver returned `Sat`.
    #[inline]
    pub fn into_model(self) -> Option<Vec<bool>> {
        match self.result {
            SatResult::Sat(model) => Some(model),
            SatResult::Unsat(_) | SatResult::Unknown => None,
        }
    }
}

impl PartialEq<SatResult> for SolverSatResult {
    fn eq(&self, other: &SatResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<SolverSatResult> for SatResult {
    fn eq(&self, other: &SolverSatResult) -> bool {
        *self == other.result
    }
}

impl std::fmt::Display for SolverSatResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.result {
            SatResult::Sat(model) => write!(f, "sat (model size: {})", model.len()),
            SatResult::Unsat(_) => write!(f, "unsat"),
            SatResult::Unknown => write!(f, "unknown"),
        }
    }
}

/// An [`AssumeResult`] returned by an `ay-sat` assumption-solving entry point.
///
/// The private constructor records solver origin; it performs no independent
/// validation. `Sat` models pass the producing entry point's model gates, which
/// may intentionally use domain-restricted semantics in IC3 mode. An `Unsat`
/// core is solver-derived and checked for membership in the query assumptions,
/// but is not independently re-solved or proof-checked by this wrapper. Any
/// attached [`ProofCertificate`] is reconstruction data, not checker authority.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct SolverAssumeResult {
    result: AssumeResult,
}

impl SolverAssumeResult {
    /// Record a result produced by an assumption-solving entry point.
    #[inline]
    pub(crate) fn from_solver_result(result: AssumeResult) -> Self {
        Self { result }
    }

    /// Borrow the underlying result for pattern matching.
    #[inline]
    pub fn result(&self) -> &AssumeResult {
        &self.result
    }

    /// Consume the provenance wrapper and return the underlying result.
    #[inline]
    pub fn into_inner(self) -> AssumeResult {
        self.result
    }

    /// Whether the solver returned `Sat`.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self.result, AssumeResult::Sat(_))
    }

    /// Whether the solver returned `Unsat`.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self.result, AssumeResult::Unsat(..))
    }

    /// Whether the solver returned `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self.result, AssumeResult::Unknown)
    }

    /// Borrow the model when the solver returned `Sat`.
    #[inline]
    pub fn model(&self) -> Option<&[bool]> {
        match &self.result {
            AssumeResult::Sat(model) => Some(model),
            AssumeResult::Unsat(..) | AssumeResult::Unknown => None,
        }
    }

    /// Consume and return the model when the solver returned `Sat`.
    #[inline]
    pub fn into_model(self) -> Option<Vec<bool>> {
        match self.result {
            AssumeResult::Sat(model) => Some(model),
            AssumeResult::Unsat(..) | AssumeResult::Unknown => None,
        }
    }

    /// Borrow the solver-derived assumption core when present.
    ///
    /// The producing path checks that a non-empty core contains only literals
    /// from the query. This accessor does not independently establish that the
    /// selected assumptions are unsatisfiable.
    #[inline]
    pub fn unsat_core(&self) -> Option<&[Literal]> {
        match &self.result {
            AssumeResult::Unsat(core, _) => Some(core),
            AssumeResult::Sat(_) | AssumeResult::Unknown => None,
        }
    }

    /// Consume and return the solver-derived assumption core when present.
    #[inline]
    pub fn into_unsat_core(self) -> Option<Vec<Literal>> {
        match self.result {
            AssumeResult::Unsat(core, _) => Some(core),
            AssumeResult::Sat(_) | AssumeResult::Unknown => None,
        }
    }

    /// Borrow the reconstruction data attached to an `Unsat` result.
    #[inline]
    pub fn proof_certificate(&self) -> Option<&ProofCertificate> {
        match &self.result {
            AssumeResult::Unsat(_, Some(certificate)) => Some(certificate),
            AssumeResult::Sat(_) | AssumeResult::Unsat(_, None) | AssumeResult::Unknown => None,
        }
    }
}

impl PartialEq<AssumeResult> for SolverAssumeResult {
    fn eq(&self, other: &AssumeResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<SolverAssumeResult> for AssumeResult {
    fn eq(&self, other: &SolverAssumeResult) -> bool {
        *self == other.result
    }
}

impl std::fmt::Display for SolverAssumeResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.result {
            AssumeResult::Sat(model) => write!(f, "sat (model size: {})", model.len()),
            AssumeResult::Unsat(core, certificate) => {
                write!(f, "unsat (core size: {}", core.len())?;
                if certificate.is_some() {
                    write!(f, ", proof data available")?;
                }
                write!(f, ")")
            }
            AssumeResult::Unknown => write!(f, "unknown"),
        }
    }
}
