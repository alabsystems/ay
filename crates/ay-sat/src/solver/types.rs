// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public types for the SAT solver: result enums, verified wrappers,
//! watch-order policy, and per-variable flag constants.

// Verified types (VerifiedSatResult, VerifiedAssumeResult) live in this module.
// Crate-level `#![forbid(unsafe_code)]` prevents transmute-based type forgery.

use crate::literal::Literal;
use crate::proof_certificate::ProofCertificate;

pub use super::tracing_config::SetSolutionError;

/// Memory usage statistics for the solver
#[allow(clippy::panic)]
#[cfg(test)]
#[derive(Debug, Clone, Default)]
pub(crate) struct MemoryStats {
    /// Inline `Solver` struct bytes: fixed-size state, sub-struct shells, and
    /// all Vec headers stored directly on the solver.
    pub solver_shell: usize,
    /// Number of variables
    pub num_vars: usize,
    /// Number of clauses
    pub num_clauses: usize,
    /// Total number of literals across all clauses
    pub total_literals: usize,
    /// Per-variable data (assignment, level, reason, trail_pos, phase)
    pub var_data: usize,
    /// VSIDS activity scores
    pub vsids: usize,
    /// Conflict analyzer
    pub conflict: usize,
    /// Clause arena (inline headers + literals)
    pub arena: usize,
    /// Watched literal lists
    pub watches: usize,
    /// Trail and trail limits
    pub trail: usize,
    /// Support buffers that are live outside the core BCP/conflict buckets.
    pub support: usize,
    /// Clause IDs (for LRAT proofs)
    pub clause_ids: usize,
    /// Immutable original-formula ledger kept alongside the arena.
    pub original_ledger: usize,
    /// Inprocessing engines (vivify, subsume, probe, bve, bce, htr, gates, sweep)
    pub inprocessing: usize,
    /// Reconstruction stack (BVE/BCE/sweep witness entries)
    pub reconstruction: usize,
}

#[allow(clippy::panic)]
#[cfg(test)]
impl MemoryStats {
    /// Total estimated memory usage in bytes
    pub(crate) fn total(&self) -> usize {
        self.solver_shell
            + self.var_data
            + self.vsids
            + self.conflict
            + self.arena
            + self.watches
            + self.trail
            + self.support
            + self.clause_ids
            + self.original_ledger
            + self.inprocessing
            + self.reconstruction
    }

    /// Memory usage per variable (excluding clause database)
    pub(crate) fn per_var(&self) -> f64 {
        if self.num_vars == 0 {
            0.0
        } else {
            (self.var_data
                + self.vsids
                + self.conflict
                + self.support
                + self.clause_ids
                + self.inprocessing) as f64
                / self.num_vars as f64
        }
    }

    /// Memory usage per literal in clause database
    pub(crate) fn per_literal(&self) -> f64 {
        if self.total_literals == 0 {
            0.0
        } else {
            self.arena as f64 / self.total_literals as f64
        }
    }
}

/// Factorization statistics
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct FactorStats {
    /// Total factorization rounds run
    pub rounds: u64,
    /// Total factoring groups applied
    pub factored_count: u64,
    /// Total extension variables introduced
    pub extension_vars: u64,
}

#[allow(clippy::panic)]
#[cfg(test)]
impl std::fmt::Display for MemoryStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Memory Statistics:")?;
        writeln!(f, "  Variables: {}", self.num_vars)?;
        writeln!(f, "  Clauses: {}", self.num_clauses)?;
        writeln!(f, "  Total literals: {}", self.total_literals)?;
        writeln!(f)?;
        writeln!(f, "  Solver shell: {} bytes", self.solver_shell)?;
        writeln!(f, "  Per-variable data: {} bytes", self.var_data)?;
        writeln!(f, "  VSIDS: {} bytes", self.vsids)?;
        writeln!(f, "  Conflict analyzer: {} bytes", self.conflict)?;
        writeln!(f, "  Clause database: {} bytes", self.arena)?;
        writeln!(f, "  Watched lists: {} bytes", self.watches)?;
        writeln!(f, "  Trail: {} bytes", self.trail)?;
        writeln!(f, "  Support buffers: {} bytes", self.support)?;
        writeln!(f, "  Clause IDs: {} bytes", self.clause_ids)?;
        writeln!(
            f,
            "  Original clause ledger: {} bytes",
            self.original_ledger
        )?;
        writeln!(f, "  Inprocessing: {} bytes", self.inprocessing)?;
        writeln!(f)?;
        writeln!(
            f,
            "  Total: {} bytes ({:.2} MB)",
            self.total(),
            self.total() as f64 / 1_048_576.0
        )?;
        writeln!(f, "  Per variable: {:.2} bytes", self.per_var())?;
        writeln!(f, "  Per literal: {:.2} bytes", self.per_literal())
    }
}

/// Result of SAT solving
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "SAT results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum SatResult {
    /// Unsatisfiable, with a lazily-materialized proof certificate.
    ///
    /// The certificate is zero-cost when not consumed: proof reconstruction
    /// is deferred until [`ProofCertificate::materialize()`] is called.
    Unsat(ProofCertificate),
    /// Satisfiable with model
    Sat(Vec<bool>),
    /// Unknown (timeout, etc.)
    Unknown,
}

impl PartialEq for SatResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sat(a), Self::Sat(b)) => a == b,
            (Self::Unsat(_), Self::Unsat(_)) => true,
            (Self::Unknown, Self::Unknown) => true,
            _ => false,
        }
    }
}

impl Eq for SatResult {}

impl SatResult {
    /// Returns true if the result is Sat.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    /// Returns true if the result is Unsat.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat(_))
    }

    /// Returns the proof certificate if the result is Unsat.
    #[inline]
    pub fn proof_certificate(&self) -> Option<&ProofCertificate> {
        match self {
            Self::Unsat(cert) => Some(cert),
            _ => None,
        }
    }

    /// Returns true if the result is Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

/// Structured classification for SAT-side `Unknown` outcomes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SatUnknownReason {
    /// Solve was interrupted by callback or interrupt flag.
    Interrupted,
    /// Theory callback requested stop (`TheoryPropResult::Stop`).
    TheoryStop,
    /// Unsupported API/configuration combination.
    UnsupportedConfig,
    /// Soundness guard: theory returned an empty conflict explanation.
    EmptyTheoryConflict,
    /// Extension reported `ExtCheckResult::Unknown`.
    ExtensionUnknown,
    /// Propagated from assumption-based solving (`AssumeResult::Unknown`).
    AssumptionUnknown,
    /// SAT model reconstruction/verification produced an invalid model.
    InvalidSatModel,
    /// UNSAT proof finalization failed after the solver derived UNSAT.
    ProofFinalizationFailure,
    /// Deterministic conflict budget (`:rlimit`) was exhausted before a
    /// definitive result. Distinct from `Interrupted` (wall-clock/flag) so
    /// callers and diagnostics can tell a reproducible resource-out apart
    /// from a timing-dependent one.
    ResourceBudget,
    /// A clause exceeding the arena's 16-bit length field (`> u16::MAX`
    /// literals) was added and stored truncated (a sound strengthening). SAT
    /// models stay valid for the original formula, but an UNSAT verdict is not
    /// trustworthy, so the solve reports `unknown` instead. See
    /// `ClauseArena::add`.
    ClauseTooLarge,
    /// Fallback for legacy/unspecified unknown paths.
    Unspecified,
}

impl SatUnknownReason {
    /// Stable diagnostic label emitted in SAT diagnostic traces.
    #[inline]
    pub const fn diagnostic_label(self) -> &'static str {
        match self {
            Self::Interrupted => "interrupted",
            Self::TheoryStop => "theory_stop",
            Self::UnsupportedConfig => "unsupported_config",
            Self::EmptyTheoryConflict => "empty_theory_conflict",
            Self::ExtensionUnknown => "extension_unknown",
            Self::AssumptionUnknown => "assumption_unknown",
            Self::InvalidSatModel => "invalid_sat_model",
            Self::ProofFinalizationFailure => "proof_finalization_failure",
            Self::ResourceBudget => "resource_budget",
            Self::ClauseTooLarge => "clause_too_large",
            Self::Unspecified => "unspecified",
        }
    }
}

/// Result from theory propagation callback (used with solve_with_theory)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum TheoryPropResult {
    /// Continue solving (no new clauses added)
    Continue,
    /// Theory added clause(s), re-propagate
    Propagate,
    /// Theory detected conflict, add this clause
    Conflict(Vec<Literal>),
    /// Stop solving, return unknown
    Stop,
}

/// Clause ordering policy before watch attachment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WatchOrderPolicy {
    /// Keep caller-provided literal order.
    Preserve,
    /// Prefer unassigned/high-score literals for watch positions.
    AssignmentScore,
    /// Keep 1UIP in position 0 and move max non-UIP level to position 1.
    LearnedBacktrack,
}

/// Result of solving with assumptions, including unsat core
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "SAT results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum AssumeResult {
    /// Satisfiable with model
    Sat(Vec<bool>),
    /// Unsatisfiable with core (subset of assumptions that caused UNSAT)
    /// and an optional proof certificate for proof-based UNSAT core extraction.
    ///
    /// The `Option<ProofCertificate>` is `Some` when LRAT proof output is enabled.
    /// Consumers can use [`ProofCertificate::minimal_core()`] to extract a
    /// proof-minimal set of original clause IDs that participated in the
    /// derivation of unsatisfiability.
    Unsat(Vec<Literal>, Option<ProofCertificate>),
    /// Unknown (timeout, etc.)
    Unknown,
}

impl PartialEq for AssumeResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sat(a), Self::Sat(b)) => a == b,
            (Self::Unsat(a, _), Self::Unsat(b, _)) => a == b,
            (Self::Unknown, Self::Unknown) => true,
            _ => false,
        }
    }
}

impl Eq for AssumeResult {}

impl AssumeResult {
    /// Returns true if the result is Sat.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    /// Returns true if the result is Unsat.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat(..))
    }

    /// Returns true if the result is Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Returns the proof certificate if the result is Unsat and a certificate
    /// is available.
    #[inline]
    pub fn proof_certificate(&self) -> Option<&ProofCertificate> {
        match self {
            Self::Unsat(_, Some(cert)) => Some(cert),
            _ => None,
        }
    }
}

/// Verified wrapper around [`SatResult`].
///
/// Guarantees that the enclosed result was produced by the SAT solver's
/// validated pipeline (through `finalize_sat_model` for SAT outcomes).
/// Can only be constructed within the `ay-sat` crate via `from_validated`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct VerifiedSatResult {
    result: SatResult,
}

impl VerifiedSatResult {
    /// Construct from a validated SAT result. Only callable within ay-sat.
    #[inline]
    pub(crate) fn from_validated(result: SatResult) -> Self {
        Self { result }
    }

    /// Extract the inner `SatResult` for pattern matching.
    #[inline]
    pub fn result(&self) -> &SatResult {
        &self.result
    }

    /// Consume and return the inner `SatResult`.
    ///
    /// **Trust boundary:** The returned `SatResult` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// `finalize_sat_model`). Prefer using [`.result()`](Self::result) to borrow
    /// or [`.is_sat()`](Self::is_sat) / [`.is_unsat()`](Self::is_unsat) to query
    /// without stripping the verification wrapper.
    #[inline]
    pub fn into_inner(self) -> SatResult {
        self.result
    }

    /// Returns `true` if the result is `Sat`.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self.result, SatResult::Sat(_))
    }

    /// Returns `true` if the result is `Unsat`.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self.result, SatResult::Unsat(_))
    }

    /// Returns `true` if the result is `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self.result, SatResult::Unknown)
    }

    /// Borrow the model if the result is `Sat`.
    ///
    /// Returns `None` for `Unsat` or `Unknown` results.
    /// Preserves the verified wrapper (no trust boundary crossing).
    #[inline]
    pub fn model(&self) -> Option<&[bool]> {
        match &self.result {
            SatResult::Sat(model) => Some(model),
            _ => None,
        }
    }

    /// Consume and return the model if the result is `Sat`.
    ///
    /// Returns `None` for `Unsat` or `Unknown` results.
    /// Prefer [`model()`](Self::model) when a borrow suffices.
    #[inline]
    pub fn into_model(self) -> Option<Vec<bool>> {
        match self.result {
            SatResult::Sat(model) => Some(model),
            _ => None,
        }
    }
}

impl PartialEq<SatResult> for VerifiedSatResult {
    fn eq(&self, other: &SatResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<VerifiedSatResult> for SatResult {
    fn eq(&self, other: &VerifiedSatResult) -> bool {
        *self == other.result
    }
}

impl std::fmt::Display for VerifiedSatResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.result {
            SatResult::Sat(model) => write!(f, "sat (model size: {})", model.len()),
            SatResult::Unsat(_) => write!(f, "unsat"),
            SatResult::Unknown => write!(f, "unknown"),
        }
    }
}

/// Verified wrapper around [`AssumeResult`].
///
/// Guarantees that the enclosed result was produced by the SAT solver's
/// validated assumption-solving pipeline. Can only be constructed within
/// the `ay-sat` crate via `from_validated`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct VerifiedAssumeResult {
    result: AssumeResult,
}

impl VerifiedAssumeResult {
    /// Construct from a validated assumption result. Only callable within ay-sat.
    #[inline]
    pub(crate) fn from_validated(result: AssumeResult) -> Self {
        Self { result }
    }

    /// Extract the inner `AssumeResult` for pattern matching.
    #[inline]
    pub fn result(&self) -> &AssumeResult {
        &self.result
    }

    /// Consume and return the inner `AssumeResult`.
    ///
    /// **Trust boundary:** The returned `AssumeResult` carries no compile-time
    /// proof of verification. Verification happened at construction time.
    /// Prefer using [`.result()`](Self::result) to borrow or
    /// [`.is_sat()`](Self::is_sat) / [`.is_unsat()`](Self::is_unsat) to query
    /// without stripping the verification wrapper.
    #[inline]
    pub fn into_inner(self) -> AssumeResult {
        self.result
    }

    /// Returns `true` if the result is `Sat`.
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self.result, AssumeResult::Sat(_))
    }

    /// Returns `true` if the result is `Unsat`.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self.result, AssumeResult::Unsat(..))
    }

    /// Returns `true` if the result is `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self.result, AssumeResult::Unknown)
    }

    /// Borrow the model if the result is `Sat`.
    ///
    /// Returns `None` for `Unsat` or `Unknown` results.
    /// Preserves the verified wrapper (no trust boundary crossing).
    #[inline]
    pub fn model(&self) -> Option<&[bool]> {
        match &self.result {
            AssumeResult::Sat(model) => Some(model),
            _ => None,
        }
    }

    /// Consume and return the model if the result is `Sat`.
    ///
    /// Returns `None` for `Unsat` or `Unknown` results.
    /// Prefer [`model()`](Self::model) when a borrow suffices.
    #[inline]
    pub fn into_model(self) -> Option<Vec<bool>> {
        match self.result {
            AssumeResult::Sat(model) => Some(model),
            _ => None,
        }
    }

    /// Borrow the unsat core if the result is `Unsat`.
    ///
    /// The core is a subset of assumptions that caused unsatisfiability.
    /// Returns `None` for `Sat` or `Unknown` results.
    #[inline]
    pub fn unsat_core(&self) -> Option<&[Literal]> {
        match &self.result {
            AssumeResult::Unsat(core, _) => Some(core),
            _ => None,
        }
    }

    /// Consume and return the unsat core if the result is `Unsat`.
    ///
    /// Returns `None` for `Sat` or `Unknown` results.
    /// Prefer [`unsat_core()`](Self::unsat_core) when a borrow suffices.
    #[inline]
    pub fn into_unsat_core(self) -> Option<Vec<Literal>> {
        match self.result {
            AssumeResult::Unsat(core, _) => Some(core),
            _ => None,
        }
    }

    /// Borrow the proof certificate if the result is `Unsat` and a certificate
    /// is available.
    ///
    /// Returns `None` for `Sat`, `Unknown`, or `Unsat` without proof output.
    #[inline]
    pub fn proof_certificate(&self) -> Option<&ProofCertificate> {
        match &self.result {
            AssumeResult::Unsat(_, Some(cert)) => Some(cert),
            _ => None,
        }
    }

    /// Compute the proof-minimal UNSAT core mapped back to assumption literals.
    ///
    /// Uses the LRAT proof certificate to find the minimal set of original
    /// clause IDs that participated in the proof, then maps those clause IDs
    /// back to the assumptions that introduced them. This produces a tighter
    /// core than the implication-graph-based core.
    ///
    /// Returns `None` if no proof certificate is available.
    ///
    /// # Arguments
    ///
    /// * `assumption_clause_ids` - Maps each assumption literal to its clause ID
    ///   in the solver's clause database (the unit clause added for that assumption).
    #[inline]
    pub fn assumption_minimal_core(
        &self,
        assumption_clause_ids: &[(Literal, u64)],
    ) -> Option<Vec<Literal>> {
        let cert = self.proof_certificate()?;
        let core_ids = cert.minimal_core();
        if core_ids.is_empty() {
            return Some(Vec::new());
        }
        let core_id_set: crate::kani_compat::DetHashSet<u64> = core_ids.into_iter().collect();
        let minimal = assumption_clause_ids
            .iter()
            .filter(|(_, id)| core_id_set.contains(id))
            .map(|(lit, _)| *lit)
            .collect();
        Some(minimal)
    }
}

impl PartialEq<AssumeResult> for VerifiedAssumeResult {
    fn eq(&self, other: &AssumeResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<VerifiedAssumeResult> for AssumeResult {
    fn eq(&self, other: &VerifiedAssumeResult) -> bool {
        *self == other.result
    }
}

impl std::fmt::Display for VerifiedAssumeResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.result {
            AssumeResult::Sat(model) => write!(f, "sat (model size: {})", model.len()),
            AssumeResult::Unsat(core, cert) => {
                write!(f, "unsat (core size: {}", core.len())?;
                if cert.is_some() {
                    write!(f, ", proof available")?;
                }
                write!(f, ")")
            }
            AssumeResult::Unknown => write!(f, "unknown"),
        }
    }
}

// Packed per-variable flags: minimize (bits 0-3) + LRAT (bits 4-5) in a single u8 (#5089).
// Replaces 4 separate Vec<bool> for minimize + 2 Vec<bool> for LRAT (6 bytes/var → 1 byte/var).
pub(crate) const MIN_POISON: u8 = 0x01;
pub(crate) const MIN_REMOVABLE: u8 = 0x02;
pub(crate) const MIN_VISITED: u8 = 0x04;
pub(crate) const MIN_KEEP: u8 = 0x08;
pub(crate) const LRAT_A: u8 = 0x10; // LRAT work array A: needed/in_final
pub(crate) const LRAT_B: u8 = 0x20; // LRAT work array B: visited (DFS)
