// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public result enums and supporting SAT-solver types.

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
    /// Backward reconstruction already ran during UNSAT finalization; public
    /// proof-step conversion waits for [`ProofCertificate::materialize()`].
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
    /// The caller-supplied whole-solve wall-clock deadline expired.
    DeadlineExceeded,
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
    /// Soundness guard (`#core-subset-audit`): an assumption-path UNSAT core
    /// contained a literal that is not an assumption of this query, so the
    /// returned core is not a certified unsatisfiable subset. The UNSAT-side
    /// counterpart of [`Self::InvalidSatModel`].
    InvalidUnsatCore,
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
            Self::DeadlineExceeded => "deadline_exceeded",
            Self::TheoryStop => "theory_stop",
            Self::UnsupportedConfig => "unsupported_config",
            Self::EmptyTheoryConflict => "empty_theory_conflict",
            Self::ExtensionUnknown => "extension_unknown",
            Self::AssumptionUnknown => "assumption_unknown",
            Self::InvalidSatModel => "invalid_sat_model",
            Self::InvalidUnsatCore => "invalid_unsat_core",
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
    /// Unsatisfiable with a solver-derived assumption core and optional proof
    /// reconstruction data.
    ///
    /// The `Option<ProofCertificate>` may be `Some` when LRAT proof output is
    /// enabled; early UNSAT paths can carry `None`. Consumers can use
    /// [`ProofCertificate::tracked_original_clause_ids()`] to inspect the
    /// producer's over-approximate original-clause support. That support is not
    /// a checked or minimal UNSAT core.
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

// Packed per-variable flags: minimize (bits 0-3) + LRAT (bits 4-5) in a single u8 (#5089).
// Replaces 4 separate Vec<bool> for minimize + 2 Vec<bool> for LRAT (6 bytes/var → 1 byte/var).
pub(crate) const MIN_POISON: u8 = 0x01;
pub(crate) const MIN_REMOVABLE: u8 = 0x02;
pub(crate) const MIN_VISITED: u8 = 0x04;
pub(crate) const MIN_KEEP: u8 = 0x08;
pub(crate) const LRAT_A: u8 = 0x10; // LRAT work array A: needed/in_final
pub(crate) const LRAT_B: u8 = 0x20; // LRAT work array B: visited (DFS)
