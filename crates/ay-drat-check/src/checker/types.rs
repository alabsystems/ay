// Copyright 2026 Andrew Yates
// Type definitions for the DRAT/DRUP proof checker.
// Extracted from mod.rs to keep production files under 500 lines.

use crate::literal::Literal;
use thiserror::Error;

/// Watch list entry for two-watched-literal propagation.
#[derive(Clone, Copy)]
pub(crate) struct Watch {
    pub(crate) blocking: Literal,
    pub(crate) clause_idx: usize,
    /// ACTIVE/core flag. Set by `mark_watches_core` when a clause is marked
    /// ACTIVE during backward checking. Used by the two-pass core-first BCP
    /// (drat-trim.c:206) to prioritize ACTIVE clauses during propagation.
    pub(crate) core: bool,
}

/// Result of visiting one watched clause during BCP.
pub(crate) enum Visit {
    KeepUpdate(Literal),
    Propagate(Literal, usize),
    Conflict(usize),
    Moved,
    Skip,
}

/// Statistics collected during proof checking.
#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub original: u64,
    pub additions: u64,
    pub deletions: u64,
    pub checks: u64,
    pub propagations: u64,
    pub failures: u64,
    pub missed_deletes: u64,
    pub rat_checks: u64,
    /// Number of literals removed by clause reduction during backward checking.
    /// Mirrors drat-trim's `nRemoved` counter.
    pub reduced_literals: u64,
    /// Number of deletion instructions silently ignored because the clause was
    /// the propagation reason for its first literal (pseudo-unit protection).
    /// drat-trim.c:806-814 — deleting a reason clause corrupts the BCP trail.
    pub pseudo_unit_skips: u64,
}

/// Result of proof conclusion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcludeResult {
    /// Proof verified: empty clause derived, no failures.
    Verified,
    /// Proof failed: reason provided.
    Failed(ConcludeFailure),
}

/// Reasons why proof conclusion failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum ConcludeFailure {
    /// No empty clause was derived in the proof.
    #[error("proof does not derive the empty clause")]
    NoEmptyClause,
    /// One or more derivation steps failed.
    #[error("one or more derivation steps failed")]
    StepFailures,
    /// No proof steps were processed.
    #[error("no proof steps were processed")]
    NoStepsProcessed,
}
