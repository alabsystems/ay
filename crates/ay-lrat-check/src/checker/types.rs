// Copyright 2026 Andrew Yates
// Shared types for the LRAT checker.
//
// Extracted from checker/mod.rs for the 500-line limit (#5267).

use crate::dimacs::Literal;
#[cfg(test)]
use ay_core::kani_compat::DetHashSet as HashSet;
use thiserror::Error;

/// Result of scanning a hint clause during RUP verification.
#[derive(Debug)]
pub(crate) enum HintAction {
    /// All literals falsified — conflict found (clause verified).
    Conflict,
    /// Exactly one literal unassigned — propagate it.
    Propagate(Literal),
    /// Exactly one non-falsified literal, but it's already satisfied (true).
    /// CaDiCaL lratchecker.cpp:370 does `checked_lit(unit) = true` which is a
    /// no-op when unit is already true. We mirror: skip without error.
    SatisfiedUnit,
    /// Multiple non-falsified literals — hint clause is not unit (#5233).
    /// CaDiCaL lratchecker.cpp:359-361 rejects this as a hard failure.
    NonUnit,
}

/// Index entry for a clause in the arena. Copyable to avoid borrow conflicts.
///
/// 16 bytes: `start` (4) + `len` (4) + `hint_gen` (4) + `tautological` (1) + padding (3).
/// CaDiCaL lratchecker.cpp stores per-clause `used` as a bool flag; we use a
/// generation counter to avoid O(n) clearing between derivation steps.
#[derive(Clone, Copy)]
pub(crate) struct ClauseEntry {
    /// Start offset in `clause_arena`.
    pub(crate) start: u32,
    /// Number of literals.
    pub(crate) len: u32,
    /// Generation stamp for duplicate hint detection. If `hint_gen` equals the
    /// checker's current `hint_generation`, this clause was already used as a
    /// hint in the current derivation step. Replaces `HashSet<u64> seen_hints`.
    /// CaDiCaL lratchecker.cpp:28 uses a per-clause `used` bool cleared per step.
    pub(crate) hint_gen: u32,
    /// Whether the clause is tautological (contains both `l` and `~l`).
    /// CaDiCaL lratchecker.cpp:28 uses a per-clause `tautological` flag.
    pub(crate) tautological: bool,
    /// Whether this clause was added as an original (not derived).
    /// Used by `delete()` to count only original-clause deletions toward
    /// finalization coverage. CaDiCaL lratchecker.cpp tracks this implicitly
    /// via `add_original_clause` vs `add_derived_clause`.
    pub(crate) original: bool,
}

/// Running statistics for the LRAT checker.
///
/// All fields are public for programmatic access by downstream consumers,
/// matching ay-drat-check's `Stats` API surface (#5319).
#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub originals: u64,
    pub derived: u64,
    pub deleted: u64,
    /// Deletions of original (not derived) clauses. Used by `conclude_unsat()`
    /// for finalization coverage: `finalized + deleted_originals == originals`.
    /// Without this, derived-clause deletions inflate the `deleted` counter,
    /// masking incomplete coverage of original clauses.
    pub deleted_originals: u64,
    /// Clauses weakened via `weaken()` (CaDiCaL `weaken_minus`).
    pub weakened: u64,
    /// Clauses restored via `restore()` (CaDiCaL `restore_clause`).
    pub restored: u64,
    pub failures: u64,
    /// Clauses verified via finalize_clause() — confirmed present and
    /// content-matched at proof end. CaDiCaL lratchecker.cpp:757-794.
    pub finalized: u64,
    /// Clauses verified via RUP check.
    pub rup_ok: u64,
    /// Clauses where resolution check matched after RUP success.
    pub resolution_ok: u64,
    /// Clauses where resolution check mismatched (advisory only).
    pub resolution_mismatch: u64,
    /// Clauses verified via RAT check.
    pub rat_ok: u64,
    /// Clauses verified via blocked clause (ER) check.
    pub blocked_ok: u64,
    /// Number of arena compaction operations performed (#8624).
    pub compactions: u64,
}

/// Proof conclusion status.
///
/// CaDiCaL lratchecker.cpp:569-811 validates proof conclusion with multiple
/// modes (CONFLICT, ASSUMPTIONS, CONSTRAINT). AY's LRAT checker currently
/// only supports CONFLICT (standard UNSAT proofs). ASSUMPTIONS and CONSTRAINT
/// are incremental-SAT features not yet needed.
///
/// The conclude step is the final validation after all proof steps have been
/// processed. It verifies an empty clause was derived and no step failures
/// occurred.
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
    /// One or more individual derivation steps failed during verification.
    #[error("one or more derivation steps failed")]
    StepFailures,
    /// No proof steps were processed at all.
    #[error("no proof steps were processed")]
    NoStepsProcessed,
    /// `conclude_unsat()` was called more than once.
    /// CaDiCaL lratchecker.cpp calls `fatal_message` on double conclusion.
    #[error("conclude_unsat() called more than once")]
    AlreadyConcluded,
    /// Finalization check failed: not all clauses were accounted for.
    /// `finalized + deleted_originals` does not equal `originals`.
    /// CaDiCaL lratchecker.cpp:797-811 `report_status()`.
    #[error("incomplete coverage: {finalized} finalized + {deleted_originals} deleted != {originals} originals")]
    IncompleteCoverage {
        /// Number of original clauses.
        originals: u64,
        /// Number of clauses finalized via `finalize_clause()`.
        finalized: u64,
        /// Number of original clauses deleted.
        deleted_originals: u64,
    },
}

/// Check whether a clause is tautological (contains both `l` and `~l`).
///
/// Reference implementation using `HashSet`. Used by tests to validate
/// `LratChecker::check_tautological()` which uses the `marks` array
/// instead (allocation-free, #5267).
#[cfg(test)]
pub(crate) fn is_tautological(clause: &[Literal]) -> bool {
    let mut seen: HashSet<Literal> = Default::default();
    for &lit in clause {
        if seen.contains(&lit.negated()) {
            return true;
        }
        seen.insert(lit);
    }
    false
}

/// Helper to build a literal from DIMACS notation.
#[cfg(test)]
pub(crate) fn lit(dimacs: i32) -> Literal {
    Literal::from_dimacs(dimacs)
}
