// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-memory clause trace for SMT proof reconstruction
//!
//! This module records SAT clause additions for use by the SMT layer when
//! reconstructing explicit Alethe `resolution` proof steps. Unlike DRAT/LRAT
//! file output, this keeps the trace in memory for direct consumption by
//! `SatProofManager`.
//!
//! The trace records clause additions (both original and learned) with stable
//! IDs, and tracks when the empty clause is derived.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::cell::Cell;
use std::mem::size_of;

use crate::literal::Literal;

/// A single clause addition entry in the trace
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ClauseTraceEntry {
    /// Stable clause ID (matches `clause_ids` in solver)
    pub id: u64,
    /// The clause literals
    pub clause: Vec<Literal>,
    /// True if this is an original (input) clause, false if learned
    pub is_original: bool,
    /// Resolution hints (clause IDs) used to derive this clause.
    ///
    /// Non-empty for learned clauses produced by conflict analysis.
    /// Uses `u64` (RUP-only); the LRAT format uses signed IDs where
    /// negatives mark RAT witness boundaries. See #5634.
    pub resolution_hints: Vec<u64>,
}

impl ClauseTraceEntry {
    /// Create a new clause trace entry.
    #[must_use]
    pub fn new(
        id: u64,
        clause: Vec<Literal>,
        is_original: bool,
        resolution_hints: Vec<u64>,
    ) -> Self {
        Self {
            id,
            clause,
            is_original,
            resolution_hints,
        }
    }
}

/// Default memory budget for clause trace: 256 MB.
///
/// Typical entry is ~224 bytes (64 byte overhead + 80 bytes literals +
/// 80 bytes hints for a 20-literal clause with 10 hints). At 256 MB,
/// this allows ~1.1M entries before truncation.
const DEFAULT_BUDGET_BYTES: usize = 256 * 1024 * 1024;

/// Why a level-0 minimize-chain hint could not be recorded.
///
/// A conflict-analysis literal whose reason cannot be named by a stable clause
/// ID contributes NO resolution hint, so downstream proof reconstruction cannot
/// resolve that literal away. The derived clause then keeps extra literals and
/// `SatProofManager` falls back to an unverifiable `trust` step. These counters
/// make that loss observable instead of silent.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct HintOmissionStats {
    /// Total level-0 minimize-chain hint lookups.
    pub queries: u64,
    /// Lookups that produced a usable clause ID.
    pub resolved: u64,
    /// Omitted: the variable's reason is not a clause reason at all.
    pub omitted_not_clause_reason: u64,
    /// Omitted: the reason is a lazy theory reason (a table index, not an
    /// arena offset — see #8467), so it has no stable clause ID.
    pub omitted_lazy_theory_reason: u64,
    /// Omitted: the reason is a clause but its stable ID is 0 (untracked).
    pub omitted_zero_clause_id: u64,
}

impl HintOmissionStats {
    /// Total omissions across all causes.
    #[must_use]
    pub fn omitted_total(&self) -> u64 {
        self.omitted_not_clause_reason
            .saturating_add(self.omitted_lazy_theory_reason)
            .saturating_add(self.omitted_zero_clause_id)
    }
}

/// Cause of a single hint omission, reported by the solver's lookup paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum HintOmission {
    /// The variable's reason is not a clause reason.
    NotClauseReason,
    /// The reason is a lazy theory reason (no stable clause ID).
    LazyTheoryReason,
    /// The reason is a clause whose stable ID is 0.
    ZeroClauseId,
}

/// Interior-mutable counters so the `&self` hint-lookup paths can record.
#[derive(Debug, Default)]
struct HintOmissionCounters {
    queries: Cell<u64>,
    resolved: Cell<u64>,
    not_clause_reason: Cell<u64>,
    lazy_theory_reason: Cell<u64>,
    zero_clause_id: Cell<u64>,
}

impl Clone for HintOmissionCounters {
    fn clone(&self) -> Self {
        Self {
            queries: Cell::new(self.queries.get()),
            resolved: Cell::new(self.resolved.get()),
            not_clause_reason: Cell::new(self.not_clause_reason.get()),
            lazy_theory_reason: Cell::new(self.lazy_theory_reason.get()),
            zero_clause_id: Cell::new(self.zero_clause_id.get()),
        }
    }
}

/// In-memory clause trace for proof reconstruction
///
/// Records all clause additions in order, enabling the SMT layer to emit
/// structured resolution DAG steps.
///
/// ## Memory budget (#6553)
///
/// The trace enforces a memory budget (default 256 MB). When the budget
/// is exceeded, new non-empty clause entries are silently dropped and
/// `is_truncated` is set. Empty clauses (UNSAT signal) are always recorded.
/// The consumer (`SatProofManager::process_trace`) handles incomplete traces
/// via trust-lemma fallback, so truncation degrades proof quality without
/// affecting solver correctness.
#[derive(Debug, Clone)]
pub struct ClauseTrace {
    /// All clause additions in order
    entries: Vec<ClauseTraceEntry>,
    /// True if the empty clause was derived (UNSAT proven)
    has_empty: bool,
    /// Estimated memory usage in bytes
    used_bytes: usize,
    /// Maximum allowed memory usage in bytes
    budget_bytes: usize,
    /// True if entries were dropped due to budget exhaustion
    is_truncated: bool,
    /// True if search-time proof bookkeeping exhausted its work budget (#A2b)
    proof_work_exhausted: bool,
    /// Why level-0 minimize-chain hints were dropped (introspection).
    hint_omissions: HintOmissionCounters,
    /// Authoritative SAT variable namespace captured by the owning solver at
    /// the exact extraction boundary.
    ///
    /// Live/manual traces carry `None`. The field is private and every public
    /// proof-content mutator clears it, so downstream proof composition cannot
    /// pair a mutated trace with stale namespace authority.
    solver_num_vars: Option<usize>,
}

impl Default for ClauseTrace {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseTrace {
    /// Create a new empty clause trace with the default memory budget.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            has_empty: false,
            used_bytes: 0,
            budget_bytes: DEFAULT_BUDGET_BYTES,
            is_truncated: false,
            proof_work_exhausted: false,
            hint_omissions: HintOmissionCounters::default(),
            solver_num_vars: None,
        }
    }

    /// Create a new trace with pre-allocated capacity and the default budget.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
            has_empty: false,
            used_bytes: 0,
            budget_bytes: DEFAULT_BUDGET_BYTES,
            is_truncated: false,
            proof_work_exhausted: false,
            hint_omissions: HintOmissionCounters::default(),
            solver_num_vars: None,
        }
    }

    /// Estimate the heap allocation size of a clause trace entry.
    fn estimate_entry_bytes(clause_len: usize, hints_len: usize) -> usize {
        // ClauseTraceEntry struct overhead (id + is_original + Vec headers)
        // plus heap allocations for clause and hints vectors.
        const ENTRY_OVERHEAD: usize = 64;
        ENTRY_OVERHEAD + clause_len * size_of::<Literal>() + hints_len * size_of::<u64>()
    }

    /// Allocated slots in the outer entry vector.
    ///
    /// The bounded independent-replay path combines this with every entry's
    /// public clause/hint capacity.  `used_bytes()` is intentionally only the
    /// trace writer's len-based admission estimate, so it cannot serve as an
    /// exact retained-capacity census for certificate validation.
    pub(crate) fn entries_capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Record the outcome of a level-0 minimize-chain hint lookup.
    ///
    /// Takes `&self` because the solver's lookup paths are `&self`; the
    /// counters are `Cell`-based and the solver instance is single-threaded.
    pub fn record_hint_lookup(&self, omission: Option<HintOmission>) {
        self.hint_omissions
            .queries
            .set(self.hint_omissions.queries.get().saturating_add(1));
        let counter = match omission {
            None => &self.hint_omissions.resolved,
            Some(HintOmission::NotClauseReason) => &self.hint_omissions.not_clause_reason,
            Some(HintOmission::LazyTheoryReason) => &self.hint_omissions.lazy_theory_reason,
            Some(HintOmission::ZeroClauseId) => &self.hint_omissions.zero_clause_id,
        };
        counter.set(counter.get().saturating_add(1));
    }

    /// Snapshot of why level-0 minimize-chain hints were dropped.
    ///
    /// A non-zero `omitted_total()` is the direct cause of `FinalClauseMismatch`
    /// during proof reconstruction: the unhinted literals cannot be resolved
    /// away, so the derived clause is a strict superclause of its target.
    #[must_use]
    pub fn hint_omission_stats(&self) -> HintOmissionStats {
        HintOmissionStats {
            queries: self.hint_omissions.queries.get(),
            resolved: self.hint_omissions.resolved.get(),
            omitted_not_clause_reason: self.hint_omissions.not_clause_reason.get(),
            omitted_lazy_theory_reason: self.hint_omissions.lazy_theory_reason.get(),
            omitted_zero_clause_id: self.hint_omissions.zero_clause_id.get(),
        }
    }

    /// Record a clause addition.
    pub fn add_clause(&mut self, id: u64, clause: Vec<Literal>, is_original: bool) {
        self.add_clause_with_hints(id, clause, is_original, Vec::new());
    }

    /// Record a clause addition with explicit resolution hints.
    ///
    /// Empty clauses are always recorded (they signal UNSAT). Non-empty
    /// clauses are silently dropped when the memory budget is exceeded.
    pub fn add_clause_with_hints(
        &mut self,
        id: u64,
        clause: Vec<Literal>,
        is_original: bool,
        resolution_hints: Vec<u64>,
    ) {
        self.solver_num_vars = None;
        let entry_bytes = Self::estimate_entry_bytes(clause.len(), resolution_hints.len());

        if clause.is_empty() {
            self.has_empty = true;
        } else if self.used_bytes + entry_bytes > self.budget_bytes {
            // Budget exceeded: drop this entry silently.
            // Empty clauses bypass this check (UNSAT signal must not be lost).
            if !self.is_truncated {
                self.is_truncated = true;
                tracing::warn!(
                    used_bytes = self.used_bytes,
                    budget_bytes = self.budget_bytes,
                    entries = self.entries.len(),
                    "clause trace memory budget exceeded — further entries will be dropped"
                );
            }
            return;
        }

        self.used_bytes += entry_bytes;
        self.entries.push(ClauseTraceEntry {
            id,
            clause,
            is_original,
            resolution_hints,
        });
    }

    /// Update the resolution hints for an existing clause entry.
    ///
    /// Prefer `add_clause_with_hints` for new code — it attaches hints
    /// atomically at insertion time, preventing hint-loss regressions (#4435).
    /// This method is retained for LRAT ID resync edge cases and tests.
    ///
    /// Returns `true` if the clause ID was found and updated. Logs a warning
    /// in release builds when the ID is missing, so proof-DAG edge drops are
    /// never completely silent.
    pub fn set_resolution_hints(&mut self, id: u64, resolution_hints: Vec<u64>) -> bool {
        self.solver_num_vars = None;
        // Search from the end: the target clause was almost always just appended,
        // making the common case O(1) instead of O(n). Over C total conflicts,
        // this turns the aggregate cost from O(C^2) to O(C).
        if let Some(entry) = self.entries.iter_mut().rfind(|entry| entry.id == id) {
            // Adjust used_bytes for the hint size change.
            let old_bytes = entry.resolution_hints.len() * size_of::<u64>();
            let new_bytes = resolution_hints.len() * size_of::<u64>();
            self.used_bytes = self
                .used_bytes
                .wrapping_sub(old_bytes)
                .wrapping_add(new_bytes);
            entry.resolution_hints = resolution_hints;
            true
        } else {
            tracing::warn!(
                clause_id = id,
                hint_count = resolution_hints.len(),
                "set_resolution_hints: clause ID not found — resolution DAG edge dropped"
            );
            false
        }
    }

    /// Record that the empty clause was derived.
    pub fn mark_empty(&mut self) {
        self.solver_num_vars = None;
        self.has_empty = true;
    }

    /// Check if the empty clause was derived.
    pub fn has_empty_clause(&self) -> bool {
        self.has_empty
    }

    /// True if entries were dropped due to memory budget exhaustion.
    pub fn is_truncated(&self) -> bool {
        self.is_truncated
    }

    /// Mark that search-time proof bookkeeping (level-0 LRAT unit
    /// materialization) exhausted its deterministic work budget (#A2b).
    /// The trace can no longer be reconstructed into a complete certificate;
    /// consumers must fail closed (no certificate, honest warning).
    pub fn mark_proof_work_exhausted(&mut self) {
        self.solver_num_vars = None;
        self.proof_work_exhausted = true;
    }

    /// True if the search-time proof bookkeeping work budget was exhausted.
    pub fn proof_work_exhausted(&self) -> bool {
        self.proof_work_exhausted
    }

    /// Drop all recorded entries (reclaims memory after #A2b budget
    /// exhaustion). The `proof_work_exhausted` / `has_empty` markers are
    /// kept so consumers still see the honest degrade signal.
    pub fn clear_entries(&mut self) {
        self.solver_num_vars = None;
        self.entries = Vec::new();
        self.used_bytes = 0;
    }

    /// Estimated memory usage in bytes.
    pub fn used_bytes(&self) -> usize {
        self.used_bytes
    }

    /// Get all trace entries.
    pub fn entries(&self) -> &[ClauseTraceEntry] {
        &self.entries
    }

    /// Number of entries in the trace.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if trace is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get original clauses only.
    pub fn original_clauses(&self) -> impl Iterator<Item = &ClauseTraceEntry> {
        self.entries.iter().filter(|e| e.is_original)
    }

    /// Get learned clauses only.
    pub fn learned_clauses(&self) -> impl Iterator<Item = &ClauseTraceEntry> {
        self.entries.iter().filter(|e| !e.is_original)
    }

    /// Exact SAT variable namespace captured by the solver that produced this
    /// immutable trace snapshot.
    ///
    /// `None` means the trace is live, manually constructed, or was mutated
    /// after extraction and therefore cannot authorize proof publication.
    #[must_use]
    pub fn solver_num_vars(&self) -> Option<usize> {
        self.solver_num_vars
    }

    /// Bind a freshly extracted immutable snapshot to its owning solver's
    /// exact variable namespace. Only solver extraction code may mint this
    /// provenance.
    pub(crate) fn stamp_solver_num_vars(&mut self, solver_num_vars: usize) {
        self.solver_num_vars = Some(solver_num_vars);
    }
}

#[cfg(test)]
#[path = "clause_trace_tests.rs"]
mod tests;
