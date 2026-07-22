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
        }
    }

    /// Estimate the heap allocation size of a clause trace entry.
    fn estimate_entry_bytes(clause_len: usize, hints_len: usize) -> usize {
        // ClauseTraceEntry struct overhead (id + is_original + Vec headers)
        // plus heap allocations for clause and hints vectors.
        const ENTRY_OVERHEAD: usize = 64;
        ENTRY_OVERHEAD + clause_len * size_of::<Literal>() + hints_len * size_of::<u64>()
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
}

#[cfg(test)]
#[path = "clause_trace_tests.rs"]
mod tests;
