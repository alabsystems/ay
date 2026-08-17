// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-memory clause trace for SMT proof reconstruction
//!
//! ## Arena storage (#A3)
//!
//! Entries are stored as `(offset, len)` spans into two shared pools (one for
//! literals, one for resolution hints) instead of one heap allocation pair per
//! entry. The hot add path has only amortized pool growth, and replay walks
//! two contiguous arrays. [`ClauseTraceEntryRef`] exposes the owned entry's
//! field shape without copying; [`ClauseTrace::entries_snapshot`] is the
//! explicit owned-snapshot compatibility path.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::cell::Cell;
use std::sync::OnceLock;

use crate::literal::Literal;

/// An owned clause addition entry.
///
/// Borrowing consumers use [`ClauseTraceEntryRef`]; this type is the retained
/// snapshot compatibility path.
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

/// Borrowed view of one trace entry, resolving its spans into shared pools.
#[derive(Debug, Clone, Copy)]
pub struct ClauseTraceEntryRef<'a> {
    /// Stable clause ID (matches `clause_ids` in solver)
    pub id: u64,
    /// The clause literals
    pub clause: &'a [Literal],
    /// True if this is an original (input) clause, false if learned
    pub is_original: bool,
    /// Resolution hints (clause IDs) used to derive this clause.
    pub resolution_hints: &'a [u64],
}

impl ClauseTraceEntryRef<'_> {
    /// Owned snapshot of this entry.
    #[must_use]
    pub fn to_entry(&self) -> ClauseTraceEntry {
        ClauseTraceEntry::new(
            self.id,
            self.clause.to_vec(),
            self.is_original,
            self.resolution_hints.to_vec(),
        )
    }
}

/// Internal per-entry `u32` spans; insertion fails closed on overflow.
#[derive(Debug, Clone, Copy)]
struct EntryMeta {
    id: u64,
    clause_off: u32,
    clause_len: u32,
    hints_off: u32,
    hints_len: u32,
    is_original: bool,
}

/// Default 256 MB budget, accounting exact retained arena capacities.
const DEFAULT_BUDGET_BYTES: usize = 256 * 1024 * 1024;

/// Cached `--sat-probe-trace-dup` probe (#A3): the environment is scanned once
/// per process instead of once per clause addition in the conflict hot loop.
fn probe_trace_dup_enabled() -> bool {
    static PROBE: OnceLock<bool> = OnceLock::new();
    *PROBE.get_or_init(|| ay_core::misc_cli_flags().probe_trace_dup)
}

/// Why a level-0 minimize-chain hint could not be recorded.
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

/// Solver-minted `(variable count, active scope premises)` authority.
type SolverProvenance = (usize, Vec<Literal>);

/// In-memory clause trace for proof reconstruction
///
/// Records all clause additions in order, enabling the SMT layer to emit
/// structured resolution DAG steps.
///
/// ## Memory budget (#6553)
///
/// The trace enforces a memory budget (default 256 MB). When the budget
/// is exceeded, new clause entries are dropped and `is_truncated` is set.
/// Admission reserves and checks all backing-vector capacities before any
/// live arena contents are changed.
/// An empty clause always sets the allocation-free UNSAT marker, even when its
/// entry/payload cannot be admitted.
/// The consumer (`SatProofManager::process_trace`) handles incomplete traces
/// via trust-lemma fallback, so truncation degrades proof quality without
/// affecting solver correctness.
#[derive(Debug, Clone)]
pub struct ClauseTrace {
    /// Per-entry metadata (id, flags, pool spans) in addition order.
    meta: Vec<EntryMeta>,
    /// Shared literal pool; every entry's clause is a contiguous span here.
    lit_pool: Vec<Literal>,
    /// Shared hint pool; every entry's hints are a contiguous span here.
    hint_pool: Vec<u64>,
    /// True if the empty clause was derived (UNSAT proven)
    has_empty: bool,
    /// Maximum allowed memory usage in bytes
    budget_bytes: usize,
    /// True if entries were dropped due to budget exhaustion
    is_truncated: bool,
    /// True if search-time proof bookkeeping exhausted its work budget (#A2b)
    proof_work_exhausted: bool,
    /// Why level-0 minimize-chain hints were dropped (introspection).
    hint_omissions: HintOmissionCounters,
    /// Namespace and active-scope authority; mutators clear the whole value.
    solver_num_vars: Option<SolverProvenance>,
}

impl Default for ClauseTrace {
    fn default() -> Self {
        Self::new()
    }
}

#[path = "clause_trace_arena.rs"]
mod arena;
#[path = "clause_trace_capacity.rs"]
mod capacity;

/// Borrowed, indexable view of all trace entries.
///
/// Obtained from [`ClauseTrace::entries`]. Supports `len`/`is_empty`/`get`/
/// `first`/`last` and iteration (`iter()`, or `for entry in trace.entries()`),
/// yielding [`ClauseTraceEntryRef`] items.
#[derive(Debug, Clone, Copy)]
pub struct TraceEntries<'a> {
    meta: &'a [EntryMeta],
    lit_pool: &'a [Literal],
    hint_pool: &'a [u64],
}

impl<'a> TraceEntries<'a> {
    fn view(&self, meta: &EntryMeta) -> ClauseTraceEntryRef<'a> {
        let clause_start = meta.clause_off as usize;
        let clause_end = clause_start + meta.clause_len as usize;
        let hints_start = meta.hints_off as usize;
        let hints_end = hints_start + meta.hints_len as usize;
        ClauseTraceEntryRef {
            id: meta.id,
            clause: &self.lit_pool[clause_start..clause_end],
            is_original: meta.is_original,
            resolution_hints: &self.hint_pool[hints_start..hints_end],
        }
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.meta.len()
    }

    /// True when there are no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.meta.is_empty()
    }

    /// Entry at `index`, if present.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<ClauseTraceEntryRef<'a>> {
        self.meta.get(index).map(|meta| self.view(meta))
    }

    /// Entry at `index`; panics when out of bounds (slice-indexing analog).
    #[must_use]
    pub fn at(&self, index: usize) -> ClauseTraceEntryRef<'a> {
        self.get(index)
            .unwrap_or_else(|| panic!("trace entry index {index} out of bounds"))
    }

    /// First entry, if any.
    #[must_use]
    pub fn first(&self) -> Option<ClauseTraceEntryRef<'a>> {
        self.get(0)
    }

    /// Last entry, if any.
    #[must_use]
    pub fn last(&self) -> Option<ClauseTraceEntryRef<'a>> {
        self.meta.last().map(|meta| self.view(meta))
    }

    /// Iterator over all entries in addition order.
    #[must_use]
    pub fn iter(&self) -> TraceEntriesIter<'a> {
        TraceEntriesIter {
            entries: *self,
            index: 0,
        }
    }
}

impl<'a> IntoIterator for TraceEntries<'a> {
    type Item = ClauseTraceEntryRef<'a>;
    type IntoIter = TraceEntriesIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &TraceEntries<'a> {
    type Item = ClauseTraceEntryRef<'a>;
    type IntoIter = TraceEntriesIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over [`TraceEntries`].
#[derive(Debug, Clone)]
pub struct TraceEntriesIter<'a> {
    entries: TraceEntries<'a>,
    index: usize,
}

impl<'a> Iterator for TraceEntriesIter<'a> {
    type Item = ClauseTraceEntryRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.entries.get(self.index)?;
        self.index += 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.entries.len().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for TraceEntriesIter<'_> {}

impl ClauseTrace {
    /// Allocated capacity of the solver-minted scope-premise snapshot.
    pub(crate) fn scope_assumptions_capacity(&self) -> usize {
        self.solver_num_vars
            .as_ref()
            .map_or(0, |provenance| provenance.1.capacity())
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

    /// Get all trace entries as a borrowed, iterable view.
    pub fn entries(&self) -> TraceEntries<'_> {
        TraceEntries {
            meta: &self.meta,
            lit_pool: &self.lit_pool,
            hint_pool: &self.hint_pool,
        }
    }

    /// Materialize all trace entries as owned snapshots.
    ///
    /// This is the allocation-explicit compatibility path for pre-A3 callers
    /// that consumed the owned `&[ClauseTraceEntry]` returned by `entries()`.
    /// Borrowing consumers should prefer [`Self::entries`].
    #[must_use]
    pub fn entries_snapshot(&self) -> Vec<ClauseTraceEntry> {
        self.entries()
            .iter()
            .map(|entry| entry.to_entry())
            .collect()
    }

    /// Number of entries in the trace.
    pub fn len(&self) -> usize {
        self.meta.len()
    }

    /// Check if trace is empty.
    pub fn is_empty(&self) -> bool {
        self.meta.is_empty()
    }

    /// Get original clauses only.
    pub fn original_clauses(&self) -> impl Iterator<Item = ClauseTraceEntryRef<'_>> {
        self.entries().iter().filter(|e| e.is_original)
    }

    /// Get learned clauses only.
    pub fn learned_clauses(&self) -> impl Iterator<Item = ClauseTraceEntryRef<'_>> {
        self.entries().iter().filter(|e| !e.is_original)
    }

    /// Exact SAT variable namespace captured by the solver that produced this
    /// immutable trace snapshot.
    ///
    /// `None` means the trace is live, manually constructed, or was mutated
    /// after extraction and therefore cannot authorize proof publication.
    #[must_use]
    pub fn solver_num_vars(&self) -> Option<usize> {
        self.solver_num_vars.as_ref().map(|provenance| provenance.0)
    }

    /// Solver-minted unit premises that activate the live incremental scopes
    /// represented by this immutable trace snapshot.
    ///
    /// `None` means the trace is live, manually constructed, or was mutated
    /// after extraction. `Some(&[])` is an authoritative base-scope snapshot.
    #[must_use]
    pub fn scope_assumptions(&self) -> Option<&[Literal]> {
        self.solver_num_vars
            .as_ref()
            .map(|provenance| provenance.1.as_slice())
    }

    /// Bind a freshly extracted immutable snapshot to its owning solver's
    /// exact variable namespace. Only solver extraction code may mint this
    /// provenance.
    #[cfg(test)]
    pub(crate) fn stamp_solver_num_vars(&mut self, solver_num_vars: usize) {
        self.solver_num_vars = Some((solver_num_vars, Vec::new()));
    }

    /// Atomically seal namespace and active-scope authority at extraction.
    pub(crate) fn stamp_solver_provenance(
        &mut self,
        solver_num_vars: usize,
        scope_assumptions: &[Literal],
    ) {
        self.solver_num_vars = Some((solver_num_vars, scope_assumptions.to_vec()));
    }
}

#[cfg(test)]
#[path = "clause_trace_tests.rs"]
mod tests;
