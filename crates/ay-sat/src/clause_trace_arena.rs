// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capacity-bounded arena storage for [`ClauseTrace`].

use std::mem::size_of;

use super::{
    capacity::ArenaCapacities, probe_trace_dup_enabled, ClauseTrace, EntryMeta,
    HintOmissionCounters, DEFAULT_BUDGET_BYTES,
};
use crate::literal::Literal;

fn reserve_replacement<T>(source_len: usize, target_capacity: usize) -> Option<Vec<T>> {
    if target_capacity < source_len {
        return None;
    }
    let mut replacement = Vec::new();
    replacement.try_reserve_exact(target_capacity).ok()?;
    Some(replacement)
}

fn replacement_capacities(
    meta: &Option<Vec<EntryMeta>>,
    literals: &Option<Vec<Literal>>,
    hints: &Option<Vec<u64>>,
) -> ArenaCapacities {
    ArenaCapacities {
        entries: meta.as_ref().map_or(0, Vec::capacity),
        literals: literals.as_ref().map_or(0, Vec::capacity),
        hints: hints.as_ref().map_or(0, Vec::capacity),
    }
}

type ArenaReplacements = (
    Option<Vec<EntryMeta>>,
    Option<Vec<Literal>>,
    Option<Vec<u64>>,
);

fn reserve_replacements(
    trace: &ClauseTrace,
    current: ArenaCapacities,
    target: ArenaCapacities,
) -> Option<ArenaReplacements> {
    let meta = if target.entries == current.entries {
        None
    } else {
        Some(reserve_replacement(trace.meta.len(), target.entries)?)
    };
    if !replacement_peak_fits(trace, current, &meta, &None, &None) {
        return None;
    }
    let literals = if target.literals == current.literals {
        None
    } else {
        Some(reserve_replacement(trace.lit_pool.len(), target.literals)?)
    };
    if !replacement_peak_fits(trace, current, &meta, &literals, &None) {
        return None;
    }
    let hints = if target.hints == current.hints {
        None
    } else {
        Some(reserve_replacement(trace.hint_pool.len(), target.hints)?)
    };
    replacement_peak_fits(trace, current, &meta, &literals, &hints)
        .then_some((meta, literals, hints))
}

fn replacement_peak_fits(
    trace: &ClauseTrace,
    current: ArenaCapacities,
    meta: &Option<Vec<EntryMeta>>,
    literals: &Option<Vec<Literal>>,
    hints: &Option<Vec<u64>>,
) -> bool {
    current
        .peak_with_replacements(replacement_capacities(meta, literals, hints))
        .is_some_and(|peak| peak <= trace.budget_bytes)
}

impl ClauseTrace {
    /// Create a new empty clause trace with the default memory budget.
    pub fn new() -> Self {
        Self {
            meta: Vec::new(),
            lit_pool: Vec::new(),
            hint_pool: Vec::new(),
            has_empty: false,
            budget_bytes: DEFAULT_BUDGET_BYTES,
            is_truncated: false,
            proof_work_exhausted: false,
            hint_omissions: HintOmissionCounters::default(),
            solver_num_vars: None,
        }
    }

    /// Create a new trace with pre-allocated capacity and the default budget.
    /// Impossible requests return an allocation-free truncated trace.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut trace = Self::new();
        if capacity == 0 {
            return trace;
        }
        let requested = ArenaCapacities {
            entries: capacity,
            literals: 0,
            hints: 0,
        };
        if requested
            .retained_bytes()
            .is_none_or(|bytes| bytes > trace.budget_bytes)
        {
            trace.mark_truncated();
            return trace;
        }
        let Some(meta) = reserve_replacement(0, capacity) else {
            trace.mark_truncated();
            return trace;
        };
        if meta
            .capacity()
            .checked_mul(size_of::<EntryMeta>())
            .is_none_or(|bytes| bytes > trace.budget_bytes)
        {
            trace.mark_truncated();
            return trace;
        }
        trace.meta = meta;
        trace
    }

    /// Mark this trace incomplete after a resource/accounting failure.
    fn mark_truncated(&mut self) {
        self.is_truncated = true;
    }

    /// Allocated slots in the entry-metadata vector.
    ///
    /// Bounded replay combines this with the slot size and pool capacities.
    pub(crate) fn entries_capacity(&self) -> usize {
        self.meta.capacity()
    }

    /// Size of one entry-metadata slot in bytes.
    pub(crate) fn entry_slot_bytes() -> usize {
        size_of::<EntryMeta>()
    }

    /// Allocated capacity of the shared literal pool, in items.
    pub(crate) fn lit_pool_capacity(&self) -> usize {
        self.lit_pool.capacity()
    }

    /// Allocated capacity of the shared hint pool, in items.
    pub(crate) fn hint_pool_capacity(&self) -> usize {
        self.hint_pool.capacity()
    }

    /// Record a clause addition.
    pub fn add_clause(&mut self, id: u64, clause: Vec<Literal>, is_original: bool) {
        self.add_clause_with_hint_slices(id, &clause, is_original, &[]);
    }

    /// Whether any entry already carries this stable id.
    ///
    /// The trace ID space must remain injective: resolution conversion rejects
    /// an entire trace if two entries carry the same ID.
    pub fn contains_id(&self, id: u64) -> bool {
        self.meta.iter().any(|entry| entry.id == id)
    }

    /// Record a clause addition with explicit resolution hints.
    ///
    /// This owned-vector wrapper delegates to the slice API; hot paths should
    /// use [`Self::add_clause_with_hint_slices`] directly.
    pub fn add_clause_with_hints(
        &mut self,
        id: u64,
        clause: Vec<Literal>,
        is_original: bool,
        resolution_hints: Vec<u64>,
    ) {
        self.add_clause_with_hint_slices(id, &clause, is_original, &resolution_hints);
    }

    /// Record a clause addition with explicit resolution hints (slice API).
    ///
    /// Empty clauses always set the allocation-free UNSAT marker. An entry is
    /// dropped and the trace truncated if its retained capacities cannot fit.
    pub fn add_clause_with_hint_slices(
        &mut self,
        id: u64,
        clause: &[Literal],
        is_original: bool,
        resolution_hints: &[u64],
    ) {
        self.solver_num_vars = None;
        if clause.is_empty() {
            self.has_empty = true;
        }
        let Some(meta) = self.preflight_entry_meta(id, clause, is_original, resolution_hints)
        else {
            self.reject_entry("clause trace span overflow — entry dropped");
            return;
        };
        if !self.reserve_for_add(clause.len(), resolution_hints.len()) {
            self.reject_entry("clause trace memory budget/accounting exhausted — entry dropped");
            return;
        }
        self.report_duplicate_if_probed(id, is_original, clause.len());
        self.lit_pool.extend_from_slice(clause);
        self.hint_pool.extend_from_slice(resolution_hints);
        self.meta.push(meta);
    }

    fn preflight_entry_meta(
        &self,
        id: u64,
        clause: &[Literal],
        is_original: bool,
        resolution_hints: &[u64],
    ) -> Option<EntryMeta> {
        let clause_off = if clause.is_empty() {
            0
        } else {
            u32::try_from(self.lit_pool.len()).ok()?
        };
        let hints_off = if resolution_hints.is_empty() {
            0
        } else {
            u32::try_from(self.hint_pool.len()).ok()?
        };
        Some(EntryMeta {
            id,
            clause_off,
            clause_len: u32::try_from(clause.len()).ok()?,
            hints_off,
            hints_len: u32::try_from(resolution_hints.len()).ok()?,
            is_original,
        })
    }

    fn reserve_for_add(&mut self, clause_len: usize, hints_len: usize) -> bool {
        let current = ArenaCapacities::current(self);
        let Some(required) = ArenaCapacities::required_after_add(self, clause_len, hints_len)
        else {
            return false;
        };
        let Some(target) = current.bounded_growth(required, self.budget_bytes) else {
            return false;
        };
        let Some((mut meta, mut literals, mut hints)) = reserve_replacements(self, current, target)
        else {
            return false;
        };
        if let Some(replacement) = &mut meta {
            replacement.extend_from_slice(&self.meta);
        }
        if let Some(replacement) = &mut literals {
            replacement.extend_from_slice(&self.lit_pool);
        }
        if let Some(replacement) = &mut hints {
            replacement.extend_from_slice(&self.hint_pool);
        }
        if let Some(replacement) = meta {
            self.meta = replacement;
        }
        if let Some(replacement) = literals {
            self.lit_pool = replacement;
        }
        if let Some(replacement) = hints {
            self.hint_pool = replacement;
        }
        true
    }

    fn reject_entry(&mut self, reason: &'static str) {
        if !self.is_truncated {
            tracing::warn!(
                used_bytes = self.used_bytes(),
                budget_bytes = self.budget_bytes,
                entries = self.meta.len(),
                reason,
                "clause trace entry dropped"
            );
        }
        self.mark_truncated();
    }

    fn report_duplicate_if_probed(&self, id: u64, is_original: bool, clause_len: usize) {
        if !probe_trace_dup_enabled() || !self.contains_id(id) {
            return;
        }
        let prev = self
            .meta
            .iter()
            .position(|entry| entry.id == id)
            .unwrap_or(usize::MAX);
        eprintln!(
            "--sat-probe-trace-dup: id={id} pushed at entry {} already at entry {prev}; \
             new_is_original={is_original} new_len={clause_len} \
             prev_is_original={} prev_len={}",
            self.meta.len(),
            self.meta.get(prev).is_some_and(|entry| entry.is_original),
            self.meta.get(prev).map_or(0, |entry| entry.clause_len),
        );
    }

    /// Update the resolution hints for an existing clause entry.
    ///
    /// New entries should attach hints atomically through
    /// [`Self::add_clause_with_hint_slices`]. This compatibility path compacts
    /// the entire hint pool so repeated replacements retain no dead spans.
    ///
    /// Returns `false` without changing any entry or pool when the ID is
    /// missing or the compact replacement cannot fit the retained budget.
    pub fn set_resolution_hints(&mut self, id: u64, resolution_hints: Vec<u64>) -> bool {
        self.solver_num_vars = None;
        let Some(index) = self.meta.iter().rposition(|entry| entry.id == id) else {
            tracing::warn!(
                clause_id = id,
                hint_count = resolution_hints.len(),
                "set_resolution_hints: clause ID not found — resolution DAG edge dropped"
            );
            return false;
        };
        let Some((new_len, new_pool_len)) = self.replacement_hint_lengths(index, &resolution_hints)
        else {
            self.reject_hint_update(id, resolution_hints.len());
            return false;
        };
        let Some(compact) = self.build_compact_hint_pool(index, &resolution_hints, new_pool_len)
        else {
            self.reject_hint_update(id, resolution_hints.len());
            return false;
        };
        self.reindex_hint_spans(index, new_len);
        self.hint_pool = compact;
        true
    }

    fn replacement_hint_lengths(
        &self,
        index: usize,
        resolution_hints: &[u64],
    ) -> Option<(u32, usize)> {
        let old_len = self.meta.get(index)?.hints_len as usize;
        let new_len = u32::try_from(resolution_hints.len()).ok()?;
        let new_pool_len = self
            .hint_pool
            .len()
            .checked_sub(old_len)?
            .checked_add(resolution_hints.len())?;
        u32::try_from(new_pool_len).ok()?;
        Some((new_len, new_pool_len))
    }

    fn build_compact_hint_pool(
        &self,
        index: usize,
        resolution_hints: &[u64],
        new_pool_len: usize,
    ) -> Option<Vec<u64>> {
        let current = ArenaCapacities::current(self);
        let planned_replacement = ArenaCapacities {
            entries: 0,
            literals: 0,
            hints: new_pool_len,
        };
        if current.peak_with_replacements(planned_replacement)? > self.budget_bytes {
            return None;
        }
        let mut compact = Vec::new();
        compact.try_reserve_exact(new_pool_len).ok()?;
        let actual_replacement = ArenaCapacities {
            entries: 0,
            literals: 0,
            hints: compact.capacity(),
        };
        if current.peak_with_replacements(actual_replacement)? > self.budget_bytes {
            return None;
        }
        for (entry_index, meta) in self.meta.iter().enumerate() {
            if entry_index == index {
                compact.extend_from_slice(resolution_hints);
                continue;
            }
            let start = meta.hints_off as usize;
            let end = start.checked_add(meta.hints_len as usize)?;
            compact.extend_from_slice(self.hint_pool.get(start..end)?);
        }
        (compact.len() == new_pool_len).then_some(compact)
    }

    fn reindex_hint_spans(&mut self, index: usize, new_len: u32) {
        let mut next_offset = 0usize;
        for (entry_index, meta) in self.meta.iter_mut().enumerate() {
            let len = if entry_index == index {
                new_len as usize
            } else {
                meta.hints_len as usize
            };
            meta.hints_off = if len == 0 {
                0
            } else {
                u32::try_from(next_offset).expect("compact pool length was preflighted")
            };
            meta.hints_len = u32::try_from(len).expect("hint length was preflighted");
            next_offset += len;
        }
    }

    fn reject_hint_update(&mut self, id: u64, hint_count: usize) {
        if !self.is_truncated {
            tracing::warn!(
                clause_id = id,
                used_bytes = self.used_bytes(),
                budget_bytes = self.budget_bytes,
                hint_count,
                "set_resolution_hints: memory budget/accounting exhausted — edge dropped"
            );
        }
        self.mark_truncated();
    }

    /// Drop all recorded entries and release their arena allocations.
    ///
    /// The proof-exhausted and empty-clause markers remain set.
    pub fn clear_entries(&mut self) {
        self.solver_num_vars = None;
        self.meta = Vec::new();
        self.lit_pool = Vec::new();
        self.hint_pool = Vec::new();
    }

    /// Exact bytes retained by entry, literal, and hint vector capacities.
    pub fn used_bytes(&self) -> usize {
        ArenaCapacities::current(self)
            .retained_bytes()
            .unwrap_or(usize::MAX)
    }
}
