// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct WorkCol {
    pub(super) active: bool,
    pub(super) lower: Option<BigRational>,
    pub(super) upper: Option<BigRational>,
    pub(super) kind: ColKind,
}

pub(super) struct WorkRow {
    pub(super) active: bool,
    pub(super) lower: Option<BigRational>,
    pub(super) upper: Option<BigRational>,
    /// Sorted, unique, nonzero, and always in the original column frame.
    pub(super) coeffs: Vec<(usize, BigRational)>,
}

pub(super) struct Work {
    pub(super) cols: Vec<WorkCol>,
    pub(super) rows: Vec<WorkRow>,
    pub(super) objective: Vec<BigRational>,
    pub(super) input_nnz: usize,
    pub(super) active_nnz: usize,
    pub(super) nnz_cap: usize,
    pub(super) recovery_term_cap: usize,
    pub(super) const_delta: BigRational,
    pub(super) recover: Vec<AffineRecovery>,
    pub(super) recovery_terms: usize,
}

pub(super) struct Candidate {
    pub(super) row: usize,
    pub(super) pivot: usize,
    pub(super) constant: BigRational,
    pub(super) terms: Vec<(usize, BigRational)>,
    pub(super) key: (bool, usize, usize, usize, usize),
}

#[derive(Clone, Copy)]
pub(super) struct StructuralPreflight {
    pub(super) input_nnz: usize,
    pub(super) max_row_nnz: usize,
}

/// One solve owns one retained-memory envelope.  Exact aggregation gets a
/// bounded share of it and is additionally clamped by the process-wide limit.
/// `start_bytes` makes the polling useful even when the caller supplied a
/// tighter envelope than the process cap: unrelated concurrent growth also
/// makes the speculative pass decline, which is the fail-closed choice.
pub(super) struct ResourceGuard {
    deadline: Option<Instant>,
    start_live_bytes: usize,
    start_bytes: usize,
    growth_budget: usize,
    process_ceiling: Option<usize>,
    polls: std::cell::Cell<usize>,
}

impl ResourceGuard {
    pub(super) fn new(
        deadline: Option<Instant>,
        memory_budget: Option<usize>,
        planned_bytes: usize,
    ) -> Option<Self> {
        if expired(deadline) || memory_budget == Some(0) {
            return None;
        }
        let requested = memory_budget.unwrap_or(DEFAULT_WORKSPACE_BYTES);
        let phase_budget = requested.checked_div(WORKSPACE_SHARE)?;
        if phase_budget == 0 {
            return None;
        }
        let start_live_bytes = ay_sys::current_live_bytes();
        let start_bytes = current_process_bytes();
        let process_limit = ay_sys::get_process_memory_limit();
        let process_ceiling = (process_limit != 0)
            .then(|| process_limit.saturating_mul(PROCESS_MEMORY_PERCENT) / 100);
        let process_remaining = process_ceiling
            .map(|ceiling| ceiling.saturating_sub(start_bytes))
            .unwrap_or(usize::MAX);
        let growth_budget = phase_budget.min(process_remaining);
        if planned_bytes > growth_budget
            || ay_sys::process_memory_exceeded_at_percent(PROCESS_MEMORY_PERCENT)
        {
            return None;
        }
        Some(Self {
            deadline,
            start_live_bytes,
            start_bytes,
            growth_budget,
            process_ceiling,
            polls: std::cell::Cell::new(0),
        })
    }

    pub(super) fn stopped(&self) -> bool {
        if expired(self.deadline) || ay_sys::live_bytes_exceeded_at_percent(PROCESS_MEMORY_PERCENT)
        {
            return true;
        }
        let live = ay_sys::current_live_bytes();
        if live.saturating_sub(self.start_live_bytes) > self.growth_budget
            || self.process_ceiling.is_some_and(|ceiling| live > ceiling)
        {
            return true;
        }
        // Footprint/RSS polling is a syscall on supported platforms.  Keep the
        // live-heap/deadline checks above hot and use the full three-signal
        // process guard as a coarse backstop while exact work advances.
        let poll = self.polls.get();
        self.polls.set(poll.wrapping_add(1));
        if !poll.is_multiple_of(64) {
            return false;
        }
        if ay_sys::process_memory_exceeded_at_percent(PROCESS_MEMORY_PERCENT) {
            return true;
        }
        let current = current_process_bytes();
        self.process_ceiling
            .is_some_and(|ceiling| current > ceiling)
            || current.saturating_sub(self.start_bytes) > self.growth_budget
    }
}
