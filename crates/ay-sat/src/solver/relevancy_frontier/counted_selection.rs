// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission for the actual incremental sync/rebuild used by decision picking.

use super::*;
use crate::counted_storage::{try_reserve, try_reserved_exact, try_vec_with, Result};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

#[cfg(test)]
mod tests;

#[derive(Default)]
pub(in crate::solver) struct SelectionStorage {
    extra_occ: Vec<Vec<u32>>,
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    pub(in crate::solver) reference: Vec<bool>,
}

impl SelectionStorage {
    pub(super) fn install_headers(&mut self, occurrences: &mut Vec<Vec<u32>>, required: usize) {
        // Preparation and commit see the same cache/arena. Every new inner
        // vector has its own paid capacity, not merely an outer-table slot.
        assert_eq!(
            self.extra_occ.len(),
            required.saturating_sub(occurrences.len())
        );
        occurrences.extend(self.extra_occ.drain(..));
        occurrences.truncate(required);
    }
}

impl RelevancyFrontier {
    pub(super) fn needs_rebuild(&self, s: &Solver) -> bool {
        !self.valid
            || self.num_vars != s.num_vars
            || self.epoch != s.arena.formula_epoch()
            || self.arena_words > s.arena.len()
            || self.arena_clauses > s.arena.num_clauses()
            || self.synced_len > s.trail.len()
    }

    pub(in crate::solver) fn prepare_selection(
        &mut self,
        s: &Solver,
        owner: &CountedAdmission,
    ) -> Result<SelectionStorage> {
        owner.admit(1, 0)?;
        let mut storage = SelectionStorage::default();
        if self.needs_rebuild(s) {
            self.reserve_rebuild(s, owner, &mut storage)?;
        } else {
            self.admit_pending_assignments(s, owner)?;
            if self.arena_words < s.arena.len() {
                let appended = self.reserve_selection_appends(s, owner)?;
                if self.arena_clauses.checked_add(appended) != Some(s.arena.num_clauses()) {
                    // The original sync folds the append first, then rebuilds.
                    // Reserve/pay BOTH operations, including their peak sizes.
                    self.reserve_rebuild(s, owner, &mut storage)?;
                }
            }
        }
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        if self.will_check_query() {
            passes(owner, s.arena.len(), 3)?; // headers + two literal passes
            passes(owner, s.num_vars, 3)?; // initialize, compare, mismatch walk
            try_reserve(owner, &mut storage.reference, s.num_vars)?;
        }
        Ok(storage)
    }

    fn admit_pending_assignments(&self, s: &Solver, owner: &CountedAdmission) -> Result<()> {
        let mut edges = 0usize;
        for index in self.synced_len..s.trail.len() {
            owner.admit(2, 0)?; // planning and real per-assignment fold
            let lit = s.trail[index];
            if let Some(occurrences) = self.occ.get(lit.index()) {
                let mut entry = 0;
                while entry < occurrences.len() {
                    owner.admit(2, 0)?; // metadata and real occurrence visit
                    let offset = occurrences[entry] as usize;
                    entry += 1;
                    // Each clause crosses 0 -> 1 at most once in this phase.
                    edges = edges
                        .saturating_add(s.arena.len_of(offset))
                        .min(s.arena.len());
                }
            }
        }
        owner.admit(edges, 0)
    }

    fn reserve_selection_appends(&mut self, s: &Solver, owner: &CountedAdmission) -> Result<usize> {
        let growth = s.arena.len().saturating_sub(self.true_count.len());
        owner.admit(growth, 0)?;
        try_reserve(owner, &mut self.true_count, growth)?;
        let mut additions = try_vec_with(owner, self.occ.len(), |_| 0usize)?;
        // Planning and real arena header walks, including inactive headers.
        passes(owner, s.arena.len() - self.arena_words, 2)?;
        let mut appended = 0usize;
        for offset in s.arena.active_indices_from(self.arena_words) {
            appended = appended
                .checked_add(1)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            if s.arena.is_garbage_any(offset) {
                continue;
            }
            passes(owner, s.arena.len_of(offset), 3)?; // plan + seed + unsatisfied
            for lit in s.arena.literals(offset) {
                if let Some(count) = additions.get_mut(lit.index()) {
                    *count = count
                        .checked_add(1)
                        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                }
            }
        }
        owner.admit(self.occ.len(), 0)?;
        for (occurrences, additional) in self.occ.iter_mut().zip(additions) {
            let required = occurrences
                .len()
                .checked_add(additional)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            reserve_pushes(occurrences, required, owner)?;
        }
        Ok(appended)
    }

    fn reserve_rebuild(
        &mut self,
        s: &Solver,
        owner: &CountedAdmission,
        storage: &mut SelectionStorage,
    ) -> Result<()> {
        let literals = s
            .num_vars
            .checked_mul(2)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        // Current lengths are retained through preflight. Rebuild itself will
        // clear/resize them, after every reservation and work debit succeeds.
        reserve_length(&mut self.buf, s.num_vars, owner)?;
        reserve_length(&mut self.var_unsat, s.num_vars, owner)?;
        reserve_length(&mut self.true_count, s.arena.len(), owner)?;
        reserve_length(&mut self.occ, literals, owner)?;
        passes(owner, s.num_vars, 3)?; // buf/var_unsat fills + membership scan
        owner.admit(s.arena.len(), 0)?; // true_count fill
        passes(owner, literals.max(self.occ.len()), 2)?; // headers/drop/clear
        let mut counts = try_vec_with(owner, literals, |_| 0usize)?;
        passes(owner, s.arena.len(), 5)?; // plan header/literal + real header/2 literals
        for offset in s.arena.live_indices() {
            for lit in s.arena.literals(offset) {
                if let Some(count) = counts.get_mut(lit.index()) {
                    *count = count
                        .checked_add(1)
                        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                }
            }
        }
        let missing = literals.saturating_sub(self.occ.len());
        // This outer temporary owns new headers until the real rebuild adopts
        // them. Refusal drops only scratch and leaves cache lengths unchanged.
        owner.admit(missing, 0)?; // cleanup of any partially prepared headers
        storage.extra_occ = try_reserved_exact(owner, missing)?;
        owner.admit(literals, 0)?;
        for (index, required) in counts.into_iter().enumerate() {
            if let Some(occurrences) = self.occ.get_mut(index) {
                reserve_pushes(occurrences, required, owner)?;
            } else {
                let mut occurrences = Vec::new();
                reserve_pushes(&mut occurrences, required, owner)?;
                storage.extra_occ.push(occurrences);
            }
        }
        Ok(())
    }

    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn will_check_query(&self) -> bool {
        #[cfg(feature = "relevancy-frontier-invariants")]
        return true;
        #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
        return self.debug_checks_done < DEFAULT_DEBUG_CHECKS;
    }
}

fn reserve_length<T>(values: &mut Vec<T>, required: usize, owner: &CountedAdmission) -> Result<()> {
    let additional = required.saturating_sub(values.len());
    try_reserve(owner, values, additional)
}

fn reserve_pushes(values: &mut Vec<u32>, required: usize, owner: &CountedAdmission) -> Result<()> {
    // The ordinary folds append one u32 at a time, unlike resize's single
    // reservation. Preserve that final amortized capacity while making the
    // actual replacement allocation fallible and prepaid in one operation.
    let mut target = values.capacity();
    while target < required {
        owner.admit(1, 0)?;
        target = target
            .checked_mul(2)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?
            .max(4); // RawVec's u32 minimum, as in counted_storage
    }
    try_reserve(owner, values, target.saturating_sub(values.len()))
}

fn passes(owner: &CountedAdmission, count: usize, number: usize) -> Result<()> {
    let work = count
        .checked_mul(number)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)
}
