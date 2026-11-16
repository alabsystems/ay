// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pay the existing frontier fold and exactness pin without changing them.

use super::*;
#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
use crate::counted_storage::try_reserve;
use crate::counted_storage::Result;
#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
use crate::solver::backtrack::admission::admit_visits;
use ay_core::original_query::CountedAdmission;

impl RelevancyFrontier {
    pub(in crate::solver) fn prepare_backtrack(
        &mut self,
        s: &Solver,
        target: u32,
        start: usize,
        owner: &CountedAdmission,
    ) -> Result<Vec<bool>> {
        owner.admit(1, 0)?;
        if !self.valid {
            return Ok(Vec::new());
        }
        if self.epoch != s.arena.formula_epoch()
            || self.arena_words > s.arena.len()
            || self.arena_clauses > s.arena.num_clauses()
        {
            // begin_unassign_fold will invalidate, clearing these vector
            // headers, but must not do so if admission itself is refused.
            owner.admit(self.occ.len(), 0)?;
            return Ok(Vec::new());
        }
        let mut edges = 0;
        for index in start..self.synced_len.min(s.trail.len()) {
            owner.admit(1, 0)?;
            let lit = s.trail[index];
            if s.var_data[lit.variable().index()].level > target {
                self.admit_literal_fold(s, lit, &mut edges, owner)?;
            }
        }
        owner.admit(edges, 0)?;
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        if self.will_check_fold() {
            return self.prepare_exactness(s, owner);
        }
        Ok(Vec::new())
    }

    fn admit_literal_fold(
        &self,
        s: &Solver,
        lit: Literal,
        edges: &mut usize,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?; // actual per-literal fold
        if let Some(occurrences) = self.occ.get(lit.index()) {
            for &offset in occurrences {
                // Planning metadata + actual occurrence visit. Each clause
                // crosses zero at most once per monotone fold phase. Thus the
                // nested-edge bound is min(sum(candidate lengths), arena words),
                // not the quadratic sum when many literals share a clause.
                owner.admit(2, 0)?;
                *edges = edges
                    .saturating_add(s.arena.len_of(offset as usize))
                    .min(s.arena.len());
            }
        }
        Ok(())
    }

    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn will_check_fold(&self) -> bool {
        #[cfg(feature = "relevancy-frontier-invariants")]
        return true;
        #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
        return self.debug_fold_checks_done < DEFAULT_DEBUG_CHECKS;
    }

    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn prepare_exactness(&mut self, s: &Solver, owner: &CountedAdmission) -> Result<Vec<bool>> {
        // Backtrack preserves order: only survivors of this formerly-unfolded
        // suffix can be folded in by the post-compaction exactness pin.
        let mut edges = 0;
        for index in self.synced_len..s.trail.len() {
            owner.admit(1, 0)?;
            self.admit_literal_fold(s, s.trail[index], &mut edges, owner)?;
        }
        owner.admit(edges, 0)?;
        if self.arena_words < s.arena.len() {
            self.reserve_appends(s, owner)?;
        }
        // The reference walks the arena (including dead headers/shrink-map
        // probes) and up to two literal passes. Charge arena words for each
        // pass: an arena walk advances at least one word on every iteration.
        admit_visits(owner, s.arena.len(), 3)?;
        // Reference initialization, equality, and possible mismatch-location
        // walk are each bounded by num_vars; keep the original assertion.
        admit_visits(owner, s.num_vars, 3)?;
        let mut reference = Vec::new();
        try_reserve(owner, &mut reference, s.num_vars)?;
        Ok(reference)
    }

    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn reserve_appends(&mut self, s: &Solver, owner: &CountedAdmission) -> Result<()> {
        use crate::counted_storage::try_vec_with;
        use ay_core::original_query::CountedAdmissionError;

        let growth = s.arena.len().saturating_sub(self.true_count.len());
        owner.admit(growth, 0)?;
        try_reserve(owner, &mut self.true_count, growth)?;
        let mut additions = try_vec_with(owner, self.occ.len(), |_| 0usize)?;
        // Iterator metadata visits, including inactive headers, are prepaid.
        admit_visits(owner, s.arena.len() - self.arena_words, 2)?;
        for offset in s.arena.active_indices_from(self.arena_words) {
            if s.arena.is_garbage_any(offset) {
                continue;
            }
            // Planning literal visits plus the real seed/unsatisfied passes.
            admit_visits(owner, s.arena.len_of(offset), 3)?;
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
            try_reserve(owner, occurrences, additional)?;
        }
        Ok(())
    }

    #[cfg(test)]
    pub(in crate::solver) fn backtrack_test_snapshot(&self) -> String {
        let checks = {
            #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
            {
                (self.debug_checks_done, self.debug_fold_checks_done)
            }
            #[cfg(not(all(debug_assertions, not(feature = "relevancy-frontier-invariants"))))]
            {
                (0u32, 0u32)
            }
        };
        format!(
            "{:?}",
            (
                (
                    &self.buf,
                    self.size,
                    &self.var_unsat,
                    &self.true_count,
                    &self.occ
                ),
                (
                    self.synced_len,
                    self.arena_words,
                    self.arena_clauses,
                    self.epoch,
                    self.num_vars,
                    self.valid
                ),
                checks,
            )
        )
    }

    #[cfg(all(test, any(debug_assertions, feature = "relevancy-frontier-invariants")))]
    pub(in crate::solver) fn backtrack_test_capacities(&self) -> Vec<usize> {
        [
            self.buf.capacity(),
            self.var_unsat.capacity(),
            self.true_count.capacity(),
            self.occ.capacity(),
        ]
        .into_iter()
        .chain(self.occ.iter().map(Vec::capacity))
        .collect()
    }

    #[cfg(all(test, any(debug_assertions, feature = "relevancy-frontier-invariants")))]
    pub(in crate::solver) fn backtrack_test_shrink(&mut self) {
        self.true_count.shrink_to_fit();
        for occurrences in &mut self.occ {
            occurrences.shrink_to_fit();
        }
    }
}
