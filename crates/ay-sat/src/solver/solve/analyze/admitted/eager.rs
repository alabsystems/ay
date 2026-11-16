// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admit the real bounded eager window, including selected garbage/watch
//! effects. The same subsumption predicate and ordinary mutation kernel run.

use super::*;
use crate::decision_trace::counted_decision::invalid;

struct Marks<'a> {
    s: &'a mut Solver,
    off: usize,
}
impl Drop for Marks<'_> {
    fn drop(&mut self) {
        self.s
            .lit_marks
            .clear_clause(self.s.arena.literals(self.off));
    }
}

impl Solver {
    pub(in crate::solver) fn eager_subsume_counted(
        &mut self,
        off: usize,
        owner: &CountedAdmission,
    ) -> AdmissionResult<()> {
        owner.admit(16, 0)?;
        let new_len = self.arena.len_of(off);
        if new_len == 0 {
            return Ok(());
        }
        self.lit_marks
            .prepare_eager_counted(self.arena.literals(off), owner)?;
        // Clear has already been paid. Arm before marking and before any
        // observer can unwind with an opaque panic payload.
        let mut scope = Marks { s: self, off };
        for &lit in scope.s.arena.literals(off) {
            scope.s.lit_marks.mark(lit);
        }
        let pushes = scope.prepare_candidates(new_len, owner)?;
        reserve_push_sequence(&mut scope.s.dirty_watch_list, pushes, owner)?;
        if scope.s.cold.num_eager_subsumptions > u64::MAX - 20
            || scope.s.cold.num_eager_subsumed_duplicate_binaries > u64::MAX - 20
        {
            return Err(invalid(owner, "eager subsumption counter overflow"));
        }
        owner.check()?;
        scope.s.eager_subsume(off);
        drop(scope); // exceptional and normal mark retirement precede fence
        owner.check()
    }
}

impl Marks<'_> {
    fn prepare_candidates(
        &mut self,
        new_len: usize,
        owner: &CountedAdmission,
    ) -> AdmissionResult<usize> {
        let end = self.s.cold.learned_clause_trail.len().saturating_sub(1);
        let start = end.saturating_sub(20);
        let mut pushes = 0;
        for i in (start..end).rev() {
            // Both the preflight and ordinary kernel query pending ownership.
            owner.admit(
                self.s
                    .pending_theory_conflicts
                    .len()
                    .saturating_mul(2)
                    .saturating_add(24),
                0,
            )?;
            let cand = self.s.cold.learned_clause_trail[i];
            if self.s.is_pending_theory_conflict_clause(cand) {
                continue;
            }
            let Some(len) = self.s.arena.eager_subsume_candidate_len(cand) else {
                continue;
            };
            if len < new_len {
                continue;
            }
            // Actual and debug reference scans, in both preflight and commit.
            owner.admit(len.saturating_mul(4), 0)?;
            if !self.s.eager_candidate_subsumed(cand, new_len) {
                continue;
            }
            if len > 2 {
                let (a, b) = self.s.arena.watched_literals(cand);
                pushes += usize::from(a.index() < self.s.dirty_watches.len());
                pushes += usize::from(b.index() < self.s.dirty_watches.len());
            } else if new_len == 2
                && ay_core::sat_ab_switches().eager_subsume_unlink_binaries == Some(true)
            {
                // remove_watch retains/shifts the real two watch lists.
                let (a, b) = (self.s.arena.literal(cand, 0), self.s.arena.literal(cand, 1));
                owner.admit(
                    self.s
                        .watches
                        .len_of(a)
                        .saturating_add(self.s.watches.len_of(b)),
                    0,
                )?;
            }
        }
        Ok(pushes)
    }
}

/// Match capacities from the ordinary sequence of individual pushes. Reserving
/// exactly the final length could change the memory-triggered search cadence.
fn reserve_push_sequence<T>(
    values: &mut Vec<T>,
    pushes: usize,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    let mut capacity = values.capacity();
    let mut len = values.len();
    let element = size_of::<T>();
    for _ in 0..pushes {
        owner.admit(1, 0)?;
        len = len
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        if len > capacity {
            let floor = if element == 1 {
                8
            } else if element <= 1024 {
                4
            } else {
                1
            };
            capacity = capacity
                .checked_mul(2)
                .map(|n| n.max(len).max(floor))
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            let bytes = capacity
                .checked_mul(element)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            owner.admit(capacity.saturating_add(len), bytes)?;
        }
    }
    if capacity > values.capacity() {
        values
            .try_reserve_exact(capacity - values.len())
            .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    }
    Ok(())
}
