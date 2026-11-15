// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VMTF queue operations (maintained in both focused and stable modes).

use super::{INVALID_VAR, VSIDS};
use crate::literal::Variable;

impl VSIDS {
    /// Remap variable indices during variable compaction.
    pub(crate) fn compact(&mut self, map: &crate::solver::compact::VariableMap) {
        let new_n = map.new_num_vars;
        let mut new_activities = vec![0.0f64; new_n];
        let mut new_bump_order = vec![0u64; new_n];
        let mut new_buried = vec![false; new_n];
        // Only allocate new CHB arrays if they were already allocated (#8121).
        let mut new_chb_scores = self.chb_scores.as_ref().map(|_| vec![0.0f64; new_n]);
        let mut new_chb_last_conflict = self.chb_last_conflict.as_ref().map(|_| vec![0u64; new_n]);
        for (old, &new_idx) in map.old_to_new.iter().enumerate() {
            if new_idx != crate::solver::compact::UNMAPPED {
                let new = new_idx as usize;
                new_activities[new] = self.activities[old];
                new_bump_order[new] = self.bump_order[old];
                new_buried[new] = self.buried[old];
                if let Some(ref scores) = self.chb_scores {
                    if old < scores.len() {
                        new_chb_scores.as_mut().expect("mirrors source")[new] = scores[old];
                    }
                }
                if let Some(ref last) = self.chb_last_conflict {
                    if old < last.len() {
                        new_chb_last_conflict.as_mut().expect("mirrors source")[new] = last[old];
                    }
                }
            }
        }
        self.activities = new_activities;
        self.bump_order = new_bump_order;
        self.buried = new_buried;
        self.chb_scores = new_chb_scores;
        self.chb_last_conflict = new_chb_last_conflict;
        self.heap.clear();
        self.heap_pos = vec![super::INVALID_POS; new_n];
        for var in 0..new_n {
            self.push_heap(var as u32);
        }
        self.rebuild_heap();
        self.vmtf_prev = vec![INVALID_VAR; new_n];
        self.vmtf_next = vec![INVALID_VAR; new_n];
        self.vmtf_first = INVALID_VAR;
        self.vmtf_last = INVALID_VAR;
        self.vmtf_unassigned = INVALID_VAR;
        self.vmtf_unassigned_bumped = 0;
        if new_n > 0 {
            let mut vars_by_order: Vec<u32> = (0..new_n as u32).collect();
            vars_by_order.sort_by_key(|&v| self.bump_order[v as usize]);
            for (i, &var) in vars_by_order.iter().enumerate() {
                if i == 0 {
                    self.vmtf_first = var;
                    self.vmtf_prev[var as usize] = INVALID_VAR;
                } else {
                    let prev = vars_by_order[i - 1];
                    self.vmtf_prev[var as usize] = prev;
                    self.vmtf_next[prev as usize] = var;
                }
                self.vmtf_next[var as usize] = INVALID_VAR;
            }
            self.vmtf_last = *vars_by_order
                .last()
                .expect("invariant: vars_by_order non-empty when new_n > 0");
            self.vmtf_unassigned = self.vmtf_last;
            self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_last as usize];
        }
    }

    /// VMTF queue bump (focused mode): update bump order and move to front.
    /// CaDiCaL `analyze.cpp:52-103`.
    #[inline]
    pub(super) fn bump_queue(&mut self, var: Variable, vals: &[i8]) {
        let idx = var.index();
        debug_assert!(
            idx < self.bump_order.len(),
            "BUG: bump_queue variable {idx} out of range (num_vars={})",
            self.bump_order.len()
        );

        self.bump_order[idx] = self.bump_counter;
        self.bump_counter += 1;

        self.vmtf_bump_to_front(var);

        if vals[idx * 2] == 0 {
            self.vmtf_unassigned = idx as u32;
            self.vmtf_unassigned_bumped = self.bump_order[idx];
        }
    }

    /// Select next variable to branch on using VMTF (most recently bumped).
    #[inline]
    #[cfg(test)]
    pub(crate) fn pick_branching_variable_vmtf(&mut self, vals: &[i8]) -> Option<Variable> {
        self.pick_branching_variable_vmtf_with_lifecycle(vals, &[])
    }

    /// VMTF branching with eliminated-variable skipping.
    ///
    /// Hot path: called on every decision in focused mode. The search walks
    /// backward from `vmtf_unassigned` through the VMTF queue looking for
    /// the first unassigned, non-eliminated variable. A wraparound from
    /// `vmtf_last` handles the case where bumped-then-assigned variables sit
    /// between the cursor and the front of the queue.
    ///
    /// Optimization: when `var_states` is empty (no BVE elimination has
    /// occurred), the inner loop skips the eliminated-variable check entirely,
    /// tightening the hot path to a single `vals[]` test per iteration.
    ///
    /// Reference: CaDiCaL `decide.cpp:12-24` (next_decision_variable_on_queue),
    /// Kissat `decide.c:9-30` (last_enqueued_unassigned_variable).
    #[inline]
    pub(crate) fn pick_branching_variable_vmtf_with_lifecycle(
        &mut self,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) -> Option<Variable> {
        if self.vmtf_unassigned == INVALID_VAR {
            if self.vmtf_last != INVALID_VAR {
                self.vmtf_unassigned = self.vmtf_last;
                self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_last as usize];
            } else {
                return None;
            }
        }

        let has_eliminated = !var_states.is_empty();
        let mut idx = self.vmtf_unassigned;
        let mut searched = false;

        // Fast path: no eliminated variables -- only check assignment status.
        // This is the common case early in solving before any BVE elimination.
        if has_eliminated {
            while idx != INVALID_VAR
                && (vals[idx as usize * 2] != 0
                    || (idx as usize) < var_states.len() && var_states[idx as usize].is_removed())
            {
                idx = self.vmtf_prev[idx as usize];
                searched = true;
            }
        } else {
            while idx != INVALID_VAR && vals[idx as usize * 2] != 0 {
                idx = self.vmtf_prev[idx as usize];
                searched = true;
            }
        }

        // Wraparound: if we hit the end of the list, try from vmtf_last.
        // This handles the case where bumped-then-assigned variables sit
        // between the cursor and the front of the queue.
        if idx == INVALID_VAR && self.vmtf_unassigned != self.vmtf_last {
            idx = self.vmtf_last;
            if has_eliminated {
                while idx != INVALID_VAR
                    && (vals[idx as usize * 2] != 0
                        || (idx as usize) < var_states.len()
                            && var_states[idx as usize].is_removed())
                {
                    idx = self.vmtf_prev[idx as usize];
                    searched = true;
                }
            } else {
                while idx != INVALID_VAR && vals[idx as usize * 2] != 0 {
                    idx = self.vmtf_prev[idx as usize];
                    searched = true;
                }
            }
        }

        if idx == INVALID_VAR {
            return None;
        }

        if searched {
            self.vmtf_unassigned = idx;
            self.vmtf_unassigned_bumped = self.bump_order[idx as usize];
        }

        Some(Variable(idx))
    }

    /// Domain-restricted VMTF pick: walk the queue from the front (most
    /// recently bumped) and return the first unassigned, non-eliminated
    /// variable inside `in_domain`.
    ///
    /// Read-only (no cursor update): the relevancy-frontier caller runs this
    /// per decision while the queue is live, and the expected walk is short
    /// (frontier density over the queue). The caller must not use this while
    /// `vmtf_is_deferred()` — the linked list is stale then (stable-mode
    /// bumps only refreshed `bump_order`); it falls back to a members scan.
    /// Queue order is bump recency, including rephase shuffles and burials —
    /// the same order the unrestricted VMTF pick follows.
    pub(crate) fn pick_vmtf_in_domain(
        &self,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
        in_domain: &[bool],
    ) -> Option<Variable> {
        let has_eliminated = !var_states.is_empty();
        let mut idx = self.vmtf_last;
        // The queue holds each variable at most once; the bound only guards
        // against a corrupted cycle turning into an infinite walk.
        let mut steps = self.vmtf_prev.len() + 1;
        while idx != INVALID_VAR {
            if steps == 0 {
                debug_assert!(false, "BUG: VMTF queue walk exceeded queue length");
                return None;
            }
            steps -= 1;
            let i = idx as usize;
            if i < in_domain.len()
                && in_domain[i]
                && vals[i * 2] == 0
                && !(has_eliminated && i < var_states.len() && var_states[i].is_removed())
            {
                return Some(Variable(idx));
            }
            idx = self.vmtf_prev[i];
        }
        None
    }

    /// Fisher-Yates shuffle of VMTF queue for focused-mode rephasing.
    pub(crate) fn shuffle_queue(&mut self, rephase_count: u64) {
        let mut vars: Vec<u32> = Vec::new();
        let mut cur = self.vmtf_first;
        while cur != INVALID_VAR {
            vars.push(cur);
            cur = self.vmtf_next[cur as usize];
        }

        if vars.len() <= 1 {
            return;
        }

        let mut rng = rephase_count
            .wrapping_mul(6364136223846793005)
            .wrapping_add(7046029254386353131);
        for i in (1..vars.len()).rev() {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let j = (rng >> 33) as usize % (i + 1);
            vars.swap(i, j);
        }

        self.vmtf_first = INVALID_VAR;
        self.vmtf_last = INVALID_VAR;
        for (i, &var) in vars.iter().enumerate() {
            if i == 0 {
                self.vmtf_first = var;
                self.vmtf_prev[var as usize] = INVALID_VAR;
            } else {
                let prev = vars[i - 1];
                self.vmtf_prev[var as usize] = prev;
                self.vmtf_next[prev as usize] = var;
            }
            self.vmtf_next[var as usize] = INVALID_VAR;
        }
        if let Some(&last) = vars.last() {
            self.vmtf_last = last;
            self.vmtf_unassigned = last;
            self.vmtf_unassigned_bumped = self.bump_order[last as usize];
        }

        #[cfg(debug_assertions)]
        self.debug_assert_vmtf_consistent();
    }

    #[inline]
    fn vmtf_bump_to_front(&mut self, var: Variable) {
        let idx = var.0;
        if idx == INVALID_VAR {
            return;
        }
        self.buried[idx as usize] = false;
        if idx == self.vmtf_last {
            return;
        }
        // Fused dequeue+enqueue (instruction-shave #4): `vmtf_dequeue`
        // writes INVALID_VAR into the moved node's own prev/next pointers,
        // which the immediate re-enqueue overwrites, and re-tests conditions
        // that are statically known here (`idx != vmtf_last` implies the node
        // has a valid `next` and the queue is non-empty). The resulting list
        // state is identical to dequeue-then-enqueue (CaDiCaL analyze.cpp:52-58
        // performs the same unlink/relink without clearing).
        let prev = self.vmtf_prev[idx as usize];
        let next = self.vmtf_next[idx as usize];
        debug_assert_ne!(
            next, INVALID_VAR,
            "BUG: vmtf_bump_to_front node {idx} != vmtf_last has no next"
        );
        if prev != INVALID_VAR {
            self.vmtf_next[prev as usize] = next;
        } else {
            debug_assert_eq!(
                self.vmtf_first, idx,
                "BUG: bump_to_front node {idx} has no prev but vmtf_first={}",
                self.vmtf_first
            );
            self.vmtf_first = next;
        }
        self.vmtf_prev[next as usize] = prev;

        let last = self.vmtf_last;
        debug_assert_ne!(
            last, INVALID_VAR,
            "BUG: vmtf_last invalid with node in queue"
        );
        debug_assert_eq!(
            self.vmtf_next[last as usize], INVALID_VAR,
            "BUG: vmtf_last ({last}) has non-INVALID next = {}",
            self.vmtf_next[last as usize]
        );
        self.vmtf_prev[idx as usize] = last;
        self.vmtf_next[idx as usize] = INVALID_VAR;
        self.vmtf_next[last as usize] = idx;
        self.vmtf_last = idx;
    }

    #[inline]
    pub(super) fn vmtf_bury_to_oldest(&mut self, var: Variable) {
        let idx = var.0;
        if idx == INVALID_VAR || idx == self.vmtf_first {
            return;
        }
        self.vmtf_dequeue(idx);
        self.vmtf_prepend(idx);
    }

    #[inline]
    fn vmtf_dequeue(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_dequeue({idx}) out of range"
        );
        let prev = self.vmtf_prev[idx as usize];
        let next = self.vmtf_next[idx as usize];
        if prev != INVALID_VAR {
            self.vmtf_next[prev as usize] = next;
        } else {
            debug_assert_eq!(
                self.vmtf_first, idx,
                "BUG: dequeue node {idx} has no prev but vmtf_first={}",
                self.vmtf_first
            );
            self.vmtf_first = next;
        }
        if next != INVALID_VAR {
            self.vmtf_prev[next as usize] = prev;
        } else {
            debug_assert_eq!(
                self.vmtf_last, idx,
                "BUG: dequeue node {idx} has no next but vmtf_last={}",
                self.vmtf_last
            );
            self.vmtf_last = prev;
        }
        self.vmtf_prev[idx as usize] = INVALID_VAR;
        self.vmtf_next[idx as usize] = INVALID_VAR;
    }

    #[inline]
    pub(super) fn vmtf_enqueue(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_enqueue({idx}) out of range"
        );
        if self.vmtf_last == INVALID_VAR {
            self.vmtf_first = idx;
            self.vmtf_last = idx;
            self.vmtf_prev[idx as usize] = INVALID_VAR;
            self.vmtf_next[idx as usize] = INVALID_VAR;
            return;
        }
        let last = self.vmtf_last;
        debug_assert_eq!(
            self.vmtf_next[last as usize], INVALID_VAR,
            "BUG: vmtf_last ({last}) has non-INVALID next = {}",
            self.vmtf_next[last as usize]
        );
        self.vmtf_prev[idx as usize] = last;
        self.vmtf_next[idx as usize] = INVALID_VAR;
        self.vmtf_next[last as usize] = idx;
        self.vmtf_last = idx;
    }

    #[inline]
    fn vmtf_prepend(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_prepend({idx}) out of range"
        );
        if self.vmtf_first == INVALID_VAR {
            self.vmtf_first = idx;
            self.vmtf_last = idx;
            self.vmtf_prev[idx as usize] = INVALID_VAR;
            self.vmtf_next[idx as usize] = INVALID_VAR;
            return;
        }
        let first = self.vmtf_first;
        debug_assert_eq!(
            self.vmtf_prev[first as usize], INVALID_VAR,
            "BUG: vmtf_first ({first}) has non-INVALID prev = {}",
            self.vmtf_prev[first as usize]
        );
        self.vmtf_prev[idx as usize] = INVALID_VAR;
        self.vmtf_next[idx as usize] = first;
        self.vmtf_prev[first as usize] = idx;
        self.vmtf_first = idx;
    }
}

impl VSIDS {
    /// Rebuild the VMTF linked list from bump_order values.
    ///
    /// Called before arena compaction or when switching from stable to focused
    /// mode, to restore VMTF list consistency after deferred stable-mode bumps.
    /// Cost: O(n log n) for the sort, but runs infrequently.
    pub(crate) fn rebuild_vmtf_from_bump_order(&mut self, vals: &[i8]) {
        if !self.vmtf_deferred {
            return;
        }
        let n = self.activities.len();
        if n == 0 {
            self.vmtf_deferred = false;
            return;
        }

        // Sort variables by ascending bump_order (oldest first -> newest last).
        let mut vars_by_order: Vec<u32> = (0..n as u32).collect();
        vars_by_order.sort_unstable_by_key(|&v| self.bump_order[v as usize]);

        // Rebuild doubly-linked list.
        self.vmtf_first = INVALID_VAR;
        self.vmtf_last = INVALID_VAR;
        self.vmtf_prev.fill(INVALID_VAR);
        self.vmtf_next.fill(INVALID_VAR);

        for (i, &var) in vars_by_order.iter().enumerate() {
            if i == 0 {
                self.vmtf_first = var;
                self.vmtf_prev[var as usize] = INVALID_VAR;
            } else {
                let prev = vars_by_order[i - 1];
                self.vmtf_prev[var as usize] = prev;
                self.vmtf_next[prev as usize] = var;
            }
            self.vmtf_next[var as usize] = INVALID_VAR;
        }
        if let Some(&last) = vars_by_order.last() {
            self.vmtf_last = last;
        }

        // Reset unassigned cursor to the most recently bumped unassigned variable.
        self.vmtf_unassigned = INVALID_VAR;
        self.vmtf_unassigned_bumped = 0;
        // Walk from newest (vmtf_last) to oldest to find highest-bumped unassigned.
        let mut cur = self.vmtf_last;
        while cur != INVALID_VAR {
            if vals[cur as usize * 2] == 0 && !self.buried[cur as usize] {
                self.vmtf_unassigned = cur;
                self.vmtf_unassigned_bumped = self.bump_order[cur as usize];
                break;
            }
            cur = self.vmtf_prev[cur as usize];
        }

        self.vmtf_deferred = false;

        #[cfg(debug_assertions)]
        self.debug_assert_vmtf_consistent();
    }

    /// `--sat-queue-freeze-kissat`: whether stable bumps leave the queue alone.
    pub(crate) fn queue_frozen_in_stable(&self) -> bool {
        self.queue_freeze
    }

    /// Kissat `kissat_reset_search_of_queue` (queue.c:13-20), run on entry to
    /// focused mode under `--sat-queue-freeze-kissat`: the queue is the one
    /// the last focused phase left, and the search restarts from its end.
    pub(crate) fn reset_vmtf_search_to_last(&mut self) {
        self.vmtf_unassigned = self.vmtf_last;
        self.vmtf_unassigned_bumped = if self.vmtf_last == INVALID_VAR {
            0
        } else {
            self.bump_order[self.vmtf_last as usize]
        };
    }
}
