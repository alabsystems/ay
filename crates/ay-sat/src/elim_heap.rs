// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Indexed binary min-heap for BVE elimination scheduling.
//!
//! Cheapest variable (lowest `pos_occ * neg_occ` score) at the top.
//! Mirrors CaDiCaL's `heap<elim_more>` (elim.hpp:16) but as a min-heap.
//! Supports O(1) `contains`, O(log n) `push`/`pop`/`update`.

use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

/// Invalid heap position marker (variable not in heap).
const INVALID_POS: u32 = u32::MAX;

/// Indexed binary min-heap for BVE elimination scheduling.
pub(crate) struct ElimHeap {
    /// Binary min-heap of variable indices.
    heap: Vec<u32>,
    /// Variable index -> position in heap (`INVALID_POS` = not present).
    pos: Vec<u32>,
}

impl ElimHeap {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            heap: Vec::new(),
            pos: vec![INVALID_POS; num_vars],
        }
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.pos.len() < num_vars {
            self.pos.resize(num_vars, INVALID_POS);
        }
    }

    #[inline]
    pub(crate) fn contains(&self, var: Variable) -> bool {
        let idx = var.index();
        idx < self.pos.len() && self.pos[idx] != INVALID_POS
    }

    pub(crate) fn push(&mut self, var: Variable, occ: &OccList, gate_pair_credit: &[u64]) {
        let idx = var.index();
        if idx < self.pos.len() && self.pos[idx] != INVALID_POS {
            return;
        }
        if idx >= self.pos.len() {
            self.pos.resize(idx + 1, INVALID_POS);
        }
        let p = self.heap.len();
        self.heap.push(idx as u32);
        self.pos[idx] = p as u32;
        self.sift_up(p, occ, gate_pair_credit);
    }

    pub(crate) fn pop(&mut self, occ: &OccList, gate_pair_credit: &[u64]) -> Option<Variable> {
        if self.heap.is_empty() {
            return None;
        }
        let root = self.heap[0] as usize;
        self.pos[root] = INVALID_POS;
        let last = self.heap.len() - 1;
        if last > 0 {
            let tail = self.heap[last];
            self.heap[0] = tail;
            self.pos[tail as usize] = 0;
            self.heap.pop();
            self.sift_down(0, occ, gate_pair_credit);
        } else {
            self.heap.pop();
        }
        Some(Variable(root as u32))
    }

    pub(crate) fn update(&mut self, var: Variable, occ: &OccList, gate_pair_credit: &[u64]) {
        let idx = var.index();
        if idx >= self.pos.len() || self.pos[idx] == INVALID_POS {
            return;
        }
        let p = self.pos[idx] as usize;
        self.sift_up(p, occ, gate_pair_credit);
        let p = self.pos[idx] as usize;
        self.sift_down(p, occ, gate_pair_credit);
    }

    pub(crate) fn clear(&mut self) {
        for &var in &self.heap {
            self.pos[var as usize] = INVALID_POS;
        }
        self.heap.clear();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.heap.len()
    }

    /// Insert if absent, or update score if present.
    pub(crate) fn push_or_update(
        &mut self,
        var: Variable,
        occ: &OccList,
        gate_pair_credit: &[u64],
    ) {
        if self.contains(var) {
            self.update(var, occ, gate_pair_credit);
        } else {
            self.push(var, occ, gate_pair_credit);
        }
    }

    /// Elimination score: pos_count * neg_count + pos_count + neg_count.
    /// Lower score = cheaper elimination = higher priority in the min-heap.
    ///
    /// CaDiCaL gives pure literals negative scores so they are eliminated
    /// before any variable that would generate resolvents at all. AY's heap
    /// uses an unsigned score, so we map that case to zero.
    #[inline]
    pub(crate) fn elim_score(var: Variable, occ: &OccList, gate_pair_credit: &[u64]) -> u64 {
        let pos = occ.count(Literal::positive(var)) as u64;
        let neg = occ.count(Literal::negative(var)) as u64;
        if pos == 0 || neg == 0 {
            return 0;
        }
        let base = pos
            .saturating_mul(neg)
            .saturating_add(pos)
            .saturating_add(neg);
        let credit = gate_pair_credit
            .get(var.index())
            .copied()
            .unwrap_or(0)
            .min(pos.saturating_mul(neg));
        base.saturating_sub(credit)
    }

    #[inline]
    fn sift_up(&mut self, mut p: usize, occ: &OccList, gate_pair_credit: &[u64]) {
        while p > 0 {
            let parent = (p - 1) / 2;
            let var = Variable(self.heap[p]);
            let parent_var = Variable(self.heap[parent]);
            let s = Self::elim_score(var, occ, gate_pair_credit);
            let ps = Self::elim_score(parent_var, occ, gate_pair_credit);
            if ps < s || (ps == s && parent_var.0 <= var.0) {
                break;
            }
            self.heap[p] = parent_var.0;
            self.heap[parent] = var.0;
            self.pos[var.index()] = parent as u32;
            self.pos[parent_var.index()] = p as u32;
            p = parent;
        }
    }

    #[inline]
    fn sift_down(&mut self, mut p: usize, occ: &OccList, gate_pair_credit: &[u64]) {
        loop {
            let left = 2 * p + 1;
            let right = 2 * p + 2;
            let mut smallest = p;
            let var = Variable(self.heap[p]);
            let mut smallest_score = Self::elim_score(var, occ, gate_pair_credit);
            let mut smallest_var = var;

            if left < self.heap.len() {
                let lv = Variable(self.heap[left]);
                let ls = Self::elim_score(lv, occ, gate_pair_credit);
                if ls < smallest_score || (ls == smallest_score && lv.0 < smallest_var.0) {
                    smallest = left;
                    smallest_score = ls;
                    smallest_var = lv;
                }
            }

            if right < self.heap.len() {
                let rv = Variable(self.heap[right]);
                let rs = Self::elim_score(rv, occ, gate_pair_credit);
                if rs < smallest_score || (rs == smallest_score && rv.0 < smallest_var.0) {
                    smallest = right;
                }
            }

            if smallest == p {
                break;
            }

            let smallest_var = Variable(self.heap[smallest]);
            self.heap[p] = smallest_var.0;
            self.heap[smallest] = var.0;
            self.pos[var.index()] = smallest as u32;
            self.pos[smallest_var.index()] = p as u32;
            p = smallest;
        }
    }
}

#[cfg(test)]
#[path = "elim_heap_tests.rs"]
mod tests;
