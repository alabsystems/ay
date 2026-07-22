// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary max-heap for O(log n) variable selection in CP search.
//!
//! Modeled after the VSIDS heap in ay-sat (CaDiCaL's heap.hpp pattern).
//! Each variable has an associated score; the heap extracts the highest-scored
//! unfixed variable in O(log n) time.
//!
//! The heap maintains a position map (`pos[var] -> index in heap`) so that
//! `increase_key` operates in O(log n) by knowing where to start percolation.

/// Invalid position marker (variable not in heap).
const INVALID_POS: u32 = u32::MAX;

/// Binary max-heap of variable indices ordered by externally-supplied scores.
///
/// Design based on ay-sat's VSIDS heap (`crates/ay-sat/src/vsids.rs`).
/// Supports insert, remove-top, increase-key, and re-insert in O(log n).
pub(crate) struct VarHeap {
    /// Binary heap of variable indices. `heap[0]` is the highest-scored.
    heap: Vec<u32>,
    /// Position map: `pos[var]` is the index in `heap`, or `INVALID_POS`.
    pos: Vec<u32>,
}

impl VarHeap {
    /// Create a new empty heap for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            heap: Vec::with_capacity(num_vars),
            pos: vec![INVALID_POS; num_vars],
        }
    }

    /// Create a heap containing all variables `0..num_vars`, ordered by `scores`.
    pub(crate) fn with_all(num_vars: usize, scores: &[f64]) -> Self {
        let mut h = Self::new(num_vars);
        h.reset_with_all(num_vars, scores);
        h
    }

    /// Reset the heap in-place to contain all variables `0..num_vars`,
    /// reusing existing allocations. Avoids the 2× O(n) alloc that
    /// `with_all` incurs when called on every backtrack.
    pub(crate) fn reset_with_all(&mut self, num_vars: usize, scores: &[f64]) {
        self.heap.clear();
        self.heap
            .reserve(num_vars.saturating_sub(self.heap.capacity()));
        for var in 0..num_vars as u32 {
            self.heap.push(var);
        }
        // Resize pos map, reusing capacity
        self.pos.resize(num_vars, INVALID_POS);
        for var in 0..num_vars as u32 {
            self.pos[var as usize] = var;
        }
        // Floyd's build-heap: sift down from the last internal node
        if num_vars > 1 {
            let last_internal = (num_vars / 2).saturating_sub(1);
            for i in (0..=last_internal).rev() {
                self.sift_down(i, scores);
            }
        }
    }

    /// Returns true if the variable is currently in the heap.
    #[inline]
    pub(crate) fn contains(&self, var: u32) -> bool {
        (var as usize) < self.pos.len() && self.pos[var as usize] != INVALID_POS
    }

    /// Insert a variable into the heap. No-op if already present.
    pub(crate) fn insert(&mut self, var: u32, scores: &[f64]) {
        if self.contains(var) {
            return;
        }
        let idx = self.heap.len();
        self.heap.push(var);
        self.pos[var as usize] = idx as u32;
        self.sift_up(idx, scores);
    }

    /// Remove and return the highest-scored variable.
    pub(crate) fn pop(&mut self, scores: &[f64]) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        self.pos[top as usize] = INVALID_POS;
        let last = self.heap.len() - 1;
        if last > 0 {
            self.heap[0] = self.heap[last];
            self.pos[self.heap[0] as usize] = 0;
            self.heap.pop();
            self.sift_down(0, scores);
        } else {
            self.heap.pop();
        }
        Some(top)
    }

    /// Notify the heap that `var`'s score increased. Percolates up.
    pub(crate) fn increase_key(&mut self, var: u32, scores: &[f64]) {
        let p = self.pos[var as usize];
        if p == INVALID_POS {
            return;
        }
        self.sift_up(p as usize, scores);
    }

    /// Peek at the top variable without removing it. Returns `None` if empty.
    #[inline]
    pub(crate) fn peek(&self) -> Option<u32> {
        self.heap.first().copied()
    }

    // ── Internal heap operations ────────────────────────────────────

    fn sift_up(&mut self, mut idx: usize, scores: &[f64]) {
        let var = self.heap[idx];
        let var_score = scores[var as usize];
        while idx > 0 {
            let parent = (idx - 1) / 2;
            let parent_var = self.heap[parent];
            if scores[parent_var as usize] >= var_score {
                break;
            }
            // Move parent down
            self.heap[idx] = parent_var;
            self.pos[parent_var as usize] = idx as u32;
            idx = parent;
        }
        self.heap[idx] = var;
        self.pos[var as usize] = idx as u32;
    }

    fn sift_down(&mut self, mut idx: usize, scores: &[f64]) {
        let len = self.heap.len();
        let var = self.heap[idx];
        let var_score = scores[var as usize];
        loop {
            let left = 2 * idx + 1;
            if left >= len {
                break;
            }
            let right = left + 1;
            // Pick the child with the higher score
            let best_child = if right < len
                && scores[self.heap[right] as usize] > scores[self.heap[left] as usize]
            {
                right
            } else {
                left
            };
            if var_score >= scores[self.heap[best_child] as usize] {
                break;
            }
            // Move child up
            let child_var = self.heap[best_child];
            self.heap[idx] = child_var;
            self.pos[child_var as usize] = idx as u32;
            idx = best_child;
        }
        self.heap[idx] = var;
        self.pos[var as usize] = idx as u32;
    }
}

#[cfg(test)]
impl VarHeap {
    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }
    fn len(&self) -> usize {
        self.heap.len()
    }
    fn grow(&mut self, new_num_vars: usize) {
        if new_num_vars > self.pos.len() {
            self.pos.resize(new_num_vars, INVALID_POS);
        }
    }
}

#[cfg(test)]
#[path = "heap_tests.rs"]
mod tests;
