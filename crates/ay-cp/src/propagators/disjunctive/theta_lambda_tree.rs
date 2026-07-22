// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theta-Lambda tree for O(n log n) edge-finding in disjunctive scheduling.
//!
//! Complete binary tree with leaves sorted by earliest start time (EST).
//! Tracks ECT (earliest completion time) and sum of processing times for:
//! - Theta set: committed tasks
//! - Lambda set: candidate tasks (at most one can be added)
//!
//! Reference: Vilím 2008 "Filtering algorithms for the unary resource constraint"
//! Ported from Pumpkin (MIT): pumpkin-crates/propagators/src/propagators/disjunctive/theta_lambda_tree.rs

use std::cmp::max;

/// A node in the Theta-Lambda tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Node {
    /// Earliest completion time of tasks in Theta at this subtree.
    pub(super) ect: i64,
    /// Sum of processing times of Theta tasks in this subtree.
    pub(super) sum_p: i64,
    /// ECT if one Lambda task can be added to Theta.
    pub(super) ect_bar: i64,
    /// Sum of processing times if one Lambda task can be added.
    pub(super) sum_p_bar: i64,
}

/// Sentinel for "no task" — equivalent to i32::MIN in Pumpkin but for i64.
const EMPTY: i64 = i64::MIN / 2; // Avoid overflow on addition

impl Node {
    fn empty() -> Self {
        Self {
            ect: EMPTY,
            sum_p: 0,
            ect_bar: EMPTY,
            sum_p_bar: 0,
        }
    }

    /// White node: task is in Theta.
    fn white(ect: i64, processing_time: i64) -> Self {
        Self {
            ect,
            sum_p: processing_time,
            ect_bar: ect,
            sum_p_bar: processing_time,
        }
    }

    /// Gray node: task is in Lambda (candidate, not committed).
    fn gray(ect: i64, processing_time: i64) -> Self {
        Self {
            ect: EMPTY,
            sum_p: 0,
            ect_bar: ect,
            sum_p_bar: processing_time,
        }
    }
}

/// Theta-Lambda tree for efficient ECT computation with optional Lambda insertion.
#[derive(Debug, Clone)]
pub(super) struct ThetaLambdaTree {
    pub(super) nodes: Vec<Node>,
    /// Task index → leaf position in sorted order.
    mapping: Vec<usize>,
    /// Leaf position → task index.
    reverse_mapping: Vec<usize>,
    /// Number of internal nodes (leaves start at this index).
    n_internal: usize,
    /// Number of tasks.
    n_tasks: usize,
}

impl ThetaLambdaTree {
    /// Create a new tree for `n` tasks.
    pub(super) fn new(n: usize) -> Self {
        let mut n_internal = 1;
        while n_internal < n {
            n_internal <<= 1;
        }
        Self {
            nodes: Vec::new(),
            mapping: vec![0; n],
            reverse_mapping: vec![0; n],
            n_internal: n_internal.saturating_sub(1).max(1),
            n_tasks: n,
        }
    }

    /// Reset the tree with tasks sorted by EST.
    /// `sorted_indices[i]` = task index of the i-th task by EST.
    pub(super) fn reset(&mut self, sorted_indices: &[usize]) {
        debug_assert_eq!(sorted_indices.len(), self.n_tasks);

        // Build mappings
        for (pos, &task_idx) in sorted_indices.iter().enumerate() {
            self.mapping[task_idx] = pos;
            self.reverse_mapping[pos] = task_idx;
        }

        // Reset all nodes to empty
        let total = 2 * self.n_internal + 1;
        self.nodes.clear();
        self.nodes.resize_with(total, Node::empty);
    }

    /// ECT of the Theta set.
    #[inline]
    pub(super) fn ect(&self) -> i64 {
        self.nodes[0].ect
    }

    /// ECT if one Lambda task is added to Theta.
    #[inline]
    pub(super) fn ect_bar(&self) -> i64 {
        self.nodes[0].ect_bar
    }

    /// Sum of processing times in Theta.
    #[cfg(test)]
    #[inline]
    pub(super) fn sum_p(&self) -> i64 {
        self.nodes[0].sum_p
    }

    /// Add task to Theta (white node).
    pub(super) fn add_to_theta(&mut self, task_idx: usize, ect: i64, processing_time: i64) {
        let pos = self.n_internal + self.mapping[task_idx];
        self.nodes[pos] = Node::white(ect, processing_time);
        self.upheap(pos);
    }

    /// Remove task from Theta.
    pub(super) fn remove_from_theta(&mut self, task_idx: usize) {
        let pos = self.n_internal + self.mapping[task_idx];
        self.nodes[pos] = Node::empty();
        self.upheap(pos);
    }

    /// Add task to Lambda (gray node).
    pub(super) fn add_to_lambda(&mut self, task_idx: usize, ect: i64, processing_time: i64) {
        let pos = self.n_internal + self.mapping[task_idx];
        self.nodes[pos] = Node::gray(ect, processing_time);
        self.upheap(pos);
    }

    /// Remove task from Lambda.
    pub(super) fn remove_from_lambda(&mut self, task_idx: usize) {
        let pos = self.n_internal + self.mapping[task_idx];
        debug_assert_eq!(self.nodes[pos].sum_p, 0, "task should not be in Theta");
        self.nodes[pos] = Node::empty();
        self.upheap(pos);
    }

    /// Find the Lambda task responsible for ect_bar.
    /// Returns `None` if no Lambda task contributes.
    pub(super) fn responsible_ect_bar(&self) -> Option<usize> {
        self.responsible_ect_bar_at(0)
            .map(|pos| self.reverse_mapping[pos - self.n_internal])
    }

    fn responsible_ect_bar_at(&self, pos: usize) -> Option<usize> {
        if self.is_leaf(pos) {
            // A leaf is responsible if it's in Lambda (ect_bar set, ect empty)
            return if self.nodes[pos].ect_bar != EMPTY && self.nodes[pos].ect == EMPTY {
                Some(pos)
            } else {
                None
            };
        }

        let left = 2 * pos + 1;
        let right = 2 * pos + 2;

        // Case 1: ect_bar comes from right child's ect_bar
        if self.nodes[right] != Node::empty()
            && self.nodes[pos].ect_bar == self.nodes[right].ect_bar
        {
            return self.responsible_ect_bar_at(right);
        }

        // Case 2: ect_bar = left.ect + right.sum_p_bar
        if self.nodes[right] != Node::empty()
            && self.nodes[pos].ect_bar == self.nodes[left].ect + self.nodes[right].sum_p_bar
        {
            return self.responsible_p_at(right);
        }

        // Case 3: ect_bar = left.ect_bar + right.sum_p
        if self.nodes[left] != Node::empty()
            && self.nodes[pos].ect_bar == self.nodes[left].ect_bar + self.nodes[right].sum_p
        {
            return self.responsible_ect_bar_at(left);
        }

        None
    }

    fn responsible_p_at(&self, pos: usize) -> Option<usize> {
        if self.is_leaf(pos) {
            return if self.nodes[pos].ect_bar > EMPTY && self.nodes[pos].ect == EMPTY {
                Some(pos)
            } else {
                None
            };
        }

        let left = 2 * pos + 1;
        let right = 2 * pos + 2;

        if self.nodes[left] != Node::empty()
            && self.nodes[pos].sum_p_bar == self.nodes[left].sum_p_bar + self.nodes[right].sum_p
        {
            return self.responsible_p_at(left);
        }

        if self.nodes[right] != Node::empty()
            && self.nodes[pos].sum_p_bar == self.nodes[left].sum_p + self.nodes[right].sum_p_bar
        {
            return self.responsible_p_at(right);
        }

        None
    }

    /// Propagate node updates from leaf to root.
    fn upheap(&mut self, mut idx: usize) {
        while idx != 0 {
            let parent = (idx - 1) / 2;
            let left = 2 * parent + 1;
            let right = 2 * parent + 2;

            // sum_p = left.sum_p + right.sum_p
            self.nodes[parent].sum_p = self.nodes[left].sum_p + self.nodes[right].sum_p;

            // ect = max(right.ect, left.ect + right.sum_p)
            let ect_via_left = self.nodes[left].ect.saturating_add(self.nodes[right].sum_p);
            self.nodes[parent].ect = max(self.nodes[right].ect, ect_via_left);

            // sum_p_bar = max(left.sum_p_bar + right.sum_p, left.sum_p + right.sum_p_bar)
            let sp_left_lambda = self.nodes[left]
                .sum_p_bar
                .saturating_add(self.nodes[right].sum_p);
            let sp_right_lambda = self.nodes[left]
                .sum_p
                .saturating_add(self.nodes[right].sum_p_bar);
            self.nodes[parent].sum_p_bar = max(sp_left_lambda, sp_right_lambda);

            // ect_bar = max(right.ect_bar, left.ect + right.sum_p_bar, left.ect_bar + right.sum_p)
            let ect_bar_right = self.nodes[right].ect_bar;
            let ect_bar_via_right_lambda = self.nodes[left]
                .ect
                .saturating_add(self.nodes[right].sum_p_bar);
            let ect_bar_via_left_lambda = self.nodes[left]
                .ect_bar
                .saturating_add(self.nodes[right].sum_p);
            self.nodes[parent].ect_bar = max(
                ect_bar_right,
                max(ect_bar_via_right_lambda, ect_bar_via_left_lambda),
            );

            idx = parent;
        }
    }

    #[inline]
    fn is_leaf(&self, idx: usize) -> bool {
        2 * idx + 1 >= self.nodes.len()
    }
}

#[cfg(test)]
#[path = "theta_lambda_tree_tests.rs"]
mod tests;
