// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Heap-backed EVSIDS operations.

use super::{batch, INVALID_POS, VSIDS};
use crate::literal::Variable;

impl VSIDS {
    /// Set the random seed for tie-breaking.
    pub(crate) fn set_random_seed(&mut self, seed: u64) {
        self.random_seed = seed;
        if seed != 0 {
            let mut state = seed;
            for i in 0..self.activities.len() {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                self.activities[i] += (state as f64) * 1e-15;
            }
            self.rebuild_heap();
        }
    }

    /// Get the random seed.
    pub(crate) fn random_seed(&self) -> u64 {
        self.random_seed
    }

    /// VSIDS score bump (stable mode): increment activity and sift up in heap.
    /// CaDiCaL `analyze.cpp:105-125`.
    #[inline]
    pub(crate) fn bump_score(&mut self, var: Variable) {
        let idx = var.index();
        debug_assert!(
            idx < self.activities.len(),
            "BUG: bump_score variable {idx} out of range (num_vars={})",
            self.activities.len()
        );

        self.activities[idx] += self.increment;
        if self.activities[idx] > batch::ACTIVITY_RESCALE_LIMIT {
            self.rescale();
        }

        debug_assert!(
            !self.activities[idx].is_nan(),
            "BUG: NaN activity for var {idx} after bump_score"
        );
        debug_assert!(
            self.activities[idx].is_finite(),
            "BUG: infinite activity for var {idx} after bump_score (rescale failed?)"
        );

        if self.heap_pos[idx] != INVALID_POS {
            self.sift_up(self.heap_pos[idx] as usize);
        }
    }

    /// Remove a variable from the heap (when assigned).
    #[inline]
    pub(crate) fn remove_from_heap(&mut self, var: Variable) {
        let idx = var.index();
        let pos = self.heap_pos[idx];
        if pos == INVALID_POS {
            return;
        }
        if pos == 0 {
            let _ = self.pop_heap_root();
            debug_assert_eq!(
                self.heap_pos[idx], INVALID_POS,
                "BUG: var {idx} still in heap_pos after pop_heap_root"
            );
            return;
        }

        let last_idx = self.heap.len() - 1;
        if pos as usize == last_idx {
            self.heap.pop();
            self.heap_pos[idx] = INVALID_POS;
        } else {
            let last_var = self.heap[last_idx] as usize;
            self.heap[pos as usize] = last_var as u32;
            self.heap_pos[last_var] = pos;
            self.heap.pop();
            self.heap_pos[idx] = INVALID_POS;

            self.sift_up(pos as usize);
            self.sift_down(self.heap_pos[last_var] as usize);
        }

        debug_assert_eq!(
            self.heap_pos[idx], INVALID_POS,
            "BUG: var {idx} still in heap_pos after remove_from_heap"
        );
    }

    /// Insert a variable into the heap (when unassigned during backtrack).
    #[inline]
    pub(crate) fn insert_into_heap(&mut self, var: Variable) {
        let idx = var.index();
        if self.heap_pos[idx] != INVALID_POS {
            return;
        }
        self.push_heap(idx as u32);
        debug_assert_ne!(
            self.heap_pos[idx], INVALID_POS,
            "BUG: var {idx} not in heap after insert_into_heap"
        );
    }

    /// Select next variable to branch on using VSIDS (highest activity).
    ///
    /// Performs lazy head pruning for assigned variables.
    #[inline]
    pub(crate) fn pick_branching_variable(&mut self, vals: &[i8]) -> Option<Variable> {
        while let Some(&top) = self.heap.first() {
            if vals[top as usize * 2] == 0 {
                return Some(Variable(top));
            }
            let _ = self.pop_heap_root();
        }
        None
    }

    /// Reset the heap to contain all variables (called on solver reset).
    pub(crate) fn reset_heap(&mut self) {
        let num_vars = self.activities.len();
        self.heap.clear();
        self.heap_pos.fill(INVALID_POS);

        for i in 0..num_vars {
            self.heap.push(i as u32);
            self.heap_pos[i] = i as u32;
        }

        self.rebuild_heap();
    }

    /// Fisher-Yates shuffle of EVSIDS heap scores for stable-mode rephasing.
    pub(crate) fn shuffle_scores(&mut self, rephase_count: u64) {
        let n = self.heap.len();
        if n <= 1 {
            return;
        }

        let mut rng = rephase_count
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        for i in (1..n).rev() {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let j = (rng >> 33) as usize % (i + 1);
            self.heap.swap(i, j);
        }

        self.increment = 1.0;
        for (rank, &var_idx) in self.heap.iter().enumerate() {
            self.activities[var_idx as usize] = rank as f64;
        }

        for (pos, &var_idx) in self.heap.iter().enumerate() {
            self.heap_pos[var_idx as usize] = pos as u32;
        }
        self.rebuild_heap();
    }

    /// Rebuild the heap from scratch (used after bulk activity changes).
    pub(super) fn rebuild_heap(&mut self) {
        if self.heap.len() <= 1 {
            return;
        }
        for i in (0..self.heap.len() / 2).rev() {
            self.sift_down(i);
        }

        #[cfg(debug_assertions)]
        {
            self.debug_assert_heap_property();
            self.debug_assert_heap_pos_consistent();
        }
    }

    /// Remove and return the heap root.
    #[inline]
    fn pop_heap_root(&mut self) -> Option<Variable> {
        let root = self.heap.first().copied()? as usize;
        self.heap_pos[root] = INVALID_POS;
        let tail = self.heap.pop().expect("non-empty heap");
        if !self.heap.is_empty() {
            self.heap[0] = tail;
            self.heap_pos[tail as usize] = 0;
            self.sift_down(0);
            debug_assert_eq!(
                self.heap_pos[self.heap[0] as usize], 0,
                "BUG: heap root position map inconsistent after pop"
            );
        }
        Some(Variable(root as u32))
    }

    /// Push a variable onto the heap and restore heap property.
    #[inline]
    pub(super) fn push_heap(&mut self, var_idx: u32) {
        debug_assert_eq!(
            self.heap_pos[var_idx as usize], INVALID_POS,
            "BUG: push_heap called for var {var_idx} already in heap at pos {}",
            self.heap_pos[var_idx as usize]
        );
        let pos = self.heap.len();
        self.heap.push(var_idx);
        self.heap_pos[var_idx as usize] = pos as u32;
        self.sift_up(pos);
    }

    /// Compare two variables for heap ordering.
    #[inline]
    #[allow(clippy::float_cmp)]
    pub(super) fn var_less(&self, var_a: usize, var_b: usize) -> bool {
        let act_a = self.activities[var_a];
        let act_b = self.activities[var_b];
        act_a > act_b || (act_a == act_b && var_a < var_b)
    }

    /// Sift up an element to restore heap property (after activity increase).
    #[inline]
    pub(super) fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            let var = self.heap[pos] as usize;
            let parent_var = self.heap[parent] as usize;

            if !self.var_less(var, parent_var) {
                break;
            }

            self.heap[pos] = parent_var as u32;
            self.heap[parent] = var as u32;
            self.heap_pos[var] = parent as u32;
            self.heap_pos[parent_var] = pos as u32;
            pos = parent;
        }
    }

    /// Batch EVSIDS score bump: increment activities for all given variables,
    /// then restore heap property using Floyd's O(n) heapify when the number
    /// of in-heap bumped variables meets the threshold. For small batches,
    /// falls back to individual O(log n) sift-ups.
    ///
    /// This is the hot-path optimization for `bump_analyzed_variables()`:
    /// after conflict analysis, k variables are bumped simultaneously.
    /// Individual sift-ups cost k * O(log n); Floyd's heapify costs O(n)
    /// once. For k >= 8, the single heapify wins.
    ///
    /// Reference: Issue #8350 — batch VSIDS/CHB score updates.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn batch_bump_scores(&mut self, vars: &[usize]) {
        if vars.is_empty() {
            return;
        }

        let update =
            batch::apply_evsids_batch(&mut self.activities, &self.heap_pos, vars, self.increment);
        if update.needs_rescale {
            self.rescale();
        }

        #[cfg(debug_assertions)]
        for &idx in vars {
            debug_assert!(
                !self.activities[idx].is_nan(),
                "BUG: NaN activity for var {idx} after batch_bump_scores"
            );
            debug_assert!(
                self.activities[idx].is_finite(),
                "BUG: infinite activity for var {idx} after batch_bump_scores (rescale failed?)"
            );
        }

        self.repair_heap_after_evsids_batch(update, vars);
    }

    /// Restore the heap after a uniform-increment EVSIDS batch bump.
    ///
    /// EVSIDS adds the same `increment` to every bumped variable, but that
    /// uniformity does NOT make naive per-variable `sift_up` correct. When a
    /// bumped node climbs, it pushes every non-bumped ancestor it passes one
    /// slot deeper. A displaced non-bumped ancestor `P` can land directly above
    /// an *already-processed* bumped node `B` whose (also-incremented) activity
    /// now exceeds `P`'s — a child-greater-than-parent violation that the
    /// per-variable sift-up pass never revisits. (This is the bug behind the
    /// `debug_assert_heap_property` panics on the group_soundness suite.)
    ///
    /// Correct sparse repair: the only positions that can violate the heap
    /// property are those on the root-ward paths of the bumped variables (every
    /// node off those paths kept both its parent and its children unchanged).
    /// Those positions form a top-closed region (closed under taking parents),
    /// so a Floyd-style bottom-up `sift_down` over exactly that region — each
    /// position processed once, in decreasing index order — restores the
    /// invariant in O(k log n) sifts rather than an O(n) Floyd rebuild.
    pub(super) fn repair_heap_after_evsids_batch(
        &mut self,
        update: batch::BatchScoreUpdate,
        vars: &[usize],
    ) {
        match update.in_heap {
            0 => {}
            1 => {
                if let batch::BatchHeapRepair::SiftUp { var } = update.repair {
                    let pos = self.heap_pos[var];
                    debug_assert_ne!(
                        pos, INVALID_POS,
                        "BUG: batch repair requested sift for non-heap var {var}"
                    );
                    self.sift_up(pos as usize);
                }
            }
            _ => {
                // Per-variable sift-ups are the permanent default (the former
                // `AY_VSIDS_BATCH_SIFT=0` always-Floyd-rebuild switch is
                // removed); the density heuristic still picks the rebuild
                // when it is cheaper.
                if batch::evsids_batch_prefers_rebuild(update.in_heap, self.heap.len()) {
                    self.rebuild_heap();
                } else {
                    self.sparse_reheapify_affected_paths(vars);
                }
            }
        }

        #[cfg(debug_assertions)]
        if update.in_heap > 0 {
            self.debug_assert_heap_property();
            self.debug_assert_heap_pos_consistent();
        }
    }

    /// Restore the max-heap invariant after a uniform batch bump in O(k log n)
    /// without a full O(n) Floyd rebuild.
    ///
    /// The only edges that a uniform bump can break are those whose child is a
    /// bumped variable, and every such child lies on (the union of) the bumped
    /// variables' root-ward paths to the root. That union is closed under taking
    /// parents, so it is a *top-closed region*, and a Floyd-style bottom-up
    /// `sift_down` (deepest position first) over exactly that region restores the
    /// invariant: when a region position is processed, its in-region child was
    /// already processed (larger index, handled earlier) and its off-region
    /// child subtree contains only unchanged variables and was never disturbed,
    /// so both children are valid heaps and `sift_down` is correct. This both
    /// lifts bumped nodes that must rise and sinks the non-bumped ancestors they
    /// displaced.
    ///
    /// (The previous implementation tried per-variable `sift_up`, claiming the
    /// uniform increment made it order-independent. It is not: a bumped node
    /// climbing pushes a non-bumped ancestor one slot deeper, where it can land
    /// above an already-processed bumped node it no longer dominates, leaving a
    /// child-greater-than-parent violation the sift-up pass never revisits.)
    fn sparse_reheapify_affected_paths(&mut self, vars: &[usize]) {
        // Take the scratch buffers out so we can freely call `&mut self`
        // methods below; swapped back at the end to retain the allocations
        // across conflicts.
        let mut positions = std::mem::take(&mut self.heap_repair_scratch);
        let mut ordered = std::mem::take(&mut self.heap_repair_order);
        positions.clear();

        // Collect the FULL root-ward path (to the root) of every in-heap bumped
        // variable. The union of these paths is closed under taking parents, so
        // it forms a top-closed region: a Floyd-style bottom-up `sift_down`
        // (deepest position first) over exactly this region restores the
        // max-heap invariant. When a region position is processed, both its
        // children subtrees are valid heaps — the in-region child was already
        // processed (deeper, handled earlier), and every off-region subtree
        // contains only non-bumped (unchanged) variables and so was never
        // disturbed by the bump. sift_down both lifts bumped nodes that must
        // rise and sinks displaced non-bumped ancestors.
        //
        // Instruction-shave #4: paths from different variables share all
        // ancestors above their lowest common ancestor, so the old
        // collect-all/sort-desc/dedup pipeline sorted ~k*log(n) entries with
        // heavy duplication near the root. Replaced by (a) per-position visit
        // stamps that terminate each climb at the first already-collected
        // ancestor (every ancestor of a stamped position is itself stamped,
        // by induction over completed climbs), and (b) a counting sort by
        // tree depth instead of a comparison sort.
        //
        // Identity note: the old code processed the region in strictly
        // decreasing position order = depth-descending with decreasing order
        // within each depth. The counting sort below is depth-descending with
        // collection order within each depth. Same-depth positions root
        // disjoint subtrees, so their sift_downs touch disjoint heap/heap_pos
        // slots and commute exactly: the final heap layout is bit-identical
        // (layout is search-observable via `shuffle_scores`).
        self.heap_repair_epoch = self.heap_repair_epoch.wrapping_add(1);
        if self.heap_repair_epoch == 0 {
            self.heap_repair_stamp.fill(0);
            self.heap_repair_epoch = 1;
        }
        let epoch = self.heap_repair_epoch;
        if self.heap_repair_stamp.len() < self.heap.len() {
            self.heap_repair_stamp.resize(self.heap.len(), 0);
        }

        // Depth of position p is ilog2(p+1); u32 positions bound depth < 32.
        let mut depth_counts = [0u32; 32];
        for &idx in vars {
            let pos = self.heap_pos[idx];
            if pos == INVALID_POS {
                continue;
            }
            let mut p = pos as usize;
            loop {
                if self.heap_repair_stamp[p] == epoch {
                    break;
                }
                self.heap_repair_stamp[p] = epoch;
                positions.push(p as u32);
                depth_counts[(p as u32 + 1).ilog2() as usize] += 1;
                if p == 0 {
                    break;
                }
                p = (p - 1) / 2;
            }
        }

        if !positions.is_empty() {
            // Counting-sort scatter: deepest depth bucket first.
            let mut cursor = [0u32; 32];
            let mut acc = 0u32;
            for d in (0..32).rev() {
                cursor[d] = acc;
                acc += depth_counts[d];
            }
            ordered.clear();
            ordered.resize(positions.len(), 0);
            for &p in &positions {
                let d = (p + 1).ilog2() as usize;
                ordered[cursor[d] as usize] = p;
                cursor[d] += 1;
            }
            for &p in &ordered {
                self.sift_down(p as usize);
            }
        }

        positions.clear();
        ordered.clear();
        self.heap_repair_scratch = positions;
        self.heap_repair_order = ordered;
    }

    pub(super) fn repair_heap_after_batch(&mut self, update: batch::BatchScoreUpdate) {
        debug_assert!(
            update.touched >= update.in_heap,
            "BUG: batch update touched {} vars but reports {} in heap",
            update.touched,
            update.in_heap
        );
        debug_assert_eq!(
            update.repair,
            match update.in_heap {
                0 => batch::BatchHeapRepair::None,
                1 => {
                    let var = match update.repair {
                        batch::BatchHeapRepair::SiftUp { var } => var,
                        _ => usize::MAX,
                    };
                    batch::BatchHeapRepair::SiftUp { var }
                }
                _ => batch::BatchHeapRepair::Rebuild,
            },
            "BUG: inconsistent batch heap repair contract"
        );

        match update.repair {
            batch::BatchHeapRepair::None => {}
            batch::BatchHeapRepair::SiftUp { var } => {
                let pos = self.heap_pos[var];
                debug_assert_ne!(
                    pos, INVALID_POS,
                    "BUG: batch repair requested sift for non-heap var {var}"
                );
                self.sift_up(pos as usize);
                // Unlike EVSIDS, a CHB update is an exponential moving
                // average and can lower the score when the new reward is
                // below the previous estimate. Repair both directions: after
                // `sift_up`, the variable's current position is the only
                // place that can still violate a child edge.
                self.sift_down(self.heap_pos[var] as usize);
            }
            batch::BatchHeapRepair::Rebuild => self.rebuild_heap(),
        }

        #[cfg(debug_assertions)]
        if update.in_heap > 0 {
            self.debug_assert_heap_property();
            self.debug_assert_heap_pos_consistent();
        }
    }

    /// Sift down an element to restore heap property.
    #[inline]
    pub(super) fn sift_down(&mut self, mut pos: usize) {
        loop {
            let left = 2 * pos + 1;
            let right = 2 * pos + 2;
            let mut largest = pos;

            let var = self.heap[pos] as usize;

            if left < self.heap.len() {
                let left_var = self.heap[left] as usize;
                if self.var_less(left_var, var) {
                    largest = left;
                }
            }

            if right < self.heap.len() {
                let right_var = self.heap[right] as usize;
                let largest_var = self.heap[largest] as usize;
                if self.var_less(right_var, largest_var) {
                    largest = right;
                }
            }

            if largest == pos {
                break;
            }

            let largest_var = self.heap[largest] as usize;
            self.heap[pos] = largest_var as u32;
            self.heap[largest] = var as u32;
            self.heap_pos[var] = largest as u32;
            self.heap_pos[largest_var] = pos as u32;
            pos = largest;
        }
    }
}
