// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VSIDS variable selection heuristic with heap-based O(log n) selection
//!
//! This module provides VSIDS (Variable State Independent Decaying Sum) with
//! a binary max-heap for efficient variable selection.
//!
//! Design based on CaDiCaL's heap.hpp - maintains position mapping for
//! efficient update operations (decrease-key/increase-key).

#![allow(clippy::upper_case_acronyms)]

use crate::literal::Variable;

use self::bucket_queue::BucketQueue;

mod batch;
pub(crate) mod bucket_queue;
mod heap;
mod vmtf;

/// Invalid heap position marker (variable not in heap)
const INVALID_POS: u32 = u32::MAX;
/// Invalid variable marker (used for VMTF linked-list pointers)
pub(crate) const INVALID_VAR: u32 = u32::MAX;

// CHB constants (Liang et al., SAT 2016, Section 3.2).
const CHB_ALPHA_INIT: f64 = 0.4;
const CHB_ALPHA_MIN: f64 = 0.06;
const CHB_ALPHA_DECAY: f64 = 0.999_995;

/// A/B knob (campaign branching research): `AY_VSIDS_DECAY` overrides the default
/// EVSIDS decay (0.95 = CaDiCaL scorefactor=950). Decay controls how fast variable
/// activity is forgotten — the core "which variables accrue activity" lever the
/// audit identified as the residual Kissat gap. Must be in (0,1); invalid/unset
/// => 0.95. Cached per process (each solver run is a fresh process). The
/// large-formula schedule (solve/mod.rs) still overrides for >1M-clause inputs.
fn default_vsids_decay() -> f64 {
    use std::sync::OnceLock;
    static DECAY: OnceLock<f64> = OnceLock::new();
    *DECAY.get_or_init(|| {
        std::env::var("AY_VSIDS_DECAY")
            .ok()
            .and_then(|s| s.parse::<f64>().ok())
            .filter(|d| *d > 0.0 && *d < 1.0 && d.is_finite())
            .unwrap_or(0.95)
    })
}

/// VSIDS activity-based variable selection with heap
#[derive(Debug, Clone)]
pub(crate) struct VSIDS {
    /// Activity scores for each variable
    activities: Vec<f64>,
    /// Activity increment (grows on each decay)
    increment: f64,
    /// Decay factor
    decay: f64,
    /// Random seed for tie-breaking (affects initial perturbation)
    random_seed: u64,
    /// Bump order for each variable - higher means more recently bumped (VMTF)
    bump_order: Vec<u64>,
    /// Variables explicitly buried at the oldest end of the VMTF queue.
    ///
    /// Factorization uses zero activity to hide fresh extension variables from
    /// decisions. Focused mode needs an explicit guard as well because
    /// backtracking calls `vmtf_on_unassign`, which would otherwise move a
    /// buried variable back to the cursor.
    buried: Vec<bool>,
    /// Counter for bump ordering
    bump_counter: u64,

    // Heap data structures
    /// Binary max-heap of variable indices (ordered by activity)
    heap: Vec<u32>,
    /// Position of each variable in heap (INVALID_POS if not in heap)
    heap_pos: Vec<u32>,
    /// Reusable scratch buffer for sparse heap repair after EVSIDS batch bumps.
    /// Holds the union of root-ward path positions of the bumped variables;
    /// kept across conflicts to avoid per-conflict allocation.
    heap_repair_scratch: Vec<u32>,
    /// Second scratch buffer for the depth-bucketed (counting-sort) ordering
    /// of `heap_repair_scratch` positions (instruction-shave #4). Kept across
    /// conflicts to avoid per-conflict allocation.
    heap_repair_order: Vec<u32>,
    /// Per-heap-position visit stamps for duplicate-free root-ward path
    /// collection in `sparse_reheapify_affected_paths` (instruction-shave #4).
    /// `heap_repair_stamp[pos] == heap_repair_epoch` marks `pos` as already
    /// collected for the current repair. Lazily sized to `heap.len()`.
    heap_repair_stamp: Vec<u32>,
    /// Current epoch for `heap_repair_stamp`; incremented per repair so the
    /// stamp array never needs clearing (reset on wrap-around).
    heap_repair_epoch: u32,

    // CHB scoring (Liang et al., SAT 2016)
    /// Per-variable Q-scores for CHB heuristic.
    /// `None` until the first CHB bump — avoids 8 bytes/var allocation in
    /// LegacyCoupled mode where CHB is never used (#8121).
    chb_scores: Option<Vec<f64>>,
    /// Conflict number at which each variable was last bumped by CHB.
    /// `None` until the first CHB bump (lazy, same as `chb_scores`).
    chb_last_conflict: Option<Vec<u64>>,
    /// Current CHB learning rate.
    pub(crate) chb_alpha: f64,
    /// Global conflict counter for CHB reward computation.
    pub(crate) chb_conflicts: u64,
    /// Whether activities currently holds CHB scores (swapped for heap use).
    chb_loaded: bool,

    // VMTF decision queue (focused mode)
    /// Previous variable in bump-order list (towards older variables)
    vmtf_prev: Vec<u32>,
    /// Next variable in bump-order list (towards more recent variables)
    vmtf_next: Vec<u32>,
    /// Oldest variable in the queue
    vmtf_first: u32,
    /// Most recently bumped variable in the queue (front)
    vmtf_last: u32,
    /// Most recently bumped *unassigned* variable (used as starting point)
    vmtf_unassigned: u32,
    /// Bump timestamp of `vmtf_unassigned` at last update
    vmtf_unassigned_bumped: u64,
    /// Whether stable-mode bumps have deferred VMTF linked-list updates.
    /// When true, bump_order values are current but the doubly-linked list
    /// (vmtf_prev/vmtf_next) is stale. Must be resolved via
    /// `rebuild_vmtf_from_bump_order()` before arena compaction or mode switch.
    vmtf_deferred: bool,

    // Bucket queue for IC3 domain-restricted queries (#8476)
    /// O(1) amortized variable selection queue for small domain-restricted
    /// queries. Built on `set_domain` when domain size is below a threshold.
    /// After 10 restarts, the solver switches back to the standard heap.
    bucket_queue: BucketQueue,
}

impl VSIDS {
    // ── Debug assertion helpers ──────────────────────────────────────

    /// O(n) check: every heap entry has a consistent position map entry and vice versa.
    #[cfg(debug_assertions)]
    fn debug_assert_heap_pos_consistent(&self) {
        for (pos, &var) in self.heap.iter().enumerate() {
            assert_eq!(
                self.heap_pos[var as usize], pos as u32,
                "BUG: heap_pos[{var}] = {} but heap[{pos}] = {var}",
                self.heap_pos[var as usize]
            );
        }
        for (var, &pos) in self.heap_pos.iter().enumerate() {
            if pos != INVALID_POS {
                assert!(
                    (pos as usize) < self.heap.len(),
                    "BUG: heap_pos[{var}] = {pos} but heap.len() = {}",
                    self.heap.len()
                );
                assert_eq!(
                    self.heap[pos as usize], var as u32,
                    "BUG: heap_pos[{var}] = {pos} but heap[{pos}] = {}",
                    self.heap[pos as usize]
                );
            }
        }
    }

    /// O(n) check: max-heap property holds for every parent-child pair.
    #[cfg(debug_assertions)]
    fn debug_assert_heap_property(&self) {
        for pos in 1..self.heap.len() {
            let parent = (pos - 1) / 2;
            let var = self.heap[pos] as usize;
            let parent_var = self.heap[parent] as usize;
            assert!(
                !self.var_less(var, parent_var),
                "BUG: heap property violated at pos {pos}: var {var} (act={}) > \
                 parent var {parent_var} (act={}) at pos {parent}",
                self.activities[var],
                self.activities[parent_var]
            );
        }
    }

    /// O(n) check: VMTF doubly-linked list is consistent (no cycles, correct
    /// forward/backward pointers, first/last sentinel values).
    #[cfg(debug_assertions)]
    fn debug_assert_vmtf_consistent(&self) {
        if self.vmtf_first == INVALID_VAR {
            assert_eq!(
                self.vmtf_last, INVALID_VAR,
                "BUG: vmtf_first is INVALID but vmtf_last = {}",
                self.vmtf_last
            );
            return;
        }
        assert_eq!(
            self.vmtf_prev[self.vmtf_first as usize], INVALID_VAR,
            "BUG: vmtf_first ({}) has non-INVALID prev = {}",
            self.vmtf_first, self.vmtf_prev[self.vmtf_first as usize]
        );
        assert_eq!(
            self.vmtf_next[self.vmtf_last as usize], INVALID_VAR,
            "BUG: vmtf_last ({}) has non-INVALID next = {}",
            self.vmtf_last, self.vmtf_next[self.vmtf_last as usize]
        );
        let mut count = 0usize;
        let mut cur = self.vmtf_first;
        while cur != INVALID_VAR {
            count += 1;
            assert!(
                count <= self.activities.len(),
                "BUG: VMTF cycle detected after {count} nodes (num_vars={})",
                self.activities.len()
            );
            let next = self.vmtf_next[cur as usize];
            if next != INVALID_VAR {
                assert_eq!(
                    self.vmtf_prev[next as usize], cur,
                    "BUG: vmtf_next[{cur}]={next} but vmtf_prev[{next}]={}",
                    self.vmtf_prev[next as usize]
                );
            } else {
                assert_eq!(
                    cur, self.vmtf_last,
                    "BUG: VMTF list ends at {cur} but vmtf_last = {}",
                    self.vmtf_last
                );
            }
            cur = next;
        }
    }

    /// Create a new VSIDS with n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        // Initialize bump_order so variables with lower indices are tried first initially
        // (same as CaDiCaL's init_queue)
        let mut bump_order = Vec::with_capacity(num_vars);
        for i in 0..num_vars {
            // Lower index = higher initial bump order (will be picked first)
            bump_order.push((num_vars - i) as u64);
        }

        // Initialize heap with all variables (all unassigned initially)
        // Variables are ordered by index initially (lower index = higher priority)
        let mut heap = Vec::with_capacity(num_vars);
        let mut heap_pos = vec![INVALID_POS; num_vars];
        for (i, pos) in heap_pos.iter_mut().enumerate().take(num_vars) {
            heap.push(i as u32);
            *pos = i as u32;
        }

        // Note: With zero initial activities, heap order doesn't matter much
        // The heap will reorganize as variables get bumped during solving

        // Initialize VMTF queue in index order, preferring smaller indices first.
        // The queue is a doubly linked list ordered by bump-recency where
        // `vmtf_last` is the most recently bumped (front).
        //
        // To pick smaller indices first initially, we build the initial order as:
        // (num_vars - 1) (oldest) -> ... -> 1 -> 0 (newest).
        let (vmtf_prev, vmtf_next, vmtf_first, vmtf_last, vmtf_unassigned, vmtf_unassigned_bumped) =
            if num_vars == 0 {
                (
                    Vec::new(),
                    Vec::new(),
                    INVALID_VAR,
                    INVALID_VAR,
                    INVALID_VAR,
                    0u64,
                )
            } else {
                let mut vmtf_prev = vec![INVALID_VAR; num_vars];
                let mut vmtf_next = vec![INVALID_VAR; num_vars];
                for i in 0..num_vars {
                    vmtf_prev[i] = if i + 1 < num_vars {
                        (i + 1) as u32
                    } else {
                        INVALID_VAR
                    };
                    vmtf_next[i] = if i > 0 { (i - 1) as u32 } else { INVALID_VAR };
                }
                let vmtf_first = (num_vars as u32) - 1;
                let vmtf_last = 0;
                let vmtf_unassigned = vmtf_last;
                let vmtf_unassigned_bumped = bump_order[vmtf_unassigned as usize];
                (
                    vmtf_prev,
                    vmtf_next,
                    vmtf_first,
                    vmtf_last,
                    vmtf_unassigned,
                    vmtf_unassigned_bumped,
                )
            };

        Self {
            activities: vec![0.0; num_vars],
            increment: 1.0,
            decay: default_vsids_decay(),
            random_seed: 0,
            bump_order,
            buried: vec![false; num_vars],
            bump_counter: num_vars as u64 + 1,
            heap,
            heap_pos,
            heap_repair_scratch: Vec::new(),
            heap_repair_order: Vec::new(),
            heap_repair_stamp: Vec::new(),
            heap_repair_epoch: 0,
            chb_scores: None,
            chb_last_conflict: None,
            chb_alpha: CHB_ALPHA_INIT,
            chb_conflicts: 0,
            chb_loaded: false,
            vmtf_prev,
            vmtf_next,
            vmtf_first,
            vmtf_last,
            vmtf_unassigned,
            vmtf_unassigned_bumped,
            vmtf_deferred: false,
            bucket_queue: BucketQueue::new(),
        }
    }

    /// Ensure VSIDS has storage for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let old_len = self.activities.len();
        if old_len < num_vars {
            self.activities.resize(num_vars, 0.0);
            self.heap_pos.resize(num_vars, INVALID_POS);
            self.vmtf_prev.resize(num_vars, INVALID_VAR);
            self.vmtf_next.resize(num_vars, INVALID_VAR);
            self.buried.resize(num_vars, false);
            if let Some(ref mut scores) = self.chb_scores {
                scores.resize(num_vars, 0.0);
            }
            if let Some(ref mut last) = self.chb_last_conflict {
                last.resize(num_vars, 0);
            }

            // New variables get increasing bump order
            for _ in old_len..num_vars {
                self.bump_order.push(self.bump_counter);
                self.bump_counter += 1;
            }

            // Ensure bucket queue can track the new variables.
            self.bucket_queue.ensure_capacity(num_vars);

            // Add new variables to heap (they are unassigned)
            for i in old_len..num_vars {
                self.push_heap(i as u32);
            }

            // Add new variables to the VMTF queue (most recent/front).
            for i in old_len..num_vars {
                self.vmtf_enqueue(i as u32);
                // New variables are unassigned initially, so treat them as best candidate.
                self.vmtf_unassigned = i as u32;
                self.vmtf_unassigned_bumped = self.bump_order[i];
            }

            #[cfg(debug_assertions)]
            {
                self.debug_assert_heap_pos_consistent();
                self.debug_assert_vmtf_consistent();
            }
        }
    }

    /// Bump the activity of a variable.
    ///
    /// Updates both the VSIDS activity (for stable mode) and the
    /// VMTF bump order (for focused mode). The `vals` slice is needed
    /// to update the VMTF unassigned cursor when bumping an unassigned
    /// variable to the front of the queue.
    ///
    /// Reference: CaDiCaL `analyze.cpp:54-64` — after bumping, if the
    /// variable is unassigned, update `queue.unassigned` to point to it.
    /// Without this, the VMTF search cursor can get stuck behind the
    /// bumped variable, causing `pick_branching_variable_vmtf` to miss
    /// unassigned variables and falsely declare SAT.
    /// Bump a variable's priority in the active heuristic, always maintaining
    /// the VMTF queue for arena compaction.
    ///
    /// CaDiCaL `bump.cpp`: `bump_variable_score` (EVSIDS heap) runs only in
    /// stable mode, but `bump_variable_queue` (VMTF linked list) runs
    /// unconditionally in both modes. This keeps the VMTF queue current so
    /// arena locality compaction can use it as a clause visit order regardless
    /// of the active decision heuristic.
    ///
    /// Optimization (#7998): in stable mode, only update the bump_order counter
    /// (O(1) write) and defer the expensive linked-list dequeue+enqueue. The
    /// VMTF linked-list order is only consumed by arena compaction (infrequent)
    /// and focused-mode decisions (not active in stable mode). Arena compaction
    /// calls `rebuild_vmtf_from_bump_order()` to restore list consistency.
    /// This eliminates ~5 scattered cache-line writes per analyzed variable
    /// per conflict in stable mode.
    #[inline]
    pub(crate) fn bump(&mut self, var: Variable, vals: &[i8], stable: bool) {
        if stable {
            self.bump_score(var);
            // Lightweight VMTF maintenance: update bump_order + counter (2 writes)
            // but skip linked-list manipulation. The deferred flag signals that
            // the list needs rebuilding before arena compaction or mode switch.
            let idx = var.index();
            self.bump_order[idx] = self.bump_counter;
            self.bump_counter += 1;
            self.vmtf_deferred = true;
            // Update unassigned cursor if this variable is unassigned and has
            // a newer bump_order. Needed for trail reuse computation in
            // compute_reuse_trail_level (restart.rs).
            if vals[idx * 2] == 0 {
                self.vmtf_unassigned = idx as u32;
                self.vmtf_unassigned_bumped = self.bump_order[idx];
            }
        } else {
            self.bump_queue(var, vals);
        }
    }

    /// Batch bump for multiple variables after conflict analysis.
    ///
    /// In stable mode (EVSIDS), increments all activities in one pass and
    /// restores the heap with Floyd's O(n) heapify when the batch is large
    /// (>= 8 in-heap variables), instead of k individual O(log n) sift-ups.
    /// Also updates VMTF bump_order counters and the unassigned cursor.
    ///
    /// In focused mode (VMTF), delegates to individual `bump_queue` calls
    /// since the VMTF linked-list insertion order matters (variables must be
    /// inserted in the caller-supplied order for correct recency ranking).
    ///
    /// Reference: Issue #8350 — batch VSIDS/CHB score updates.
    pub(crate) fn batch_bump(&mut self, vars: &[usize], vals: &[i8], stable: bool) {
        if vars.is_empty() {
            return;
        }

        if stable {
            // Fused single pass (instruction-shave #4): the former Phase 1
            // (EVSIDS score increment + in-heap census, previously the
            // `apply_evsids_batch` kernel via `batch_bump_scores`) and
            // Phase 2 (VMTF bump_order counters + unassigned cursor) touched
            // disjoint state and re-iterated `vars` twice. One pass performs
            // exactly the same writes in the same relative per-array order,
            // so the final state is bit-identical to the two-pass version.
            let mut in_heap = 0usize;
            let mut first_in_heap = 0usize;
            let mut needs_rescale = false;

            for &idx in vars {
                debug_assert!(
                    idx < self.activities.len() && idx < self.bump_order.len(),
                    "BUG: batch_bump variable {idx} out of range (num_vars={})",
                    self.activities.len()
                );

                // EVSIDS score update (matches apply_evsids_batch semantics,
                // including repeated application for duplicate variables).
                self.activities[idx] += self.increment;
                needs_rescale |= self.activities[idx] > batch::ACTIVITY_RESCALE_LIMIT;
                if self.heap_pos[idx] != INVALID_POS {
                    if in_heap == 0 {
                        first_in_heap = idx;
                    }
                    in_heap += 1;
                }

                // Deferred VMTF maintenance: bump_order + cursor only
                // (O(1) writes, no linked-list manipulation; #7998).
                self.bump_order[idx] = self.bump_counter;
                self.bump_counter += 1;
                if vals[idx * 2] == 0 {
                    self.vmtf_unassigned = idx as u32;
                    self.vmtf_unassigned_bumped = self.bump_order[idx];
                }
            }

            let update =
                batch::BatchScoreUpdate::new(vars.len(), in_heap, first_in_heap, needs_rescale);
            if update.needs_rescale {
                self.rescale();
            }

            #[cfg(debug_assertions)]
            for &idx in vars {
                debug_assert!(
                    !self.activities[idx].is_nan(),
                    "BUG: NaN activity for var {idx} after batch_bump"
                );
                debug_assert!(
                    self.activities[idx].is_finite(),
                    "BUG: infinite activity for var {idx} after batch_bump (rescale failed?)"
                );
            }

            self.repair_heap_after_evsids_batch(update, vars);
            self.vmtf_deferred = true;
        } else {
            // VMTF mode: insertion order matters for recency ranking.
            // Caller must provide variables sorted by ascending bump_order.
            for &idx in vars {
                self.bump_queue(Variable(idx as u32), vals);
            }
        }
    }

    /// VMTF batch bump from pre-sorted `(old bump_order, var index)` pairs.
    ///
    /// Identical to `batch_bump(vars, vals, false)` on the projected index
    /// sequence, but consumes the caller's sort buffer directly instead of
    /// requiring a second copy into a plain index buffer (instruction-shave
    /// #4; the copy was pure overhead on the focused-mode conflict path).
    pub(crate) fn batch_bump_queue_sorted(&mut self, sorted: &[(u64, usize)], vals: &[i8]) {
        for &(_, idx) in sorted {
            self.bump_queue(Variable(idx as u32), vals);
        }
    }

    /// Lightweight VMTF bump_order-only update for CHB mode.
    ///
    /// When CHB is the active heuristic (MabUcb1 in stable mode), the main
    /// `bump()` path is not called. This method keeps `bump_order` current
    /// so that arena compaction and mode-switch VMTF rebuilds use accurate
    /// variable recency data. Matches the deferred stable-mode path in
    /// `bump()`: O(1) writes, no linked-list manipulation.
    #[inline]
    pub(crate) fn bump_vmtf_order_only(&mut self, var: Variable, vals: &[i8]) {
        let idx = var.index();
        self.bump_order[idx] = self.bump_counter;
        self.bump_counter += 1;
        self.vmtf_deferred = true;
        if vals[idx * 2] == 0 {
            self.vmtf_unassigned = idx as u32;
            self.vmtf_unassigned_bumped = self.bump_order[idx];
        }
    }

    /// Whether stable-mode bumps have deferred VMTF linked-list updates.
    ///
    /// When true, the VMTF doubly-linked list is stale and must be rebuilt
    /// via `rebuild_vmtf_from_bump_order()` before arena compaction or
    /// mode switch to focused mode.
    #[inline]
    pub(crate) fn vmtf_is_deferred(&self) -> bool {
        self.vmtf_deferred
    }

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

    /// Decay all activities
    #[inline]
    pub(crate) fn decay(&mut self) {
        self.increment /= self.decay;
        // Proactive rescale: if increment exceeds the activity threshold,
        // rescale everything to prevent overflow to infinity (#5580).
        // Without this, decay() can push increment past f64::MAX before
        // bump() triggers the activity-based rescale check.
        if self.increment > 1e100 {
            self.rescale();
        }
        debug_assert!(
            self.increment.is_finite() && self.increment > 0.0,
            "BUG: increment became non-finite or non-positive after decay: {}",
            self.increment
        );
    }

    /// Set the VSIDS decay factor (#8655).
    ///
    /// The decay factor controls how quickly old activity scores lose
    /// influence relative to new bumps. A higher decay (e.g., 0.99)
    /// preserves more historical information; a lower decay (e.g., 0.95)
    /// makes recent conflicts dominate more quickly.
    ///
    /// Must be in (0, 1). The standard CaDiCaL default is 0.95
    /// (scorefactor=950, i.e., 1000/950 = 1/0.95).
    #[inline]
    pub(crate) fn set_decay(&mut self, decay: f64) {
        debug_assert!(
            decay > 0.0 && decay < 1.0 && decay.is_finite(),
            "BUG: set_decay called with invalid decay factor: {decay}"
        );
        self.decay = decay;
    }

    /// Get activity of a variable
    #[inline]
    pub(crate) fn activity(&self, var: Variable) -> f64 {
        self.activities[var.index()]
    }

    /// Get the current VSIDS activity increment.
    ///
    /// Used by `reset_search_state` to assign competitive activity scores
    /// to variables reactivated after BVE elimination (#7981).
    #[inline]
    pub(crate) fn current_increment(&self) -> f64 {
        self.increment
    }

    /// Set activity of a variable and update heap position.
    ///
    /// Zero activity has an extra meaning for factorization: the variable is
    /// also buried at the oldest end of the VMTF queue so focused-mode search
    /// does not immediately branch on fresh extension variables. This matches
    /// the intent of CaDiCaL's `queue.bury()` for factoring fresh vars
    /// (factor.cpp:769-839).
    #[inline]
    pub(crate) fn set_activity(&mut self, var: Variable, activity: f64) {
        let idx = var.index();
        debug_assert!(idx < self.activities.len());
        let old = self.activities[idx];
        self.activities[idx] = activity;
        if self.heap_pos[idx] != INVALID_POS {
            let pos = self.heap_pos[idx] as usize;
            if activity > old {
                self.sift_up(pos);
            } else if activity < old {
                self.sift_down(pos);
            }
        }

        if activity == 0.0 {
            self.buried[idx] = true;
            self.vmtf_bury_to_oldest(var);
            if self.vmtf_unassigned == idx as u32 {
                self.reset_vmtf_unassigned();
            }
        } else {
            self.buried[idx] = false;
        }
    }

    /// Rescale all activities to prevent overflow
    fn rescale(&mut self) {
        for act in &mut self.activities {
            *act *= 1e-100;
        }
        self.increment *= 1e-100;
        // Multiplying by 1e-100 can flush distinct small activities to the SAME
        // value (or to 0), collapsing the strict order the heap's tie-break
        // (by variable index) assumed. That leaves a stale child-before-parent
        // ordering the heap never repairs. Rescale is already O(n) and rare, so
        // re-establish the invariant with a full heapify here. (Previously this
        // was masked by the batch-bump path always Floyd-rebuilding; the sparse
        // batch repair only touches bumped paths and so surfaced the latent bug.)
        self.rebuild_heap();

        debug_assert!(
            self.increment.is_finite() && self.increment > 0.0,
            "BUG: increment is {}, expected positive finite after rescale",
            self.increment
        );
        debug_assert!(
            self.activities.iter().all(|a| a.is_finite()),
            "BUG: non-finite activity found after rescale"
        );
    }

    /// Multiply all VSIDS activity scores by `factor` (#8399).
    ///
    /// Used by `continue_solving_with_extension_raw` to decay stale VSIDS
    /// scores when preserving heuristic state across split-loop iterations.
    /// A factor of 0.5 halves all scores while keeping the bump increment
    /// unchanged. This makes fresh conflict bumps more influential relative
    /// to historical scores, steering the search away from the previous
    /// iteration's trajectory.
    ///
    /// The increment is NOT scaled: the goal is to shift priority toward
    /// variables active in NEW conflicts (post-decay). If we scaled the
    /// increment too, the relative influence of old vs new bumps would be
    /// unchanged, defeating the purpose.
    ///
    /// Preserves the *mathematical* order of the scores, but the heap is
    /// re-heapified afterwards (see the body: scaling is not strictly
    /// monotone in IEEE-754).
    pub(crate) fn decay_all_scores(&mut self, factor: f64) {
        debug_assert!(factor > 0.0 && factor <= 1.0 && factor.is_finite());
        for act in &mut self.activities {
            *act *= factor;
        }
        // Note: increment is NOT scaled. After decay, the next bump adds
        // `increment` to a halved score, effectively 2x the relative boost.
        // This is intentional: new conflicts should dominate stale scores.

        // Scaling is monotone but NOT strictly monotone: distinct tiny
        // activities can round to the SAME value without ever reaching
        // exactly 0.0 (e.g. with factor 0.5, both 5*d and 4*d collapse to
        // 2*d, where d = 2^-1074 is the smallest positive denormal). The heap
        // breaks ties by variable index (`var_less`), so a collapse can
        // invert the relative order of a parent/child pair that was strictly
        // ordered before scaling, leaving a stale arrangement the heap never
        // repairs (debug builds then panic in `debug_assert_heap_property`).
        // The old guard here rebuilt only on underflow to exactly 0.0, which
        // misses the collapse-to-a-shared-nonzero case entirely. `rescale`
        // (the 1e-100 overflow path) and `rescale_for_reorder` already
        // re-heapify unconditionally for exactly this reason — mirror them.
        // This path is rare (split-loop iteration boundaries) and the scan
        // above is already O(n), so the Floyd rebuild is free at this
        // frequency. Heuristic-only: it restores the decision-order structure
        // and can never change a SAT/UNSAT result.
        self.rebuild_heap();
    }

    /// Get the bump order for a variable (for trail reuse comparison)
    #[inline]
    pub(crate) fn bump_order(&self, var: Variable) -> u64 {
        self.bump_order[var.index()]
    }

    /// Notify the VMTF queue that `var` became unassigned (during backtracking).
    ///
    /// This updates the "unassigned cursor" if this variable is more recently bumped
    /// than the current cursor (CaDiCaL's `update_queue_unassigned` logic).
    #[inline]
    pub(crate) fn vmtf_on_unassign(&mut self, var: Variable) {
        let idx = var.index();
        if self.buried[idx] {
            return;
        }
        let order = self.bump_order[idx];
        if self.vmtf_unassigned == INVALID_VAR || order > self.vmtf_unassigned_bumped {
            self.vmtf_unassigned = idx as u32;
            self.vmtf_unassigned_bumped = order;
        }
    }

    /// Reset VMTF cursor assuming all variables are unassigned.
    #[inline]
    pub(crate) fn reset_vmtf_unassigned(&mut self) {
        if self.vmtf_last == INVALID_VAR {
            self.vmtf_unassigned = INVALID_VAR;
            self.vmtf_unassigned_bumped = 0;
        } else {
            self.vmtf_unassigned = self.vmtf_last;
            self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_unassigned as usize];
        }
    }

    // -- VMTF queue accessors for arena compaction --

    /// Most recently bumped variable (front of VMTF queue).
    /// Returns `INVALID_VAR` if the queue is empty.
    #[inline]
    pub(crate) fn vmtf_last(&self) -> u32 {
        self.vmtf_last
    }

    /// Previous variable in VMTF bump order (towards less recently bumped).
    /// Returns `INVALID_VAR` for end-of-list.
    #[inline]
    pub(crate) fn vmtf_prev_of(&self, var: u32) -> u32 {
        self.vmtf_prev[var as usize]
    }

    // -- Reorder support --

    /// Rebuild the VMTF queue in the order given by `vars_ascending`.
    ///
    /// Variables are moved to the front of the queue in the order they appear in
    /// the slice: the last variable in the slice ends up as `vmtf_last` (the most
    /// recently bumped, searched first). Callers should pass variables sorted by
    /// ascending score so the highest-score variables end up at the front.
    ///
    /// Reference: Kissat `reorder.c:162-173` — iterates sorted variables
    /// calling `move_to_front` so the last-moved (highest weight) is at front.
    ///
    /// `vals` is needed to update the VMTF unassigned cursor when bumping
    /// unassigned variables.
    pub(crate) fn reorder_vmtf_queue(&mut self, vars_ascending: &[u32], vals: &[i8]) {
        for &v in vars_ascending {
            let var = Variable(v);
            self.bump_queue(var, vals);
        }

        #[cfg(debug_assertions)]
        self.debug_assert_vmtf_consistent();
    }

    /// Rescale EVSIDS activities to a normalized range before reorder weight
    /// addition (Kissat `reorder.c:180` — `kissat_rescale_scores`).
    ///
    /// After many VSIDS bumps, activities can grow to 1e100. Adding clause
    /// weights (0.0–1.0 range) to such large values is a no-op in floating
    /// point due to precision loss. Rescaling normalizes activities so that
    /// clause-weighted adjustments are meaningful.
    pub(crate) fn rescale_for_reorder(&mut self) {
        // Find the maximum activity to determine the scale factor.
        let max_act = self.activities.iter().copied().fold(0.0_f64, f64::max);
        if max_act > 1.0 {
            let scale = 1.0 / max_act;
            for act in &mut self.activities {
                *act *= scale;
            }
            self.increment *= scale;
            // Scaling is monotone but NOT strictly monotone: distinct tiny
            // activities can round to the SAME value (denormal collapse)
            // without reaching exactly 0.0. The heap's tie-break is by
            // variable index (`var_less`), so a collapse can invert the
            // relative order of a parent/child pair that was strictly
            // ordered before scaling, leaving a stale arrangement the heap
            // never repairs (debug builds panic in
            // debug_assert_heap_property; hit by the model-checker-consumer looping_id
            // IC3 lane after heavily-decayed activities). `rescale` (the
            // 1e-100 overflow path) already re-heapifies unconditionally
            // for exactly this reason — mirror it. This path is rare
            // (every INCREMENTAL_VSIDS_RESCALE_INTERVAL solves / stable
            // reorder) and the scan above is already O(n).
            self.rebuild_heap();
        }
    }

    /// Add a weight to an EVSIDS activity score without going through the
    /// normal bump path. Used by stable-mode reorder (Kissat `reorder.c:176-196`)
    /// to fold clause weights into heap scores.
    pub(crate) fn add_to_activity(&mut self, var: Variable, weight: f64) {
        let idx = var.index();
        debug_assert!(idx < self.activities.len());
        let old = self.activities[idx];
        let new = old + weight;
        self.activities[idx] = new;
        if self.heap_pos[idx] != INVALID_POS {
            let pos = self.heap_pos[idx] as usize;
            if new > old {
                self.sift_up(pos);
            }
        }
    }

    // -- CHB methods --

    /// Lazily allocate CHB score arrays on first use.
    ///
    /// In LegacyCoupled mode (the default), CHB is never used and these
    /// arrays stay `None`, saving 16 bytes per variable (#8121).
    fn ensure_chb_arrays(&mut self) {
        let n = self.activities.len();
        if self.chb_scores.is_none() {
            self.chb_scores = Some(vec![0.0; n]);
            self.chb_last_conflict = Some(vec![0; n]);
        }
    }

    /// Read a variable CHB Q-score (respects swap state).
    #[cfg(test)]
    pub(crate) fn chb_score(&self, var: Variable) -> f64 {
        if self.chb_loaded {
            self.activities[var.index()]
        } else {
            self.chb_scores.as_ref().map_or(0.0, |s| s[var.index()])
        }
    }

    /// Bump a variable CHB score using the exponential recency reward.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn chb_bump(&mut self, var: Variable) {
        self.chb_bump_batch(&[var.index()]);
    }

    /// Batch-bump CHB Q-scores for analyzed variables.
    ///
    /// This preserves scalar `chb_bump()` semantics, including duplicate
    /// variables, while doing a single heap repair when CHB scores are loaded.
    pub(crate) fn chb_bump_batch(&mut self, vars: &[usize]) {
        if vars.is_empty() {
            return;
        }

        self.ensure_chb_arrays();
        let last_conflict = self.chb_last_conflict.as_mut().expect("ensured");
        let update = if self.chb_loaded {
            batch::apply_chb_batch(
                &mut self.activities,
                last_conflict,
                Some(&self.heap_pos),
                vars,
                self.chb_conflicts,
                self.chb_alpha,
            )
        } else {
            let scores = self.chb_scores.as_mut().expect("ensured");
            batch::apply_chb_batch(
                scores,
                last_conflict,
                None,
                vars,
                self.chb_conflicts,
                self.chb_alpha,
            )
        };
        self.repair_heap_after_batch(update);
    }

    /// Advance the CHB conflict counter and decay the learning rate.
    #[inline]
    pub(crate) fn chb_on_conflict(&mut self) {
        self.chb_conflicts += 1;
        self.chb_alpha = (self.chb_alpha * CHB_ALPHA_DECAY).max(CHB_ALPHA_MIN);
    }

    /// Swap EVSIDS activities and CHB scores so the heap orders by CHB.
    pub(crate) fn swap_chb_scores(&mut self) {
        self.ensure_chb_arrays();
        let scores = self.chb_scores.as_mut().expect("ensured");
        std::mem::swap(&mut self.activities, scores);
        self.chb_loaded = !self.chb_loaded;
        self.rebuild_heap();
    }

    /// Reset CHB state (used on search reset / incremental solve).
    pub(crate) fn chb_reset(&mut self) {
        if self.chb_loaded {
            let scores = self
                .chb_scores
                .as_mut()
                .expect("chb_loaded implies allocated");
            std::mem::swap(&mut self.activities, scores);
            self.chb_loaded = false;
        }
        if let Some(ref mut scores) = self.chb_scores {
            scores.fill(0.0);
        }
        if let Some(ref mut last) = self.chb_last_conflict {
            last.fill(0);
        }
        self.chb_alpha = CHB_ALPHA_INIT;
        self.chb_conflicts = 0;
    }

    /// Bump EVSIDS score for a variable while CHB is the active heuristic.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn bump_evsids_score_dormant(&mut self, var: Variable) {
        self.bump_evsids_score_dormant_batch(&[var.index()]);
    }

    /// Batch-bump dormant EVSIDS scores while CHB is active.
    pub(crate) fn bump_evsids_score_dormant_batch(&mut self, vars: &[usize]) {
        if vars.is_empty() {
            return;
        }

        debug_assert!(
            self.chb_loaded,
            "bump_evsids_score_dormant_batch requires CHB loaded"
        );
        // chb_scores holds EVSIDS data when chb_loaded is true (swapped).
        let scores = self
            .chb_scores
            .as_mut()
            .expect("chb_loaded implies allocated");
        let update = batch::apply_evsids_batch(scores, &self.heap_pos, vars, self.increment);
        if update.needs_rescale {
            self.rescale_dormant_evsids();
        }
    }

    /// Decay EVSIDS increment while CHB is active.
    #[inline]
    pub(crate) fn decay_evsids_dormant(&mut self) {
        debug_assert!(self.chb_loaded, "decay_evsids_dormant requires CHB loaded");
        self.increment /= self.decay;
        if self.increment > 1e100 {
            self.rescale_dormant_evsids();
        }
    }

    /// Rescale dormant EVSIDS scores (in chb_scores) to prevent overflow.
    fn rescale_dormant_evsids(&mut self) {
        if let Some(ref mut scores) = self.chb_scores {
            for score in scores.iter_mut() {
                *score *= 1e-100;
            }
        }
        self.increment *= 1e-100;
    }

    /// Heap-backed buffer bytes used by VSIDS state.
    ///
    /// Excludes the inline `VSIDS` struct itself so callers can count the
    /// parent solver shell exactly once.
    #[cfg(test)]
    pub(crate) fn buffer_bytes(&self) -> usize {
        use std::mem::size_of;

        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }

        self.activities.capacity() * size_of::<f64>()
            + self.bump_order.capacity() * size_of::<u64>()
            + packed_bool_vec_bytes(self.buried.capacity())
            + self.heap.capacity() * size_of::<u32>()
            + self.heap_pos.capacity() * size_of::<u32>()
            + self
                .chb_scores
                .as_ref()
                .map_or(0, |v| v.capacity() * size_of::<f64>())
            + self
                .chb_last_conflict
                .as_ref()
                .map_or(0, |v| v.capacity() * size_of::<u64>())
            + self.vmtf_prev.capacity() * size_of::<u32>()
            + self.vmtf_next.capacity() * size_of::<u32>()
    }

    // -- Bucket queue methods for IC3 domain-restricted queries (#8476) --

    /// Rebuild the bucket queue with ONLY the given domain variables (#8569 Gap 4).
    ///
    /// Convenience wrapper that takes `&[Variable]` instead of `&[usize]`.
    /// When called from `set_domain()` in IC3 mode, this ensures the bucket
    /// queue contains only domain-relevant variables, providing O(1) amortized
    /// decisions without popping through non-domain variables.
    ///
    /// Activities are preserved — only the set of variables in the queue
    /// changes. The bucket assignment uses each variable's current VSIDS
    /// activity score for relative-exponent bucketing.
    pub(crate) fn rebuild_bucket_queue_with_domain(&mut self, domain_vars: &[Variable]) {
        let indices: Vec<usize> = domain_vars.iter().map(|v| v.index()).collect();
        self.bucket_queue
            .build_from_domain(&indices, &self.activities);
    }

    /// Pop the highest-priority variable from the bucket queue, skipping
    /// assigned variables.
    ///
    /// Returns `None` when no unassigned variable remains in the queue.
    #[inline]
    pub(crate) fn pick_branching_variable_bucket(&mut self, vals: &[i8]) -> Option<Variable> {
        while let Some(var) = self.bucket_queue.pop() {
            if vals[var.index() * 2] == 0 {
                return Some(var);
            }
        }
        None
    }

    /// Reinsert a variable into the bucket queue (e.g., on backtrack).
    ///
    /// Uses the current activity to compute the bucket index. This is an
    /// approximation — the variable may not land in exactly the same bucket
    /// it came from — but for IC3 short queries this is acceptable.
    #[inline]
    pub(crate) fn bucket_queue_insert(&mut self, var: Variable) {
        self.bucket_queue.push_with_activity(var, &self.activities);
    }

    /// Whether the bucket queue contains a given variable.
    #[inline]
    pub(crate) fn bucket_queue_contains(&self, var: Variable) -> bool {
        self.bucket_queue.contains(var)
    }

    /// Clear the bucket queue state.
    pub(crate) fn bucket_queue_clear(&mut self) {
        self.bucket_queue.clear();
    }

    /// Whether the bucket queue is active (has variables in it).
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn bucket_queue_is_empty(&self) -> bool {
        self.bucket_queue.is_empty()
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
