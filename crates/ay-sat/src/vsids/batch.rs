// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Heap-free batch score update kernels for VSIDS/CHB.
//!
//! These functions deliberately operate only on caller-owned slices and return
//! a small repair contract. They do not allocate, do not inspect solver state,
//! and do not know about propagation or JIT machinery.

use super::INVALID_POS;

pub(super) const ACTIVITY_RESCALE_LIMIT: f64 = 1e100;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BatchHeapRepair {
    None,
    SiftUp { var: usize },
    Rebuild,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct BatchScoreUpdate {
    pub(super) touched: usize,
    pub(super) in_heap: usize,
    pub(super) needs_rescale: bool,
    pub(super) repair: BatchHeapRepair,
}

impl BatchScoreUpdate {
    #[inline]
    pub(super) fn new(
        touched: usize,
        in_heap: usize,
        first_in_heap: usize,
        needs_rescale: bool,
    ) -> Self {
        let repair = match in_heap {
            0 => BatchHeapRepair::None,
            1 => BatchHeapRepair::SiftUp { var: first_in_heap },
            _ => BatchHeapRepair::Rebuild,
        };
        Self {
            touched,
            in_heap,
            needs_rescale,
            repair,
        }
    }
}

/// Decide whether a uniform-increment (EVSIDS) batch bump should restore the
/// heap with a single Floyd `rebuild_heap` (O(n)) or with `in_heap` individual
/// `sift_up`s (O(in_heap * log n)).
///
/// The original contract always rebuilt when two or more bumped variables were
/// in the heap. That is catastrophic on the large QF_LRA BMC instances, whose
/// decision heap holds hundreds of thousands of variables: every conflict bumps
/// a handful of in-heap variables and triggered a full O(n) heapify, so
/// `rebuild_heap` dominated wall time (~62% in profiling). Individual sift-ups
/// only touch the bumped variables' root-ward paths.
///
/// Floyd heapify costs ~`heap_len` comparisons; `in_heap` sift-ups cost
/// ~`in_heap * log2(heap_len)`. Rebuild wins only once
/// `in_heap * log2(heap_len) >= heap_len`. This is sound regardless of the
/// branch taken — both restore the same max-heap invariant; the choice is
/// purely a performance heuristic (heap order is a search heuristic, never a
/// correctness condition).
///
/// When this returns `false`, the caller repairs the heap with
/// `sparse_reheapify_affected_paths`: a bottom-up Floyd `sift_down` restricted
/// to the union of the bumped variables' root-ward paths. (Naive per-variable
/// `sift_up` is NOT correct even under a uniform increment — a bumped node
/// climbing can displace a non-bumped ancestor down onto an already-processed
/// bumped node, leaving a child-greater-than-parent violation.) Both branches
/// restore the same max-heap invariant; the choice is purely a performance
/// heuristic (heap order is a search heuristic, never a correctness condition).
#[inline]
pub(super) fn evsids_batch_prefers_rebuild(in_heap: usize, heap_len: usize) -> bool {
    if in_heap < 2 {
        return false;
    }
    if heap_len <= 1 {
        return false;
    }
    // log2 floor; heap_len >= 2 here so this is >= 1.
    let log2_len = (usize::BITS - 1 - heap_len.leading_zeros()) as usize;
    in_heap.saturating_mul(log2_len.max(1)) >= heap_len
}

/// Add one EVSIDS increment to every variable in `vars`.
///
/// Contract:
/// - deterministic in caller-supplied order,
/// - heap-free after the caller has allocated the input/output slices,
/// - duplicate variables are applied repeatedly, matching scalar bumps,
/// - returns the minimal safe heap repair plan used by the caller.
pub(super) fn apply_evsids_batch(
    activities: &mut [f64],
    heap_pos: &[u32],
    vars: &[usize],
    increment: f64,
) -> BatchScoreUpdate {
    let mut in_heap = 0usize;
    let mut first_in_heap = 0usize;
    let mut needs_rescale = false;

    for &idx in vars {
        debug_assert!(
            idx < activities.len(),
            "BUG: apply_evsids_batch variable {idx} out of range (num_vars={})",
            activities.len()
        );
        debug_assert!(
            idx < heap_pos.len(),
            "BUG: apply_evsids_batch heap_pos missing variable {idx}"
        );

        activities[idx] += increment;
        needs_rescale |= activities[idx] > ACTIVITY_RESCALE_LIMIT;

        if heap_pos[idx] != INVALID_POS {
            if in_heap == 0 {
                first_in_heap = idx;
            }
            in_heap += 1;
        }
    }

    BatchScoreUpdate::new(vars.len(), in_heap, first_in_heap, needs_rescale)
}

/// Apply CHB Q-score updates to every variable in `vars`.
///
/// `heap_pos` is `Some` when the updated scores are currently loaded into the
/// decision heap and `None` when CHB scores are dormant side data.
pub(super) fn apply_chb_batch(
    scores: &mut [f64],
    last_conflict: &mut [u64],
    heap_pos: Option<&[u32]>,
    vars: &[usize],
    conflicts: u64,
    alpha: f64,
) -> BatchScoreUpdate {
    let mut in_heap = 0usize;
    let mut first_in_heap = 0usize;

    for &idx in vars {
        debug_assert!(
            idx < scores.len(),
            "BUG: apply_chb_batch variable {idx} out of range (num_vars={})",
            scores.len()
        );
        debug_assert!(
            idx < last_conflict.len(),
            "BUG: apply_chb_batch last_conflict missing variable {idx}"
        );

        let last = last_conflict[idx];
        let reward = 1.0 / (conflicts.saturating_sub(last) + 1) as f64;
        scores[idx] = (1.0 - alpha).mul_add(scores[idx], alpha * reward);
        last_conflict[idx] = conflicts;

        if let Some(pos) = heap_pos {
            debug_assert!(
                idx < pos.len(),
                "BUG: apply_chb_batch heap_pos missing variable {idx}"
            );
            if pos[idx] != INVALID_POS {
                if in_heap == 0 {
                    first_in_heap = idx;
                }
                in_heap += 1;
            }
        }
    }

    BatchScoreUpdate::new(vars.len(), in_heap, first_in_heap, false)
}
