// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The gate's memo of resolved array and datatype leaves
//! (#gate-exact-leaf-memo).
//!
//! A leaf resolves through its asserted definitions, which read other leaves.
//! A read of a leaf that is already being resolved is a cycle cut: it fails,
//! and the leaf it was resolving falls back to its next definition or to its
//! model entry. So the value a resolution returns can depend on which leaves
//! are in flight. For `(= u w)`, `u` read on its own resolves through `w`, and
//! `w` (with `u` cut) falls back to `w`'s model entry. The same `w` read on its
//! own falls back to `u`'s entry instead.
//!
//! The memo used to keep every value it resolved. Values computed under a cut
//! were then reused at the top level, and whichever leaf an evaluation reached
//! first decided both values. The gate (walking the assertions) and
//! `(get-model)` (walking the declared constants) start from different leaves,
//! so the gate confirmed one model and the printer printed another. On the
//! QF_AUFBV reproducer `invalid_model_min1`, z3 rejects the printed model.
//!
//! The memo now returns an entry only where resolving the leaf again would
//! compute the same value. A read therefore returns the same value whatever
//! has been cached before. Every top-level read, by the gate, by the
//! authoritative gate or by the printer, is the same function of the model.
//! Here is why this is exact.
//!
//! * A resolution depends on its context only through the cycle-guard
//!   attempts it makes. Each attempt either enters a leaf that is not in
//!   flight, or hits one that is. If no attempt hits a frame that was in
//!   flight before the resolution started, the result is the one the leaf has
//!   with an empty stack. Such a result is memoized; any other result is not.
//! * That result is also what a later read computes, unless the reader's stack
//!   holds a leaf whose read inside the resolution returned a value. A read of
//!   an in-flight leaf is cut and returns nothing, so a leaf whose reads there
//!   all returned nothing would read the same either way.
//! * Every read inside a memoized resolution finished at a time in `[lo, hi]`.
//!   `lo` is the start of the resolution, lowered to the `lo` of every
//!   memoized entry it read. The memo logs when each resolution that returned
//!   a value finished.
//! * An in-flight frame is therefore harmless if its leaf returned no value
//!   during that window. It is also harmless if it was in flight on the same
//!   stack for the whole resolution: it was in the original context, and the
//!   original resolution never hit it.
//!
//! An entry whose check fails is recomputed in the current context. That costs
//! time, never correctness. Cycle-free resolutions pass the check wherever
//! they are read again, so they keep the reuse that #gate-none-cache and the
//! nested datatype-carrying-array memo depend on. A cyclic region is resolved
//! a bounded number of times instead of once per top-level read: in an alias
//! chain `(= a_k b_k)`, `(= a_k (store a_{k-1} ..))`, `b_k` read inside `a_k`
//! is cut and resolves to nothing, so `a_k`'s entry also serves `b_k`'s own
//! resolution, and the chain stays linear.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use ay_core::TermId;
use ay_model_check::ModelValue;

use super::IndependentModelView;

/// The leaf values shared by every view of one cache scope
/// ([`super::GateViewCacheSession`], #gate-view-cache).
#[derive(Default)]
pub(super) struct LeafMemo {
    /// Logical time: one tick per entered frame, finished resolution and view.
    clock: Cell<u64>,
    entries: RefCell<HashMap<TermId, LeafEntry>>,
    /// When each resolution of a leaf that returned a value finished,
    /// ascending, in any view of the scope.
    valued: RefCell<HashMap<TermId, Vec<u64>>>,
    /// Frames entered, for the work-bound regression tests.
    #[cfg(test)]
    frames: Cell<u64>,
}

/// A memoized resolution: its value, and the window in which every read it
/// depends on finished.
struct LeafEntry {
    value: Option<ModelValue>,
    view: u64,
    start: u64,
    lo: u64,
    hi: u64,
}

impl LeafMemo {
    fn tick(&self) -> u64 {
        let now = self.clock.get() + 1;
        self.clock.set(now);
        now
    }

    /// Forget every memoized value. The entry log stays, which only makes
    /// later checks more conservative.
    pub(super) fn clear(&self) {
        self.entries.borrow_mut().clear();
    }

    fn valued_within(&self, t: TermId, lo: u64, hi: u64) -> bool {
        self.valued.borrow().get(&t).is_some_and(|times| {
            let first = times.partition_point(|&time| time < lo);
            times.get(first).is_some_and(|&time| time <= hi)
        })
    }

    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.entries.borrow().is_empty()
    }

    /// Plant `value` for `t`, valid in every context (a stale-cache fixture).
    #[cfg(test)]
    pub(super) fn seed(&self, t: TermId, value: ModelValue) {
        let entry = LeafEntry {
            value: Some(value),
            view: 0,
            start: 0,
            lo: 0,
            hi: 0,
        };
        self.entries.borrow_mut().insert(t, entry);
    }

    #[cfg(test)]
    pub(super) fn frames_entered(&self) -> u64 {
        self.frames.get()
    }
}

/// One in-flight resolution.
struct Frame {
    term: TermId,
    start: u64,
    /// The earliest time at which a read inside this resolution may have
    /// finished.
    lo: u64,
    /// The lowest stack depth any cycle cut inside this resolution hit.
    low: usize,
}

/// The stack of in-flight resolutions of one view. It records frames, never
/// results, so it is per view even when the memo is shared.
pub(super) struct LeafStack {
    view: u64,
    frames: RefCell<Vec<Frame>>,
    depth: RefCell<HashMap<TermId, usize>>,
}

impl LeafStack {
    pub(super) fn new(memo: &LeafMemo) -> Self {
        LeafStack {
            view: memo.tick(),
            frames: RefCell::new(Vec::new()),
            depth: RefCell::new(HashMap::new()),
        }
    }
}

impl IndependentModelView<'_> {
    /// The memoized value of `t`, if it is exactly the value resolving `t` in
    /// the current context would compute.
    pub(super) fn memoized_leaf(&self, t: TermId) -> Option<Option<ModelValue>> {
        if self.leaf_stack.depth.borrow().contains_key(&t) {
            return None; // in flight: the read is a cycle cut
        }
        let entries = self.leaf_memo.entries.borrow();
        let entry = entries.get(&t)?;
        let mut frames = self.leaf_stack.frames.borrow_mut();
        let in_flight_throughout = if entry.view == self.leaf_stack.view {
            frames.partition_point(|frame| frame.start < entry.start)
        } else {
            0
        };
        let cut_would_change_a_read = frames[in_flight_throughout..]
            .iter()
            .any(|frame| self.leaf_memo.valued_within(frame.term, entry.lo, entry.hi));
        if cut_would_change_a_read {
            return None;
        }
        if let Some(reader) = frames.last_mut() {
            reader.lo = reader.lo.min(entry.lo);
        }
        if entry
            .value
            .as_ref()
            .is_some_and(|value| !super::super::recovery_admission::pay_model_value_copy(value))
        {
            return Some(None);
        }
        Some(entry.value.clone())
    }

    /// Enter the resolution of `t`. `false` is a cycle cut: `t` is in flight.
    pub(super) fn enter_leaf(&self, t: TermId) -> bool {
        let mut depth = self.leaf_stack.depth.borrow_mut();
        let mut frames = self.leaf_stack.frames.borrow_mut();
        if let Some(&cut) = depth.get(&t) {
            if let Some(top) = frames.last_mut() {
                top.low = top.low.min(cut);
            }
            return false;
        }
        let start = self.leaf_memo.tick();
        #[cfg(test)]
        self.leaf_memo.frames.set(self.leaf_memo.frames.get() + 1);
        depth.insert(t, frames.len());
        frames.push(Frame {
            term: t,
            start,
            lo: start,
            low: usize::MAX,
        });
        true
    }

    /// Record a read of the in-flight leaf `t` that is answered with a
    /// trial value instead of being cut (AY-SMT-3,
    /// [`Self::array_self_referential_fixpoint`]). The bookkeeping is a cycle
    /// cut's: every resolution above `t`'s frame that saw the trial value is
    /// context-dependent and is not memoized. `false` when `t` is not in
    /// flight, in which case nothing may answer for it.
    pub(super) fn note_trial_read(&self, t: TermId) -> bool {
        let depth = self.leaf_stack.depth.borrow();
        let Some(&cut) = depth.get(&t) else {
            return false;
        };
        let mut frames = self.leaf_stack.frames.borrow_mut();
        if let Some(top) = frames.last_mut() {
            top.low = top.low.min(cut);
        }
        true
    }

    /// Leave the resolution of `t` entered by [`Self::enter_leaf`], which
    /// returned `result`. With `memoize`, the result is kept when no cycle cut
    /// inside it hit a frame that was in flight before it started.
    pub(super) fn leave_leaf(&self, t: TermId, result: &Option<ModelValue>, memoize: bool) {
        let mut frames = self.leaf_stack.frames.borrow_mut();
        let Some(frame) = frames.pop() else {
            debug_assert!(false, "leave_leaf without a frame");
            return;
        };
        debug_assert_eq!(frame.term, t, "leaf frames are strictly nested");
        self.leaf_stack.depth.borrow_mut().remove(&frame.term);
        let depth = frames.len();
        if let Some(parent) = frames.last_mut() {
            parent.lo = parent.lo.min(frame.lo);
            parent.low = parent.low.min(frame.low);
        }
        drop(frames);
        let finished = self.leaf_memo.tick();
        if result.is_some() {
            self.leaf_memo
                .valued
                .borrow_mut()
                .entry(t)
                .or_default()
                .push(finished);
        }
        if !memoize {
            return;
        }
        if frame.low < depth {
            return; // a cut below this frame: the value depends on the context
        }
        if result
            .as_ref()
            .is_some_and(|value| !super::super::recovery_admission::pay_model_value_copy(value))
        {
            return;
        }
        let entry = LeafEntry {
            value: result.clone(),
            view: self.leaf_stack.view,
            start: frame.start,
            lo: frame.lo,
            hi: finished,
        };
        self.leaf_memo.entries.borrow_mut().insert(t, entry);
    }
}

#[cfg(test)]
mod tests;
