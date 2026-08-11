// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;
use std::cell::RefCell;

struct GuardState {
    /// Term under evaluation -> its entry depth on this thread's stack.
    in_progress: DetHashMap<TermId, u32>,
    /// Current evaluation-stack depth (frames with a live `Entered`).
    depth: u32,
    /// Lowest ENTRY DEPTH targeted by any cycle re-entry observed in the
    /// current frame's scope (`u32::MAX` = none). Swapped per frame and
    /// folded into the parent's scope on exit — the Tarjan-lowlink
    /// discipline (#eval-lowlink).
    min_reentry: u32,
    /// Monotone counter bumped on external stop — results computed
    /// across a stop are never memoized (unchanged from the original
    /// poison semantics for stops).
    stop_poison: u64,
    /// Monotone count of MEMO-MISSING `evaluate_term` node visits on this
    /// thread — the evaluator's unit of real work (a memo hit never
    /// reaches `enter`). Throttles the external-stop poll, and is the
    /// deterministic clock W4's search budget is measured against
    /// (`Executor::w4_work_deadline`).
    enters: u64,
    /// Active scoped evaluator-work deadlines as
    /// `(guard_id, absolute_enters_deadline)` pairs.
    work_budgets: Vec<(u64, u64)>,
    next_work_budget_id: u64,
    /// Monotone poison bumped when a scoped work deadline refuses a node.
    /// Any frame spanning that event must not memoize its `Unknown`.
    work_budget_poison: u64,
    /// Process-unique id of the current OUTERMOST evaluation frame
    /// (assigned on every depth 0 -> 1 transition from the global
    /// [`FRAME_GENERATION`] source). See [`top_frame_generation`].
    top_generation: u64,
}

/// Process-global frame-generation source. Monotonic across ALL threads,
/// so a generation is never reused — even when solves run on fresh
/// dedicated-stack threads whose thread-locals restart from scratch.
static FRAME_GENERATION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

thread_local! {
    static STATE: RefCell<GuardState> = RefCell::new(GuardState {
        in_progress: DetHashMap::default(),
        depth: 0,
        min_reentry: u32::MAX,
        stop_poison: 0,
        enters: 0,
        work_budgets: Vec::new(),
        next_work_budget_id: 0,
        work_budget_poison: 0,
        top_generation: 0,
    });
}

/// The process-unique id of the outermost `evaluate_term` frame currently
/// live on this thread, or `None` outside any evaluation.
///
/// SOUNDNESS BASIS (borrow discipline, not convention): `evaluate_term`
/// takes `&self` on the executor and `ctx.assertions` /
/// `last_assumptions` are plain fields (no interior mutability), so for
/// the whole lifetime of one outermost frame no `&mut self` method can
/// run on this thread — the assertion set is FROZEN by the borrow
/// checker. A cache validated under generation G may therefore skip
/// re-validation for as long as `top_frame_generation()` still returns
/// G. (This is deliberately NOT keyed on eval-memo sessions: sessions
/// span `&mut self` regions that DO mutate assertions — the incremental
/// push/pop suite refuted that contract via the debug oracle.)
pub(in crate::executor) fn top_frame_generation() -> Option<u64> {
    STATE.with(|s| {
        let st = s.borrow();
        (st.depth > 0).then_some(st.top_generation)
    })
}

/// RAII token marking one term as under evaluation on this thread.
pub(super) struct Entered {
    term: TermId,
}

/// RAII guard imposing an actual memo-missing evaluator-node budget.
/// Nested guards compose by their minimum absolute deadline and restore
/// independently on drop.
pub(in crate::executor::model) struct EvalWorkBudget {
    id: u64,
    poison_before: u64,
    active: bool,
}

impl EvalWorkBudget {
    pub(in crate::executor::model) fn new(limit: usize) -> Self {
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            let id = st.next_work_budget_id;
            st.next_work_budget_id = st.next_work_budget_id.wrapping_add(1);
            let limit = u64::try_from(limit).unwrap_or(u64::MAX);
            let deadline = st.enters.saturating_add(limit);
            let poison_before = st.work_budget_poison;
            st.work_budgets.push((id, deadline));
            EvalWorkBudget {
                id,
                poison_before,
                active: true,
            }
        })
    }

    pub(in crate::executor::model) fn exhausted(&self) -> bool {
        STATE.with(|s| s.borrow().work_budget_poison != self.poison_before)
    }
}

impl Drop for EvalWorkBudget {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            if let Some(index) = st.work_budgets.iter().position(|(id, _)| *id == self.id) {
                st.work_budgets.swap_remove(index);
            }
        });
        self.active = false;
    }
}

impl Drop for Entered {
    fn drop(&mut self) {
        STATE.with(|s| {
            let mut st = s.borrow_mut();
            st.in_progress.remove(&self.term);
            st.depth -= 1;
        });
    }
}

/// Mark `term` in-progress; `None` when it already is — a cycle. The
/// re-entry records the TARGET frame's entry depth in the current
/// frame's `min_reentry` scope: a frame's result is a pure function of
/// `(model, term)` iff every cycle observed during its computation
/// targeted a term at or below its own depth (the cycle is then
/// internal to its subtree and a fresh top-level evaluation reproduces
/// the identical fail-closed cuts). The former GLOBAL poison vetoed the
/// memo for the ENTIRE stack above any cycle — and the UF function
/// tables' self/congruent rows guarantee bottom cycles, so effectively
/// nothing memoized and sibling row resolutions re-walked whole trees:
/// the #eval-cycle-guard turned the old unbounded-memory divergence
/// into a bounded-memory EXPONENTIAL-TIME recomputation (the 30s
/// slice_index verification-consumer spins). Depth-scoped purity lets cycle heads
/// and self-contained subtrees memoize.
pub(super) fn enter(term: TermId) -> Option<Entered> {
    STATE.with(|s| {
        let mut st = s.borrow_mut();
        if st
            .work_budgets
            .iter()
            .map(|(_, deadline)| *deadline)
            .min()
            .is_some_and(|deadline| st.enters >= deadline)
        {
            st.work_budget_poison = st.work_budget_poison.wrapping_add(1);
            return None;
        }
        st.enters = st.enters.saturating_add(1);
        if let Some(&entry_depth) = st.in_progress.get(&term) {
            st.min_reentry = st.min_reentry.min(entry_depth);
            None
        } else {
            st.depth += 1;
            if st.depth == 1 {
                // New outermost frame: mint its process-unique id.
                st.top_generation =
                    1 + FRAME_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            let d = st.depth;
            st.in_progress.insert(term, d);
            Some(Entered { term })
        }
    })
}

/// Depth of the innermost live frame (call between `enter` and drop).
pub(super) fn depth() -> u32 {
    STATE.with(|s| s.borrow().depth)
}

/// Open a fresh `min_reentry` scope for the current frame, returning the
/// parent's value to restore-fold on exit.
pub(super) fn swap_min(new: u32) -> u32 {
    STATE.with(|s| {
        let mut st = s.borrow_mut();
        std::mem::replace(&mut st.min_reentry, new)
    })
}

pub(super) fn min_reentry() -> u32 {
    STATE.with(|s| s.borrow().min_reentry)
}

/// Fold this frame's observations back into the parent's scope.
pub(super) fn fold_min(parent: u32) {
    STATE.with(|s| {
        let mut st = s.borrow_mut();
        st.min_reentry = st.min_reentry.min(parent);
    })
}

/// True on every 512th `enter` — throttles the external-stop poll to
/// keep the hot path free of clock reads.
pub(super) fn should_poll_stop() -> bool {
    STATE.with(|s| s.borrow().enters & 511 == 0)
}

/// This thread's memo-missing node-visit count (see `GuardState::enters`).
pub(super) fn enters() -> u64 {
    STATE.with(|s| s.borrow().enters)
}

thread_local! {
    /// Nesting depth of live [`AssertionsFrozen`] guards on this thread.
    static FREEZE_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// Process-unique id of the outermost live freeze region.
    static FREEZE_GEN: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Process-global freeze-generation source (never reused across threads).
static FREEZE_GENERATION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// RAII marker for a lexical region that PROMISES not to mutate
/// `ctx.assertions` / `last_assumptions` — placed only around passes that
/// interleave model mutation with many top-level `evaluate_term` calls
/// (each of which is its own frame, so the frame-generation fast path
/// cannot amortize across them; the read-pin repair loop re-ran the
/// O(constraints) def-index snapshot compare once per pin because of
/// exactly this).
///
/// UNLIKE the borrow-checker-backed frame generation, this is a stated
/// contract — so it is defended the same way the (refuted) eval-memo
/// session keying was caught: `array_def_candidates` re-runs the full
/// byte-exact snapshot compare on every freeze-keyed fast hit in debug
/// builds. A guard placed around a region that does mutate assertions
/// fails loudly across the test batteries instead of serving a stale
/// definition set.
pub(in crate::executor) struct AssertionsFrozen(());

impl AssertionsFrozen {
    pub(in crate::executor) fn new() -> Self {
        FREEZE_DEPTH.with(|d| {
            let depth = d.get();
            if depth == 0 {
                FREEZE_GEN.with(|g| {
                    g.set(1 + FREEZE_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
                });
            }
            d.set(depth + 1);
        });
        AssertionsFrozen(())
    }
}

impl Drop for AssertionsFrozen {
    fn drop(&mut self) {
        FREEZE_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// The process-unique id of the outermost live assertions-freeze region on
/// this thread, or `None` when no guard is live.
pub(in crate::executor) fn assertions_freeze_generation() -> Option<u64> {
    FREEZE_DEPTH.with(|d| (d.get() > 0).then(|| FREEZE_GEN.with(std::cell::Cell::get)))
}

pub(super) fn stop_poison() -> u64 {
    STATE.with(|s| s.borrow().stop_poison)
}

pub(super) fn work_budget_poison() -> u64 {
    STATE.with(|s| s.borrow().work_budget_poison)
}

pub(super) fn note_stop() {
    STATE.with(|s| s.borrow_mut().stop_poison += 1);
}
