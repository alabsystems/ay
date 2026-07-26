// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #warm-simplex (`AY_LRA_WARM_SIMPLEX_STATE`, default OFF): delta-only simplex
//! bookkeeping across push/pop, adopted (clean-room) from OpenSMT, the 2025
//! SMT-COMP incremental QF_LRA winner.
//!
//! Three coupled mechanisms, ONE flag:
//!
//! 1. **Persistent infeasible-candidate set.** The violated-basic-var heap is
//!    maintained incrementally at every value-write site and SURVIVES `pop()`:
//!    instead of clearing the heap and forcing an O(rows)
//!    `rebuild_infeasible_heap` + O(vars) non-basic scan on the next check,
//!    `pop_inner` re-validates exactly the vars whose bound slots the trail
//!    replay rewrote (O(bounds-changed)). Stale heap entries are already
//!    lazily re-validated by `pop_greatest_error`, so keeping them is sound.
//!
//! 2. **Value-preserving pop + last-feasible delta.** AY never rolled back
//!    variable values on pop (bounds pop, values stay) — this flag leans into
//!    that: a changed-vars delta vector (first-write-wins log of pre-change
//!    values, recorded at the `update_nonbasic` chokepoint) lets the solver
//!    restore the last-feasible assignment after a simplex CONFLICT, so the
//!    next check starts from a near-feasible point instead of wherever the
//!    failed repair left the values. Any value write that bypasses the
//!    chokepoint (float-layer install, LIA rounding/patching, optimization,
//!    diseq repair, lifecycle resets, row additions) invalidates the log; it
//!    re-arms at the next feasible anchor.
//!
//! 3. **Non-basic violation discovery without the O(vars) scan.** A bound
//!    activation that makes a NON-basic var violate enqueues it in a small
//!    persistent dirty set (`nonbasic_dirty`), as does an `update_nonbasic`
//!    that leaves its target violated and a pop that rewrites a non-basic
//!    var's bound slot. When the set's coverage invariant holds
//!    (`nonbasic_valid`), the simplex's no-violated-row exit scans only the
//!    dirty set instead of every variable. The invariant is broken (and the
//!    full scan restored, which re-arms it on a clean pass) by every site
//!    that marks the heap stale or writes values outside the chokepoint.
//!
//! SOUNDNESS: verdict semantics are preserved exactly. The targeted exit can
//! at worst claim an optimistic Sat if a coverage invariant were violated —
//! and every final Sat verdict still passes the unconditional
//! `guard_sat_current_assignment_bounds` full rescan (allow_memo=false), which
//! demotes to Unknown and (under this flag) marks the heap stale so the next
//! simplex runs the full rebuild + full scan instead of livelocking on the
//! same warm state. Conflict construction (`build_conflict_with_farkas`)
//! depends only on tableau rows + bound reason literals, not on the heap,
//! the dirty set, or variable values, so Farkas conflicts remain valid.
//!
//! Flag OFF: every gated site takes the exact code path it takes today.

use super::*;
use std::sync::OnceLock;

/// `AY_LRA_WARM_SIMPLEX_STATE` — parse-once process-wide default (same pattern
/// as the other `AY_LRA_*` flags). DEFAULT ON (`=0` opts out) since 2026-07-25:
/// 2-sample full-division @1200s measurement (official SMT-COMP 2025 Inc QF_LRA
/// 10-file corpus, isolated per file) = 769/763 warm vs 743/751 off — non-
/// overlapping ranges, +19 mean, gains reproduce exactly per file (rod.bmc
/// 94=94 +22, dist.bmc 81/80 +14, fisher_ring.bmc 60=60 +6); one known
/// reproducible per-file cost (bmwlin.bmc 78=78 vs 101 — loses its completion;
/// follow-up candidate) outweighed division-wide. Soundness: adversarial
/// review + 4 suite configs + 0 real verdict conflicts in 773 common answers
/// vs OpenSMT. The per-solver copy (`WarmSimplexState::enabled`) is what all
/// code paths read, so tests can drive flag-on and flag-off solvers in one
/// process.
pub(crate) fn warm_simplex_state_enabled() -> bool {
    static V: OnceLock<bool> = OnceLock::new();
    *V.get_or_init(|| !std::env::var("AY_LRA_WARM_SIMPLEX_STATE").is_ok_and(|v| v == "0"))
}

/// All #warm-simplex state, grouped so constructors add a single field.
#[derive(Debug)]
pub(crate) struct WarmSimplexState {
    /// Per-solver copy of the env flag; tests override directly.
    pub(crate) enabled: bool,
    /// True while the `nonbasic_dirty` coverage invariant holds: every
    /// currently-violated NON-basic variable is in the dirty set (or was
    /// snapped back in bounds). Set false by any untracked mutation
    /// (`warm_invalidate`); set true only by the simplex full non-basic scan
    /// completing clean.
    pub(crate) nonbasic_valid: bool,
    /// Persistent candidate set of non-basic vars whose bounds changed (or
    /// whose value was left violated) since the last full non-basic scan.
    pub(crate) nonbasic_dirty: Vec<u32>,
    /// Membership stamps for `nonbasic_dirty`: member iff
    /// `nonbasic_stamp[v] == nonbasic_epoch` (O(1) logical clear by epoch
    /// bump, same trick as `in_infeasible_heap`).
    pub(crate) nonbasic_stamp: Vec<u32>,
    pub(crate) nonbasic_epoch: u32,
    /// First-write-wins log of `(var, value-at-last-anchor)` since the last
    /// feasible anchor. Restoring every entry reproduces the anchor
    /// assignment exactly (all values that changed are logged; the tableau's
    /// row equations are preserved because pivots are solution-set-preserving
    /// row operations and row ADDITIONS invalidate the log).
    pub(crate) delta: Vec<(u32, InfRational)>,
    /// Membership stamps for `delta` (member iff `== delta_epoch`).
    pub(crate) delta_stamp: Vec<u32>,
    pub(crate) delta_epoch: u32,
    /// True while the delta log captured EVERY value write since the anchor
    /// (i.e. all writes went through `update_nonbasic`). False after any
    /// bypass writer or row addition until the next anchor re-arms it.
    pub(crate) delta_valid: bool,
}

impl WarmSimplexState {
    pub(crate) fn new() -> Self {
        Self {
            enabled: warm_simplex_state_enabled(),
            nonbasic_valid: false,
            nonbasic_dirty: Vec::new(),
            nonbasic_stamp: Vec::new(),
            nonbasic_epoch: 1,
            delta: Vec::new(),
            delta_stamp: Vec::new(),
            delta_epoch: 1,
            delta_valid: false,
        }
    }
}

impl LraSolver {
    /// Invalidate ALL warm tracking. Called (flag-gated, O(1)) at every site
    /// that marks the infeasible heap stale or writes variable values outside
    /// the `update_nonbasic` chokepoint: row additions, the float-layer basis
    /// install, `optimize_impl`, `round_integer_vars_*`,
    /// `try_repair_free_var_pair_disequalities`, lifecycle resets, and the
    /// guard's Sat->Unknown demotion.
    #[inline]
    pub(crate) fn warm_invalidate(&mut self) {
        if !self.warm.enabled {
            return;
        }
        self.warm.nonbasic_valid = false;
        self.warm_clear_nonbasic_dirty();
        self.warm.delta_valid = false;
        self.warm_clear_delta();
    }

    /// O(1) logical clear of the non-basic dirty set.
    #[inline]
    pub(crate) fn warm_clear_nonbasic_dirty(&mut self) {
        self.warm.nonbasic_dirty.clear();
        self.warm.nonbasic_epoch = self.warm.nonbasic_epoch.wrapping_add(1);
        if self.warm.nonbasic_epoch == 0 {
            for e in self.warm.nonbasic_stamp.iter_mut() {
                *e = 0;
            }
            self.warm.nonbasic_epoch = 1;
        }
    }

    /// O(1) logical clear of the last-feasible delta log.
    #[inline]
    pub(crate) fn warm_clear_delta(&mut self) {
        self.warm.delta.clear();
        self.warm.delta_epoch = self.warm.delta_epoch.wrapping_add(1);
        if self.warm.delta_epoch == 0 {
            for e in self.warm.delta_stamp.iter_mut() {
                *e = 0;
            }
            self.warm.delta_epoch = 1;
        }
    }

    /// Enqueue a non-basic var in the persistent candidate set (dedup by
    /// stamp). Callers decide whether to pre-filter on `violates_bounds`;
    /// stale entries are re-validated when the set is drained.
    #[inline]
    pub(crate) fn warm_mark_nonbasic_dirty(&mut self, var: u32) {
        let vi = var as usize;
        if vi >= self.warm.nonbasic_stamp.len() {
            self.warm.nonbasic_stamp.resize(vi + 1, 0);
        }
        if self.warm.nonbasic_stamp[vi] == self.warm.nonbasic_epoch {
            return;
        }
        self.warm.nonbasic_stamp[vi] = self.warm.nonbasic_epoch;
        self.warm.nonbasic_dirty.push(var);
    }

    /// First-write-wins log of `var`'s CURRENT value (call before mutating).
    /// No-op unless the delta log is armed.
    #[inline]
    pub(crate) fn warm_log_value(&mut self, var: u32) {
        if !self.warm.delta_valid {
            return;
        }
        let vi = var as usize;
        if vi >= self.vars.len() {
            return;
        }
        if vi >= self.warm.delta_stamp.len() {
            self.warm.delta_stamp.resize(vi + 1, 0);
        }
        if self.warm.delta_stamp[vi] == self.warm.delta_epoch {
            return;
        }
        self.warm.delta_stamp[vi] = self.warm.delta_epoch;
        let value = self.vars[vi].value.clone();
        self.warm.delta.push((var, value));
    }

    /// Anchor the delta log at the current assignment (called right after a
    /// feasible simplex completion, alongside `save_feasible_snapshot`).
    /// Re-arms logging after a bypass-writer invalidation.
    #[inline]
    pub(crate) fn warm_reanchor_delta(&mut self) {
        if !self.warm.enabled {
            return;
        }
        self.warm_clear_delta();
        self.warm.delta_valid = true;
    }

    /// OpenSMT-style conflict recovery: restore the last-feasible (anchor)
    /// assignment from the changed-vars delta vector. Called after the
    /// simplex reports Unsat (the conflict is already fully packaged — it
    /// depends on rows + bound reasons only, never on values). Restored vars
    /// are re-validated into the warm candidate structures, so the heap /
    /// dirty-set coverage invariants are preserved.
    pub(crate) fn warm_restore_last_feasible(&mut self) {
        if !self.warm.enabled || !self.warm.delta_valid || self.warm.delta.is_empty() {
            return;
        }
        // Values are about to change wholesale: the guard memo and the
        // tightened-list chain no longer describe the assignment.
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        let mut delta = std::mem::take(&mut self.warm.delta);
        for (var, old_val) in delta.drain(..) {
            let vi = var as usize;
            if vi < self.warm.delta_stamp.len() {
                self.warm.delta_stamp[vi] = 0;
            }
            if vi >= self.vars.len() {
                continue;
            }
            self.vars[vi].value = old_val;
            // Re-establish candidate tracking for the restored var: basic
            // vars re-enter/leave the heap; non-basic vars whose restored
            // value violates the (possibly tighter) current bounds join the
            // persistent dirty set.
            if !self.heap_stale {
                self.track_var_feasibility(var);
            }
            if matches!(self.vars[vi].status, Some(VarStatus::NonBasic))
                && self.violates_bounds(var).is_some()
            {
                self.warm_mark_nonbasic_dirty(var);
            }
        }
        self.warm.delta = delta;
        // The assignment now equals the anchor; the (empty) log stays armed.
    }
}
