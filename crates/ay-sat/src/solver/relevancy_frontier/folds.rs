// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The INCREMENTAL FOLD half of the relevancy frontier.
//!
//! The parent owns the frontier's state, its invalidation rules, and the
//! from-scratch `rebuild` that every invalidating event falls back to. This
//! child owns the other direction: taking the frontier from one search state to
//! the next in O(touched) rather than O(clauses x literals), by folding in a
//! single assignment, a single unassignment, or the clauses appended since the
//! last sync.
//!
//! The split is along that line and nothing else — every function here mutates
//! `true_count` / `var_unsat` / `buf` incrementally and none of them decides
//! WHEN a fold is legal; `sync`, `invalidate` and `begin_unassign_fold` in the
//! parent do that.
//!
//! Visibility note: `fold_unassign` is `pub(in crate::solver)` because
//! `solver::backtrack` drives it directly during trail unwinding — the same
//! reach it had as `pub(super)` when it lived in the parent.

use super::*;

impl RelevancyFrontier {
    /// Fold every clause appended since the watermark.
    ///
    /// Returns `false` when the appended-clause count disagrees with the
    /// arena's own `num_clauses()` delta — the O(1) guard against an arena
    /// mutation that neither bumped the epoch nor appended. The caller decides
    /// what that means: `sync` rebuilds, the exactness pin asserts.
    #[must_use]
    pub(super) fn fold_appended_clauses(&mut self, s: &Solver) -> bool {
        let start = self.arena_words;
        self.true_count.resize(s.arena.len(), 0);
        let mut appended = 0usize;
        for off in s.arena.active_indices_from(start) {
            appended += 1;
            if s.arena.is_garbage_any(off) {
                continue;
            }
            self.fold_new_clause(s, off);
        }
        if self.arena_clauses + appended != s.arena.num_clauses() {
            return false;
        }
        self.arena_words = s.arena.len();
        self.arena_clauses = s.arena.num_clauses();
        true
    }

    /// Seed one freshly appended clause from the CURRENT assignment.
    fn fold_new_clause(&mut self, s: &Solver, off: usize) {
        let lits = s.arena.literals(off);
        let mut true_lits = 0u32;
        for &lit in lits {
            if s.lit_val(lit) > 0 {
                true_lits += 1;
            }
            let li = lit.index();
            if li < self.occ.len() {
                self.occ[li].push(off as u32);
            }
        }
        self.true_count[off] = true_lits;
        if true_lits != 0 {
            return;
        }
        for &lit in lits {
            self.mark_unsat_occurrence(s, lit.variable().index());
        }
    }

    /// Fold "literal `lit` just became TRUE".
    pub(super) fn fold_assign(&mut self, s: &Solver, lit: Literal) {
        let v = lit.variable().index();
        if v < self.buf.len() && self.buf[v] {
            self.buf[v] = false;
            self.size -= 1;
        }
        let li = lit.index();
        if li >= self.occ.len() {
            return;
        }
        // Move the occurrence vector out so the clause walk can borrow it while
        // `true_count` / `var_unsat` are written. A `Vec` move is three word
        // copies and never reallocates.
        let occ = std::mem::take(&mut self.occ[li]);
        for &off in &occ {
            let off = off as usize;
            self.true_count[off] += 1;
            if self.true_count[off] != 1 {
                continue; // already satisfied by another literal
            }
            // 0 -> 1: the clause is satisfied and stops contributing.
            for &other in s.arena.literals(off) {
                let u = other.variable().index();
                if u >= self.var_unsat.len() {
                    continue;
                }
                self.var_unsat[u] -= 1;
                if self.var_unsat[u] == 0 && self.buf[u] {
                    self.buf[u] = false;
                    self.size -= 1;
                }
            }
        }
        self.occ[li] = occ;
    }

    /// Fold "literal `lit` stopped being TRUE". Called from backtrack AFTER
    /// `vals` has been cleared for `lit`'s variable.
    pub(in crate::solver) fn fold_unassign(&mut self, s: &Solver, lit: Literal) {
        // The offsets below are only meaningful while the live formula holds
        // still; `begin_unassign_fold` is what guarantees that, and this is the
        // pin on it. Not a `debug_assert!`: the invariants feature is meant to
        // be usable on a `--release` run too.
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        assert_eq!(
            self.epoch,
            s.arena.formula_epoch(),
            "BUG: fold_unassign over a MOVED formula (cached epoch {} != arena \
             epoch {}); `occ` holds arena offsets that no longer denote the \
             clauses they were recorded for",
            self.epoch,
            s.arena.formula_epoch(),
        );
        let li = lit.index();
        if li < self.occ.len() {
            let occ = std::mem::take(&mut self.occ[li]);
            for &off in &occ {
                let off = off as usize;
                debug_assert!(
                    self.true_count[off] > 0,
                    "BUG: unassigning {lit:?} from clause @{off} that has no true literal"
                );
                self.true_count[off] -= 1;
                if self.true_count[off] != 0 {
                    continue;
                }
                // 1 -> 0: the clause is unsatisfied again.
                for &other in s.arena.literals(off) {
                    self.mark_unsat_occurrence(s, other.variable().index());
                }
            }
            self.occ[li] = occ;
        }
        // `lit`'s own variable re-enters the frontier iff it still occurs in an
        // unsatisfied clause; the loop above may already have put it there.
        let v = lit.variable().index();
        if v < self.buf.len()
            && !self.buf[v]
            && self.var_unsat[v] > 0
            && !s.var_lifecycle.is_removed(v)
        {
            self.buf[v] = true;
            self.size += 1;
        }
    }

    /// Record one more unsatisfied-clause occurrence for variable `v`, adding it
    /// to the frontier when that is its first one and it is eligible (still
    /// unassigned, not inprocessing-removed).
    #[inline]
    fn mark_unsat_occurrence(&mut self, s: &Solver, v: usize) {
        if v >= self.var_unsat.len() {
            return;
        }
        let was = self.var_unsat[v];
        self.var_unsat[v] = was + 1;
        if was == 0
            && !self.buf[v]
            && ay_prefetch::val_at(&s.vals, v * 2) == 0
            && !s.var_lifecycle.is_removed(v)
        {
            self.buf[v] = true;
            self.size += 1;
        }
    }
}
