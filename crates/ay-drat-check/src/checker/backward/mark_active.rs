// Copyright 2026 Andrew Yates
// ACTIVE marking and dependency tracking for backward DRAT checking.
//
// Extracted from backward/mod.rs to keep files under 500 lines.
// Contains: mark_active worklist, watch management (remove/restore),
// clause reduction, and backward RAT checking with dependency collection.

use crate::literal::Literal;

use super::super::{DratChecker, Watch};
use super::BackwardChecker;

impl BackwardChecker {
    /// Mark a clause as ACTIVE and iteratively mark all clauses in its
    /// dependency chain (reason clauses for the unit propagations that
    /// led to the conflict). Uses `inner.reasons` for accurate per-variable
    /// reason tracking.
    ///
    /// Uses an explicit worklist instead of recursion to handle arbitrarily
    /// deep dependency chains without stack overflow (#5216).
    pub(super) fn mark_active(&mut self, root: usize) {
        let mut worklist = vec![root];
        while let Some(cidx) = worklist.pop() {
            if cidx >= self.active.len() || self.active[cidx] {
                continue;
            }
            self.active[cidx] = true;
            // Mark watch entries as core for two-pass BCP
            // (drat-trim.c:160-161 markWatch calls inside markClause).
            self.inner.mark_watches_core(cidx);

            if let Some(ref clause) = self.inner.clauses[cidx] {
                for &lit in clause.iter() {
                    let neg = lit.negated();
                    if self.inner.value(neg) == Some(true) {
                        let vi = neg.variable().index();
                        if vi < self.inner.reasons.len() {
                            if let Some(reason_cidx) = self.inner.reasons[vi] {
                                worklist.push(reason_cidx);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Mark all trail reason clauses as ACTIVE. Used when the conflict
    /// came from propagation (e.g., empty clause simplified away) rather
    /// than from a stored clause.
    pub(super) fn mark_trail_reasons_active(&mut self) {
        for i in 0..self.inner.trail.len() {
            let lit = self.inner.trail[i];
            let vi = lit.variable().index();
            if vi < self.inner.reasons.len() {
                if let Some(reason_cidx) = self.inner.reasons[vi] {
                    self.mark_active(reason_cidx);
                }
            }
        }
    }

    /// Mark a set of clause indices as ACTIVE.
    pub(super) fn mark_deps_active(&mut self, deps: &[usize]) {
        for &cidx in deps {
            self.mark_active(cidx);
        }
    }

    /// Clause reduction: remove top-level falsified literals before a RUP check
    /// (drat-trim.c sortSize() + truncation, lines 935-950). Literals falsified
    /// by prior unit propagation cannot contribute to a RUP derivation, so
    /// removing them reduces BCP work.
    pub(super) fn reduce_clause(&mut self, clause: Vec<Literal>) -> Vec<Literal> {
        let original_len = clause.len();
        let reduced: Vec<Literal> = clause
            .into_iter()
            .filter(|&lit| self.inner.value(lit) != Some(false))
            .collect();
        let removed = original_len - reduced.len();
        if removed > 0 {
            self.inner.stats.reduced_literals += removed as u64;
        }
        reduced
    }

    /// Remove watches for a clause (used when undoing an addition in
    /// the backward pass).
    pub(super) fn remove_watches(&mut self, cidx: usize) {
        let (w0, w1) = match &self.inner.clauses[cidx] {
            Some(c) if c.len() >= 2 => (c[0], c[1]),
            _ => return,
        };
        Self::remove_watch_entry(&mut self.inner.watches[w0.index()], cidx);
        Self::remove_watch_entry(&mut self.inner.watches[w1.index()], cidx);
    }

    fn remove_watch_entry(watches: &mut Vec<Watch>, cidx: usize) {
        if let Some(pos) = watches.iter().position(|w| w.clause_idx == cidx) {
            watches.swap_remove(pos);
        }
    }

    /// Restore a clause that was soft-deleted during the forward pass.
    /// Re-adds watch entries and restores the hash table entry. The clause
    /// data is already in the arena (delete_forward preserves it).
    pub(super) fn restore_clause(&mut self, cidx: usize) {
        self.readd_watches(cidx);
        self.inner.add_stored_clause_occurrences(cidx);
        // Restore hash table entry.
        if let Some(ref clause) = self.inner.clauses[cidx] {
            let hash = DratChecker::hash_clause(clause);
            let bucket = self.inner.bucket_idx(hash);
            self.inner.hash_buckets[bucket].push(cidx);
            self.inner.live_clauses += 1;
        }
    }

    /// Re-add watches for a clause (used when undoing a deletion in
    /// the backward pass).
    fn readd_watches(&mut self, cidx: usize) {
        let (c0, c1) = match &self.inner.clauses[cidx] {
            Some(c) if c.len() >= 2 => (c[0], c[1]),
            _ => return,
        };
        let is_core = cidx < self.active.len() && self.active[cidx];
        self.inner.watches[c0.index()].push(Watch {
            blocking: c1,
            clause_idx: cidx,
            core: is_core,
        });
        self.inner.watches[c1.index()].push(Watch {
            blocking: c0,
            clause_idx: cidx,
            core: is_core,
        });
    }

    /// Check if `clause` is RAT in backward mode with dependency tracking.
    /// Filters resolution candidates by ACTIVE status (drat-trim.c:565-567),
    /// uses pivot fallback (drat-trim.c:662-683), and marks all resolution
    /// candidates and their RUP proof chain dependencies as ACTIVE.
    ///
    /// Returns true if RAT succeeds (and marks deps), false otherwise.
    pub(super) fn check_rat_backward(&mut self, clause: &[Literal]) -> bool {
        if clause.is_empty() {
            return false;
        }
        self.inner.stats.rat_checks += 1;
        // Try the first literal as pivot with ACTIVE filtering + deps.
        let result = self
            .inner
            .check_rat_with_pivot_deps(clause, clause[0], Some(&self.active));
        if result.success {
            self.mark_rat_deps_active(&result);
            return true;
        }
        // Pivot fallback: try remaining literals.
        for &alt_pivot in &clause[1..] {
            let result =
                self.inner
                    .check_rat_with_pivot_deps(clause, alt_pivot, Some(&self.active));
            if result.success {
                self.mark_rat_deps_active(&result);
                return true;
            }
        }
        false
    }

    /// Mark all resolution candidates and RUP proof chain dependencies
    /// from a successful RAT check as ACTIVE.
    fn mark_rat_deps_active(&mut self, result: &super::super::rat::RatDepsResult) {
        for &cidx in &result.candidate_indices {
            self.mark_active(cidx);
        }
        self.mark_deps_active(&result.rup_deps);
    }
}
