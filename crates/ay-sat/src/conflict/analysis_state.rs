// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolution-chain, seen-state, and learned-clause analysis helpers.

use super::ConflictAnalyzer;
use crate::literal::Literal;
use crate::solver::VarData;

impl ConflictAnalyzer {
    /// Add a clause ID to the resolution chain (for LRAT proofs).
    /// No dedup at this level — the same clause ID may legitimately appear
    /// at multiple positions when reached via different stages (1UIP,
    /// minimize, unit chain). Dedup is applied at the proof output boundary
    /// in `ProofManager::emit_add` (#5248).
    #[inline]
    pub(crate) fn add_to_chain(&mut self, clause_id: u64) {
        self.resolution_chain.push(clause_id);
        self.resolution_chain_pivots.push(None);
    }

    /// Add a clause ID and the pivot literal resolved against that clause.
    ///
    /// This is the proof skeleton IBCL needs before it can run McMillan-style
    /// extraction over CDCL resolution chains (#8269).
    #[inline]
    pub(crate) fn add_to_chain_with_pivot(&mut self, clause_id: u64, pivot: Literal) {
        self.resolution_chain.push(clause_id);
        self.resolution_chain_pivots.push(Some(pivot));
    }

    /// Current resolution-chain length.
    #[inline]
    pub(crate) fn resolution_chain_len(&self) -> usize {
        self.resolution_chain.len()
    }

    /// True when the chain prefix has a conflict-clause seed followed only by
    /// reason clauses with recorded pivot literals and non-zero proof IDs.
    #[inline]
    pub(crate) fn resolution_chain_prefix_has_pivots(&self, prefix_len: usize) -> bool {
        if prefix_len == 0
            || prefix_len > self.resolution_chain.len()
            || prefix_len > self.resolution_chain_pivots.len()
        {
            return false;
        }

        self.resolution_chain[..prefix_len]
            .iter()
            .all(|&clause_id| clause_id != 0)
            && self.resolution_chain_pivots[..prefix_len]
                .iter()
                .enumerate()
                .all(|(idx, pivot)| idx == 0 || pivot.is_some())
    }

    #[cfg(test)]
    pub(crate) fn resolution_chain_pivot_at(&self, i: usize) -> Option<Literal> {
        self.resolution_chain_pivots[i]
    }

    /// Mark a variable as seen and track for sparse clear.
    /// Seen mark stored in `var_data[var].flags` for cache locality (#6994).
    #[inline]
    pub(crate) fn mark_seen(&mut self, var: usize, var_data: &mut [VarData]) {
        debug_assert!(
            var < var_data.len(),
            "BUG: mark_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        if !var_data[var].is_seen() {
            var_data[var].set_seen(true);
            self.seen_to_clear.push(var);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count += 1;
            }
        }
    }

    /// Register a variable whose seen flag was set externally (by JIT).
    ///
    /// The JIT conflict processor sets VarData.flags seen bit directly but
    /// does not push to `seen_to_clear` or update debug counters. This method
    /// completes the bookkeeping for a JIT-marked variable. The caller must
    /// ensure the variable's seen flag is already set in `var_data`.
    #[inline]
    #[cfg(feature = "jit")]
    pub(crate) fn register_jit_seen(&mut self, var: usize) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(
                !self.seen_to_clear.contains(&var),
                "BUG(#8760): JIT seen var {var} was already tracked in \
                 seen_to_clear before register_jit_seen; duplicate or stale \
                 JIT seen_vars output would desync sparse clear bookkeeping"
            );
        }
        self.seen_to_clear.push(var);
        #[cfg(debug_assertions)]
        {
            self.seen_true_count += 1;
        }
    }

    /// Debug-only postcondition for the JIT seen-bit handoff (#8760).
    ///
    /// After conflict-analysis JIT bookkeeping, each JIT-emitted `seen_vars`
    /// entry must either be still marked and tracked in `seen_to_clear`, or
    /// have been cleared by the non-false-literal guard and remain untracked.
    #[inline]
    #[cfg(all(debug_assertions, feature = "jit"))]
    pub(crate) fn debug_assert_jit_seen_bookkeeping(&self, var: usize, var_data: &[VarData]) {
        debug_assert!(
            var < var_data.len(),
            "BUG(#8760): JIT seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        let is_seen = var_data[var].is_seen();
        let tracked = self.seen_to_clear.contains(&var);
        debug_assert_eq!(
            is_seen, tracked,
            "BUG(#8760): JIT seen bookkeeping mismatch for var {var}: \
             is_seen={is_seen}, tracked_in_seen_to_clear={tracked}"
        );
    }

    /// Unmark a variable as seen.
    /// Not used in production (CaDiCaL keeps seen flags until end of analysis),
    /// but retained for test coverage of the mark/unmark lifecycle.
    #[inline]
    #[cfg(any(test, kani))]
    pub(crate) fn unmark_seen(&mut self, var: usize, var_data: &mut [VarData]) {
        debug_assert!(
            var < var_data.len(),
            "BUG: unmark_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        if var_data[var].is_seen() {
            var_data[var].set_seen(false);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count = self
                    .seen_true_count
                    .checked_sub(1)
                    .expect("seen_true_count underflow during unmark");
            }
        }
    }

    /// Check if a variable is seen.
    #[inline]
    pub(crate) fn is_seen(&self, var: usize, var_data: &[VarData]) -> bool {
        debug_assert!(
            var < var_data.len(),
            "BUG: is_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        var_data[var].is_seen()
    }

    /// Access the analyzed variable list (all vars marked during analysis).
    /// Used for post-analysis sorted VMTF bumping (CaDiCaL analyze.cpp:189-194).
    #[inline]
    pub(crate) fn analyzed_vars(&self) -> &[usize] {
        &self.seen_to_clear
    }

    /// Rollback the analyzed variable list to a saved size.
    ///
    /// CaDiCaL analyze.cpp:410-417: when reason bumping exceeds its limit,
    /// clear the `seen` flag for all variables added since `saved_size` and
    /// truncate the list. This prevents the extra reason-side variables from
    /// being bumped in `bump_analyzed_variables()`.
    pub(crate) fn rollback_analyzed(&mut self, saved_size: usize, var_data: &mut [VarData]) {
        debug_assert!(
            saved_size <= self.seen_to_clear.len(),
            "BUG: rollback_analyzed saved_size ({saved_size}) > current len ({})",
            self.seen_to_clear.len()
        );
        for i in saved_size..self.seen_to_clear.len() {
            let var = self.seen_to_clear[i];
            debug_assert!(var_data[var].is_seen(), "BUG: rollback var {var} not seen");
            var_data[var].set_seen(false);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count = self
                    .seen_true_count
                    .checked_sub(1)
                    .expect("seen_true_count underflow during rollback");
            }
        }
        self.seen_to_clear.truncate(saved_size);
    }

    /// Add a literal to the learned clause
    ///
    /// Untracked variant: invalidates incremental learned-level tracking
    /// (#8790). Callers on the 1UIP hot path use `add_to_learned_tracked`.
    #[inline]
    pub(crate) fn add_to_learned(&mut self, lit: Literal) {
        debug_assert!(
            !self.learned.contains(&lit),
            "BUG: duplicate literal {} added to learned clause",
            lit.to_dimacs()
        );
        debug_assert!(
            self.asserting_lit != Some(lit),
            "BUG: learned literal {} duplicates the asserting literal",
            lit.to_dimacs()
        );
        self.learned_level_tracking_valid = false;
        self.learned.push(lit);
    }

    /// Add a literal to the learned clause, incrementally tracking the
    /// maximum literal level and the watch-swap index (#8790).
    ///
    /// `level` must be the literal's current decision level from `var_data`.
    /// This folds the `compute_backtrack_level` rescan and the
    /// `reorder_for_watches` scan into the 1UIP resolution loop: after
    /// analysis, `backtrack_level_and_watch_swap` returns both in O(1) as
    /// long as the learned clause was not shrunk/minimized in between.
    #[inline]
    pub(crate) fn add_to_learned_tracked(&mut self, lit: Literal, level: u32) {
        debug_assert!(
            !self.learned.contains(&lit),
            "BUG: duplicate literal {} added to learned clause",
            lit.to_dimacs()
        );
        debug_assert!(
            self.asserting_lit != Some(lit),
            "BUG: learned literal {} duplicates the asserting literal",
            lit.to_dimacs()
        );
        let idx = self.learned.len();
        if level > self.learned_max_level {
            self.learned_max_level = level;
            self.learned_max_swap_idx = if idx >= 1 { idx } else { usize::MAX };
        } else if level == self.learned_max_level
            && self.learned_max_swap_idx == usize::MAX
            && idx >= 1
        {
            self.learned_max_swap_idx = idx;
        }
        self.learned.push(lit);
    }

    /// Set the asserting literal (the 1UIP negated)
    #[inline]
    pub(crate) fn set_asserting_literal(&mut self, lit: Literal) {
        debug_assert!(
            self.asserting_lit.is_none(),
            "BUG: asserting literal set twice (was {:?}, now {})",
            self.asserting_lit.map(Literal::to_dimacs),
            lit.to_dimacs()
        );
        self.asserting_lit = Some(lit);
    }

    /// Retain only learned literals where the predicate returns true.
    /// Compacts in-place without heap allocation (like `Vec::retain`).
    #[inline]
    pub(crate) fn retain_learned(&mut self, mut f: impl FnMut(Literal) -> bool) {
        let len_before = self.learned.len();
        self.learned.retain(|&lit| f(lit));
        if self.learned.len() != len_before {
            // Removals shift indices and can change which literal attains the
            // maximum level first; force the fused rescan (#8790). When
            // nothing is removed the relative order is untouched and the
            // incremental tracking stays exact.
            self.learned_level_tracking_valid = false;
        }
    }

    /// Replace the learned clause with a new set of literals (used by shrink).
    pub(crate) fn replace_learned(&mut self, lits: &[Literal]) {
        // Shrink reorders the clause even when it removes nothing (#8790).
        self.learned_level_tracking_valid = false;
        self.learned.clear();
        self.learned.extend_from_slice(lits);
    }

    /// Get the asserting literal (1UIP negated)
    #[inline]
    pub(crate) fn asserting_literal(&self) -> Literal {
        self.asserting_lit
            .expect("asserting_literal called before set")
    }

    /// Get learned literal count (avoids borrow when iterating by index)
    #[inline]
    pub(crate) fn learned_count(&self) -> usize {
        self.learned.len()
    }

    /// Get learned literal at index (avoids borrow when iterating by index)
    #[inline]
    pub(crate) fn learned_at(&self, i: usize) -> Literal {
        self.learned[i]
    }

    /// Get mutable access to the clause buffer for reuse in conflict analysis
    #[inline]
    pub(crate) fn clause_buf_mut(&mut self) -> &mut Vec<Literal> {
        &mut self.clause_buf
    }

    /// Bulk copy learned literals to clause_buf (memcpy-speed).
    ///
    /// Replaces the per-element push loop with `extend_from_slice` for
    /// memcpy-speed bulk copy (#8569). Both `learned` and `clause_buf` are
    /// fields of the same struct, so this method accesses both within a
    /// single `&mut self` borrow (no borrow conflict).
    #[inline]
    pub(crate) fn copy_learned_to_clause_buf(&mut self) {
        self.clause_buf.clear();
        self.clause_buf.extend_from_slice(&self.learned);
    }

    /// Compute the backtrack level from the learned clause.
    /// This is the second-highest decision level among the literals,
    /// or 0 if the learned clause is unit.
    pub(crate) fn compute_backtrack_level(&self, var_data: &[VarData]) -> u32 {
        if self.learned.is_empty() {
            // Unit learned clause - backtrack to level 0
            return 0;
        }

        // Find the highest level among non-asserting literals
        let mut max_level = 0;
        for &lit in &self.learned {
            let var_level = var_data[lit.variable().index()].level;
            if var_level > max_level {
                max_level = var_level;
            }
        }
        max_level
    }

    /// Fused replacement for `compute_backtrack_level` + the scan inside
    /// `reorder_for_watches` (#8790).
    ///
    /// Returns `(backtrack_level, swap_learned_idx)` where:
    /// - `backtrack_level` == `compute_backtrack_level(var_data)` exactly
    ///   (maximum level over the learned literals; 0 when unit), and
    /// - `swap_learned_idx` is the first learned index `j >= 1` with
    ///   `level(learned[j]) == backtrack_level`, or `usize::MAX` when none
    ///   exists. After the UIP prepend in `get_result`, learned index `j`
    ///   becomes clause index `j + 1`, which is exactly the literal
    ///   `reorder_for_watches` swaps into watch slot 1. When `usize::MAX`,
    ///   only `learned[0]` (clause slot 1) attains the backtrack level and
    ///   `reorder_for_watches`'s fallback loop performs no swap.
    ///
    /// Uses the O(1) incremental tracking from `add_to_learned_tracked` when
    /// still valid (learned clause untouched by shrink/minimize), otherwise a
    /// single O(clause_len) pass replacing the previous two.
    pub(crate) fn backtrack_level_and_watch_swap(&self, var_data: &[VarData]) -> (u32, usize) {
        if self.learned.is_empty() {
            // Unit learned clause - backtrack to level 0, nothing to reorder.
            return (0, usize::MAX);
        }
        if self.learned_level_tracking_valid {
            let tracked = (self.learned_max_level, self.learned_max_swap_idx);
            debug_assert_eq!(
                tracked,
                self.scan_backtrack_level_and_watch_swap(var_data),
                "BUG(#8790): incrementally tracked (backtrack_level, swap_idx) \
                 diverges from learned-clause rescan"
            );
            return tracked;
        }
        self.scan_backtrack_level_and_watch_swap(var_data)
    }

    /// Single-pass computation backing `backtrack_level_and_watch_swap`.
    fn scan_backtrack_level_and_watch_swap(&self, var_data: &[VarData]) -> (u32, usize) {
        let mut max_level = 0u32;
        let mut swap_idx = usize::MAX;
        for (i, &lit) in self.learned.iter().enumerate() {
            let level = var_data[lit.variable().index()].level;
            if level > max_level {
                max_level = level;
                swap_idx = if i >= 1 { i } else { usize::MAX };
            } else if level == max_level && swap_idx == usize::MAX && i >= 1 {
                swap_idx = i;
            }
        }
        (max_level, swap_idx)
    }
}
