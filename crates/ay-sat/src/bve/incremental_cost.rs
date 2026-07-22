// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Incremental elimination-cost tracker for mid-search BVE (Phase 1, #8795).
//!
//! Implements the per-variable running cost estimator from
//! the development design notes. Each variable carries a
//! coarse `u32` cost proxy that is:
//!
//! * **decremented** when a clause containing the variable is discovered to
//!   be satisfied by the current trail (one resolvent fewer to generate if
//!   the variable were eliminated), and
//! * **recomputed** when a clause is learned that mentions the variable
//!   (learned clauses add real elimination work).
//!
//! Both hooks are O(clause width) and free of heap allocation once the
//! per-variable buffers are sized. `on_backtrack` marks touched state as
//! dirty so the next scan re-examines the affected variables without
//! double-counting conflict-local decrements.
//!
//! ## Phase 1 scope
//!
//! * Pure data structure. No CDCL-loop wiring yet — that is Phase 2.
//! * Does **not** perform any elimination or proof emission.
//! * Emphasis is on (a) a deterministic API surface that survives the
//!   Phase 2 wiring pass, and (b) total independence from the rest of
//!   the `bve` module so this file can move without churn.
//!
//! ## Cost semantics
//!
//! The concrete cost function is intentionally simple: `cost_by_var[v]`
//! starts at the variable's initial occurrence count (set via
//! [`IncrementalCostTracker::set_initial_cost`]) and is mutated by the
//! hooks below. Phase 2 will refine the model (gate-pair credits, learned
//! clause weighting) — the public API here does not need to change for
//! those refinements.

use crate::literal::{Literal, Variable};

/// Saturating-`u32` cost proxy for one variable.
pub(crate) type Cost = u32;

/// Per-variable elimination-cost tracker.
///
/// Invariants (Phase 1):
///
/// * `cost_by_var.len() == dirty.len()`
/// * `dirty[i] == true` means `cost_by_var[i]` may be stale and the next
///   trigger-evaluation pass should refresh or skip it.
/// * `events_processed` increases monotonically; resets only on `clear()`.
#[derive(Debug, Clone, Default)]
pub(crate) struct IncrementalCostTracker {
    /// Current cost estimate for each variable, indexed by `Variable::index()`.
    cost_by_var: Vec<Cost>,
    /// Dirty bitset — variables whose cost may be out of date.
    ///
    /// Phase 1 uses `Vec<bool>` (byte bitset) for simplicity and to match
    /// the BVE module's existing `candidate_dirty` style. A packed bitset
    /// (`bitvec::BitVec`) is a Phase 2 swap if profiling shows cache
    /// pressure.
    dirty: Vec<bool>,
    /// Number of hook events observed, for diagnostics.
    events_processed: u64,
}

impl IncrementalCostTracker {
    /// Default starting cost for a variable with no known occurrences.
    pub(crate) const DEFAULT_COST: Cost = 0;

    /// Create a tracker sized for `num_vars` variables.
    ///
    /// All variables start at [`Self::DEFAULT_COST`] and are marked clean.
    #[must_use]
    pub(crate) fn with_num_vars(num_vars: usize) -> Self {
        Self {
            cost_by_var: vec![Self::DEFAULT_COST; num_vars],
            dirty: vec![false; num_vars],
            events_processed: 0,
        }
    }

    /// Resize internal buffers to accommodate at least `num_vars` variables.
    ///
    /// Existing cost/dirty entries are preserved. New entries start at
    /// [`Self::DEFAULT_COST`] and clean.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.cost_by_var.len() < num_vars {
            self.cost_by_var.resize(num_vars, Self::DEFAULT_COST);
            self.dirty.resize(num_vars, false);
        }
    }

    /// Number of variables currently tracked.
    #[must_use]
    pub(crate) fn num_vars(&self) -> usize {
        self.cost_by_var.len()
    }

    /// Read the current cost estimate for `var`.
    ///
    /// Returns [`Self::DEFAULT_COST`] for out-of-range variables.
    #[must_use]
    pub(crate) fn cost(&self, var: Variable) -> Cost {
        self.cost_by_var
            .get(var.index())
            .copied()
            .unwrap_or(Self::DEFAULT_COST)
    }

    /// Whether `var`'s cost entry is marked dirty.
    ///
    /// Out-of-range variables are reported as clean.
    #[must_use]
    pub(crate) fn is_dirty(&self, var: Variable) -> bool {
        self.dirty.get(var.index()).copied().unwrap_or(false)
    }

    /// Number of hook events observed. Monotonically non-decreasing until
    /// [`Self::clear`] is called.
    #[must_use]
    pub(crate) fn events_processed(&self) -> u64 {
        self.events_processed
    }

    /// Seed an initial per-variable cost (typically `pos_occs * neg_occs`
    /// computed once at the start of search).
    ///
    /// Out-of-range `var` is ignored so callers can seed optimistically
    /// without pre-sizing.
    pub(crate) fn set_initial_cost(&mut self, var: Variable, cost: Cost) {
        if let Some(slot) = self.cost_by_var.get_mut(var.index()) {
            *slot = cost;
            // A freshly-seeded variable is, by definition, clean.
            if let Some(d) = self.dirty.get_mut(var.index()) {
                *d = false;
            }
        }
    }

    /// Hook: a clause became satisfied by the current trail.
    ///
    /// For each variable in the clause, decrement its elimination cost by 1
    /// (saturating at 0). A satisfied clause contributes nothing to the set
    /// of resolvents required for future BVE of that variable.
    pub(crate) fn on_clause_sat(&mut self, clause: &[Literal]) {
        self.events_processed = self.events_processed.saturating_add(1);
        for &lit in clause {
            let idx = lit.variable().index();
            if let Some(slot) = self.cost_by_var.get_mut(idx) {
                *slot = slot.saturating_sub(1);
            }
        }
    }

    /// Hook: a clause was learned (added to the clause database).
    ///
    /// Each variable in the clause has its cost incremented by 1 (saturating
    /// at [`Cost::MAX`]) and marked dirty for reevaluation. Learned clauses
    /// expand the resolvent frontier; the dirty flag tells the next trigger
    /// pass to recompute the exact cost rather than trust the running tally.
    pub(crate) fn on_clause_learn(&mut self, clause: &[Literal]) {
        self.events_processed = self.events_processed.saturating_add(1);
        for &lit in clause {
            let idx = lit.variable().index();
            if let Some(slot) = self.cost_by_var.get_mut(idx) {
                *slot = slot.saturating_add(1);
            }
            if let Some(d) = self.dirty.get_mut(idx) {
                *d = true;
            }
        }
    }

    /// Hook: the solver backtracked to `new_level`.
    ///
    /// Phase 1 conservatively marks *all* tracked variables dirty: the next
    /// trigger pass should re-examine each candidate rather than trust
    /// conflict-era decrements. This is the safe default; Phase 2 will
    /// use the decision level to scope the re-dirty to variables whose
    /// reason clauses live above `new_level`.
    pub(crate) fn on_backtrack(&mut self, new_level: usize) {
        self.events_processed = self.events_processed.saturating_add(1);
        // `new_level` is recorded for Phase 2's per-level rollback; Phase 1
        // only needs to ensure no stale cost is used for triggering.
        let _ = new_level;
        self.dirty.fill(true);
    }

    /// Return every variable whose recorded cost is strictly below `k`.
    ///
    /// Dirty entries are included: the consumer is expected to re-verify
    /// candidates before acting on them. The result is sorted by variable
    /// id (ascending) so downstream scheduling is deterministic.
    #[must_use]
    pub(crate) fn variables_below_threshold(&self, k: Cost) -> Vec<Variable> {
        let mut out = Vec::new();
        for (idx, &cost) in self.cost_by_var.iter().enumerate() {
            if cost < k {
                out.push(Variable::new(idx as u32));
            }
        }
        // `idx` iteration already produces sorted output, but we keep an
        // explicit sort in case the storage layout ever changes.
        out.sort_by_key(|v| v.id());
        out
    }

    /// Clear a variable's dirty flag. Used by the trigger after it has
    /// fully re-evaluated the candidate.
    pub(crate) fn clear_dirty(&mut self, var: Variable) {
        if let Some(d) = self.dirty.get_mut(var.index()) {
            *d = false;
        }
    }

    /// Drop all state and reset counters. Intended for incremental-solver
    /// restarts where the clause database is rebuilt from scratch.
    pub(crate) fn clear(&mut self) {
        self.cost_by_var.fill(Self::DEFAULT_COST);
        self.dirty.fill(false);
        self.events_processed = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: u32) -> Variable {
        Variable::new(i)
    }

    fn pos(i: u32) -> Literal {
        Literal::positive(v(i))
    }

    fn neg(i: u32) -> Literal {
        Literal::negative(v(i))
    }

    #[test]
    fn test_with_num_vars_initializes_defaults() {
        let t = IncrementalCostTracker::with_num_vars(4);
        assert_eq!(t.num_vars(), 4);
        for i in 0..4 {
            assert_eq!(t.cost(v(i)), IncrementalCostTracker::DEFAULT_COST);
            assert!(!t.is_dirty(v(i)));
        }
        assert_eq!(t.events_processed(), 0);
    }

    #[test]
    fn test_cost_out_of_range_returns_default() {
        let t = IncrementalCostTracker::with_num_vars(2);
        assert_eq!(t.cost(v(99)), IncrementalCostTracker::DEFAULT_COST);
        assert!(!t.is_dirty(v(99)));
    }

    #[test]
    fn test_ensure_num_vars_preserves_existing_state() {
        let mut t = IncrementalCostTracker::with_num_vars(2);
        t.set_initial_cost(v(1), 42);
        t.ensure_num_vars(5);
        assert_eq!(t.num_vars(), 5);
        assert_eq!(t.cost(v(1)), 42);
        assert_eq!(t.cost(v(4)), IncrementalCostTracker::DEFAULT_COST);
    }

    #[test]
    fn test_set_initial_cost_clears_dirty() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.on_clause_learn(&[pos(0)]);
        assert!(t.is_dirty(v(0)));
        t.set_initial_cost(v(0), 7);
        assert_eq!(t.cost(v(0)), 7);
        assert!(!t.is_dirty(v(0)));
    }

    #[test]
    fn test_on_clause_sat_decrements_saturating() {
        let mut t = IncrementalCostTracker::with_num_vars(4);
        t.set_initial_cost(v(0), 3);
        t.set_initial_cost(v(1), 0);
        t.on_clause_sat(&[pos(0), neg(1), pos(2)]);
        assert_eq!(t.cost(v(0)), 2);
        assert_eq!(t.cost(v(1)), 0, "saturates at 0");
        assert_eq!(t.cost(v(2)), 0, "default - 1 saturates");
        assert_eq!(t.events_processed(), 1);
    }

    #[test]
    fn test_on_clause_learn_increments_and_marks_dirty() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.set_initial_cost(v(0), 5);
        t.on_clause_learn(&[pos(0), neg(1)]);
        assert_eq!(t.cost(v(0)), 6);
        assert_eq!(t.cost(v(1)), 1);
        assert!(t.is_dirty(v(0)));
        assert!(t.is_dirty(v(1)));
        assert!(!t.is_dirty(v(2)));
        assert_eq!(t.events_processed(), 1);
    }

    #[test]
    fn test_on_clause_learn_saturates_at_u32_max() {
        let mut t = IncrementalCostTracker::with_num_vars(1);
        t.set_initial_cost(v(0), u32::MAX);
        t.on_clause_learn(&[pos(0)]);
        assert_eq!(t.cost(v(0)), u32::MAX);
    }

    #[test]
    fn test_on_backtrack_marks_all_dirty() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.set_initial_cost(v(0), 4);
        t.set_initial_cost(v(1), 4);
        t.set_initial_cost(v(2), 4);
        assert!(!t.is_dirty(v(0)));
        t.on_backtrack(0);
        assert!(t.is_dirty(v(0)));
        assert!(t.is_dirty(v(1)));
        assert!(t.is_dirty(v(2)));
        assert_eq!(t.cost(v(0)), 4, "cost values unchanged by backtrack");
        assert_eq!(t.events_processed(), 1);
    }

    #[test]
    fn test_variables_below_threshold_returns_sorted() {
        let mut t = IncrementalCostTracker::with_num_vars(5);
        t.set_initial_cost(v(0), 10);
        t.set_initial_cost(v(1), 2);
        t.set_initial_cost(v(2), 5);
        t.set_initial_cost(v(3), 1);
        t.set_initial_cost(v(4), 20);
        let got = t.variables_below_threshold(5);
        // v(1)=2 and v(3)=1 are below the threshold 5. v(0)=10, v(2)=5
        // (boundary — strict <), v(4)=20 are all at or above.
        assert_eq!(got, vec![v(1), v(3)]);
    }

    #[test]
    fn test_variables_below_threshold_strict_less_than() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.set_initial_cost(v(0), 5);
        t.set_initial_cost(v(1), 4);
        t.set_initial_cost(v(2), 6);
        let got = t.variables_below_threshold(5);
        assert_eq!(
            got,
            vec![v(1)],
            "boundary value (cost == threshold) is NOT included"
        );
    }

    #[test]
    fn test_variables_below_threshold_zero_is_empty() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.set_initial_cost(v(0), 0);
        t.set_initial_cost(v(1), 0);
        assert!(t.variables_below_threshold(0).is_empty());
    }

    #[test]
    fn test_default_cost_variables_are_candidates_at_any_positive_threshold() {
        let t = IncrementalCostTracker::with_num_vars(3);
        let got = t.variables_below_threshold(1);
        // All three default-cost variables qualify.
        assert_eq!(got, vec![v(0), v(1), v(2)]);
    }

    #[test]
    fn test_clear_dirty_resets_only_target_var() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.on_clause_learn(&[pos(0), pos(1)]);
        assert!(t.is_dirty(v(0)));
        assert!(t.is_dirty(v(1)));
        t.clear_dirty(v(0));
        assert!(!t.is_dirty(v(0)));
        assert!(t.is_dirty(v(1)));
    }

    #[test]
    fn test_clear_resets_state() {
        let mut t = IncrementalCostTracker::with_num_vars(3);
        t.set_initial_cost(v(0), 42);
        t.on_clause_learn(&[pos(0), pos(1)]);
        t.on_clause_sat(&[pos(0)]);
        assert!(t.events_processed() > 0);
        t.clear();
        assert_eq!(t.events_processed(), 0);
        assert_eq!(t.cost(v(0)), IncrementalCostTracker::DEFAULT_COST);
        assert_eq!(t.cost(v(1)), IncrementalCostTracker::DEFAULT_COST);
        assert!(!t.is_dirty(v(0)));
        assert!(!t.is_dirty(v(1)));
    }

    #[test]
    fn test_mixed_event_sequence_produces_expected_tally() {
        let mut t = IncrementalCostTracker::with_num_vars(2);
        t.set_initial_cost(v(0), 10);
        t.on_clause_learn(&[pos(0)]); // cost=11
        t.on_clause_learn(&[pos(0)]); // cost=12
        t.on_clause_sat(&[pos(0)]); //   cost=11
        t.on_clause_sat(&[pos(0)]); //   cost=10
        t.on_clause_sat(&[pos(0)]); //   cost=9
        assert_eq!(t.cost(v(0)), 9);
        assert_eq!(t.events_processed(), 5);
    }

    #[test]
    fn test_out_of_range_hook_literals_are_ignored() {
        let mut t = IncrementalCostTracker::with_num_vars(2);
        // v(9) is out of range; must not panic and must not grow buffers.
        t.on_clause_learn(&[pos(0), pos(9)]);
        t.on_clause_sat(&[neg(9)]);
        assert_eq!(t.num_vars(), 2);
        assert_eq!(t.cost(v(0)), 1);
        assert_eq!(t.cost(v(9)), IncrementalCostTracker::DEFAULT_COST);
    }
}
