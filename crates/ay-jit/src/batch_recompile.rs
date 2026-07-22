// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Batch profile scheduler for learned-clause descriptors.
//!
//! Implements the scheduling side of the "inspect every N conflicts" profile
//! plan from the development design notes. The
//! [`RecompileScheduler`] answers two questions:
//!
//! 1. **When** should a profile batch fire? →
//!    [`RecompileScheduler::on_conflict`].
//! 2. **Which** learned clauses should the batch include? →
//!    [`RecompileScheduler::select_candidates`].
//!
//! This module owns *only* the scheduling logic. Descriptor extraction lives in
//! [`crate::learned_clause_emit`], and that contract is profile-only: it does
//! not install native propagators or bypass scalar SAT propagation.

use crate::learned_clause_emit::LearnedClausePropagator;

/// Budget controlling how frequently and how broadly profile batches fire.
///
/// - `every_n_conflicts`: inspect exactly once per `N` conflicts. `0`
///   disables the scheduler (no batch will ever be triggered).
/// - `top_k_clauses`: maximum number of learned clauses to include in a single
///   batch. Selected by descending activity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BatchRecompileBudget {
    /// Conflicts between consecutive profile batches.
    pub every_n_conflicts: u64,
    /// Maximum number of clauses to profile per batch.
    pub top_k_clauses: usize,
}

impl BatchRecompileBudget {
    /// A conservative default. Solver-side profile wiring can make this
    /// adaptive to the formula size and learning rate.
    pub const DEFAULT: Self = Self {
        every_n_conflicts: 10_000,
        top_k_clauses: 64,
    };

    /// Returns `true` if this budget is effectively disabled.
    #[must_use]
    pub const fn is_disabled(&self) -> bool {
        self.every_n_conflicts == 0 || self.top_k_clauses == 0
    }
}

impl Default for BatchRecompileBudget {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Opaque identifier assigned to a learned clause by the solver.
///
/// Solver-side integrations should map this to their internal clause-reference
/// type; standalone tests use a plain `u64`.
pub type ClauseId = u64;

/// Compact metadata about a learned clause, used by the scheduler to pick
/// batch candidates.
///
/// The scheduler deliberately does not see the literals themselves — that
/// avoids coupling it to any specific `Literal` type and lets the solver hand
/// over only whatever metadata it already tracks.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LearnedClauseMeta {
    /// Solver-owned identifier.
    pub id: ClauseId,
    /// Activity score (VSIDS-like). Higher = hotter.
    pub activity: f64,
    /// Number of literals in the clause. Used as a tiebreaker and a proxy
    /// for future external code generation lowering cost.
    pub length: u32,
    /// `true` if this clause is already represented by a profile descriptor.
    /// The scheduler still allows re-selection so callers can refresh activity
    /// and epoch metadata deterministically.
    pub already_compiled: bool,
}

impl LearnedClauseMeta {
    /// Construct metadata for a freshly-learned clause.
    #[must_use]
    pub const fn new(id: ClauseId, activity: f64, length: u32) -> Self {
        Self {
            id,
            activity,
            length,
            already_compiled: false,
        }
    }
}

/// Scheduler that decides when to fire a profile batch and which clauses to
/// inspect.
///
/// The scheduler is purely *advisory*: it holds no state about native code,
/// makes no decisions about dispatch, and does not own propagators.
#[derive(Debug, Clone)]
pub struct RecompileScheduler {
    budget: BatchRecompileBudget,
    /// Conflict count at which the next batch is allowed to fire.
    next_trigger_at: u64,
    /// Number of batches fired so far (exposed via [`Self::batches_fired`]).
    batches_fired: u64,
}

impl RecompileScheduler {
    /// Create a scheduler with the given budget.
    ///
    /// If the budget is disabled, [`Self::on_conflict`] will never return
    /// `true`.
    #[must_use]
    pub fn new(budget: BatchRecompileBudget) -> Self {
        let next_trigger_at = budget.every_n_conflicts.max(1);
        Self {
            budget,
            next_trigger_at,
            batches_fired: 0,
        }
    }

    /// Report that the solver has reached `conflict_count` conflicts total.
    ///
    /// Returns `true` exactly when a profile batch should fire. The caller
    /// is then responsible for invoking [`Self::select_candidates`] and
    /// extracting descriptors through [`crate::learned_clause_emit`].
    ///
    /// The scheduler is monotonic: `conflict_count` is expected to be
    /// non-decreasing across calls. A regressed count is treated as "no new
    /// conflicts" and never triggers.
    pub fn on_conflict(&mut self, conflict_count: u64) -> bool {
        if self.budget.is_disabled() {
            return false;
        }
        if conflict_count < self.next_trigger_at {
            return false;
        }
        // Advance the trigger past `conflict_count` by whole intervals so that
        // a gap of >N conflicts (e.g., after a restart with bulk conflicts)
        // only fires once per call, not once per missed interval.
        let interval = self.budget.every_n_conflicts;
        let overshoot = conflict_count - self.next_trigger_at;
        let steps = overshoot / interval + 1;
        self.next_trigger_at = self
            .next_trigger_at
            .saturating_add(steps.saturating_mul(interval));
        self.batches_fired = self.batches_fired.saturating_add(1);
        true
    }

    /// Select up to `top_k_clauses` hottest clauses from `clauses`.
    ///
    /// Returns clause IDs sorted by descending activity, with `length` as a
    /// tiebreaker (shorter clauses preferred -- smaller future lowering cost).
    ///
    /// This does **not** consume the input; the solver typically re-feeds the
    /// same `LearnedClauseMeta` buffer each round with updated activity
    /// values.
    #[must_use]
    pub fn select_candidates(&self, clauses: &[LearnedClauseMeta]) -> Vec<ClauseId> {
        if self.budget.is_disabled() || clauses.is_empty() {
            return Vec::new();
        }
        let mut sorted: Vec<&LearnedClauseMeta> = clauses.iter().collect();
        sorted.sort_by(|a, b| {
            // Descending activity.
            b.activity
                .partial_cmp(&a.activity)
                .unwrap_or(std::cmp::Ordering::Equal)
                // Ascending length (shorter clauses preferred on ties).
                .then_with(|| a.length.cmp(&b.length))
                // Stable tiebreak by id so the output is deterministic.
                .then_with(|| a.id.cmp(&b.id))
        });
        sorted
            .into_iter()
            .take(self.budget.top_k_clauses)
            .map(|m| m.id)
            .collect()
    }

    /// Number of batches this scheduler has fired since construction.
    #[must_use]
    pub fn batches_fired(&self) -> u64 {
        self.batches_fired
    }

    /// Current budget.
    #[must_use]
    pub fn budget(&self) -> BatchRecompileBudget {
        self.budget
    }

    /// Replace the budget. Resets the next-trigger counter relative to the
    /// most recent conflict count the scheduler knows about (its current
    /// `next_trigger_at` floor).
    pub fn set_budget(&mut self, budget: BatchRecompileBudget) {
        // Preserve any progress by keeping `next_trigger_at` ≥ its old value.
        let old_floor = self.next_trigger_at;
        self.budget = budget;
        self.next_trigger_at = budget.every_n_conflicts.max(1).max(old_floor);
    }
}

impl Default for RecompileScheduler {
    fn default() -> Self {
        Self::new(BatchRecompileBudget::default())
    }
}

/// A tiny record of a single profile batch, returned by helpers that want to
/// bundle "fire the scheduler + collect selected oracle propagators" into one
/// call.
#[derive(Debug, Clone)]
pub struct RecompileBatchOutcome {
    /// Conflict count at which this batch fired.
    pub fired_at_conflicts: u64,
    /// Clauses included in the batch.
    pub selected: Vec<ClauseId>,
    /// Interpreted oracle propagators produced by the batch, if a caller opts
    /// in for differential/profile experiments.
    pub propagators: Vec<LearnedClausePropagator>,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disabled_budget_never_triggers() {
        let mut s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 0,
            top_k_clauses: 16,
        });
        assert!(!s.on_conflict(0));
        assert!(!s.on_conflict(1_000));
        assert!(!s.on_conflict(1_000_000));
        assert_eq!(s.batches_fired(), 0);
    }

    #[test]
    fn zero_top_k_budget_is_disabled() {
        let b = BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 0,
        };
        assert!(b.is_disabled());
        let mut s = RecompileScheduler::new(b);
        assert!(!s.on_conflict(1_000));
    }

    #[test]
    fn scheduler_fires_at_interval_boundaries() {
        let mut s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 4,
        });
        assert!(!s.on_conflict(1));
        assert!(!s.on_conflict(50));
        assert!(!s.on_conflict(99));
        assert!(s.on_conflict(100));
        assert_eq!(s.batches_fired(), 1);
        assert!(!s.on_conflict(101));
        assert!(!s.on_conflict(199));
        assert!(s.on_conflict(200));
        assert_eq!(s.batches_fired(), 2);
        assert!(s.on_conflict(300));
        assert_eq!(s.batches_fired(), 3);
    }

    #[test]
    fn scheduler_skips_missed_intervals_in_one_fire() {
        // If conflicts jump from 10 to 10_000 (e.g., after a big restart),
        // we fire exactly once, not 99 times.
        let mut s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 4,
        });
        assert!(s.on_conflict(10_000));
        assert_eq!(s.batches_fired(), 1);
        // Next trigger should be at 10_100, not 200.
        assert!(!s.on_conflict(10_050));
        assert!(s.on_conflict(10_100));
        assert_eq!(s.batches_fired(), 2);
    }

    #[test]
    fn scheduler_ignores_regressed_conflict_counts() {
        let mut s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 4,
        });
        assert!(s.on_conflict(100));
        assert!(!s.on_conflict(50)); // regression — no new trigger
        assert_eq!(s.batches_fired(), 1);
    }

    #[test]
    fn select_candidates_returns_top_k_by_activity() {
        let s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 3,
        });
        let clauses = vec![
            LearnedClauseMeta::new(1, 0.5, 4),
            LearnedClauseMeta::new(2, 0.9, 3),
            LearnedClauseMeta::new(3, 0.1, 10),
            LearnedClauseMeta::new(4, 0.7, 5),
            LearnedClauseMeta::new(5, 0.3, 2),
        ];
        let picks = s.select_candidates(&clauses);
        // Ordered by activity desc: 2 (0.9), 4 (0.7), 1 (0.5).
        assert_eq!(picks, vec![2, 4, 1]);
    }

    #[test]
    fn select_candidates_breaks_ties_by_length_then_id() {
        let s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 4,
        });
        let clauses = vec![
            LearnedClauseMeta::new(1, 0.5, 10),
            LearnedClauseMeta::new(2, 0.5, 3), // shorter, same activity → wins
            LearnedClauseMeta::new(3, 0.5, 3), // same activity+length → higher id
            LearnedClauseMeta::new(4, 0.5, 5),
        ];
        let picks = s.select_candidates(&clauses);
        assert_eq!(picks, vec![2, 3, 4, 1]);
    }

    #[test]
    fn select_candidates_honours_top_k_cap() {
        let s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 2,
        });
        let clauses = vec![
            LearnedClauseMeta::new(1, 0.9, 4),
            LearnedClauseMeta::new(2, 0.8, 4),
            LearnedClauseMeta::new(3, 0.7, 4),
            LearnedClauseMeta::new(4, 0.6, 4),
        ];
        let picks = s.select_candidates(&clauses);
        assert_eq!(picks, vec![1, 2]);
    }

    #[test]
    fn select_candidates_empty_input_returns_empty() {
        let s = RecompileScheduler::default();
        assert!(s.select_candidates(&[]).is_empty());
    }

    #[test]
    fn select_candidates_disabled_scheduler_returns_empty() {
        let s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 0,
            top_k_clauses: 8,
        });
        let clauses = vec![LearnedClauseMeta::new(1, 1.0, 3)];
        assert!(s.select_candidates(&clauses).is_empty());
    }

    #[test]
    fn set_budget_does_not_regress_trigger_floor() {
        let mut s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 1_000,
            top_k_clauses: 8,
        });
        assert!(s.on_conflict(1_000));
        // Shrink the interval; we must not retroactively fire batches for
        // conflicts we already passed.
        s.set_budget(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 8,
        });
        assert!(!s.on_conflict(1_500));
        assert!(s.on_conflict(2_000));
    }

    #[test]
    fn default_budget_matches_documented_constant() {
        let d = BatchRecompileBudget::default();
        assert_eq!(d, BatchRecompileBudget::DEFAULT);
        assert!(!d.is_disabled());
    }

    #[test]
    fn nan_activity_is_sorted_deterministically() {
        // Defensive: f64::NaN in activity must not panic and should not bubble
        // to the top.
        let s = RecompileScheduler::new(BatchRecompileBudget {
            every_n_conflicts: 100,
            top_k_clauses: 3,
        });
        let clauses = vec![
            LearnedClauseMeta::new(1, f64::NAN, 3),
            LearnedClauseMeta::new(2, 0.5, 4),
            LearnedClauseMeta::new(3, 0.9, 5),
        ];
        let picks = s.select_candidates(&clauses);
        assert_eq!(picks.len(), 3);
        // Regardless of where NaN ends up, 3 (0.9) outranks 2 (0.5).
        let pos3 = picks.iter().position(|&id| id == 3).unwrap();
        let pos2 = picks.iter().position(|&id| id == 2).unwrap();
        assert!(pos3 < pos2);
    }
}
