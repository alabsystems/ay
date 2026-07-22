// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Centralized model-equality policy for incremental DPLL(T) pipelines.
//!
//! Extracted from duplicated inline logic across 4+ pipeline macro paths
//! (#6851, #6846). This module is the single source of truth for:
//!
//! 1. Recording repeated `(lhs, rhs)` requests for diagnostics
//! 2. Global round-budget enforcement for termination
//! 3. Deduplication of triangle axiom clauses for persistent theories
//!
//! The key invariant: the tracker never returns an abort signal for individual
//! pairs. The algorithm has no per-pair retry threshold. Only the global round
//! budget limits total model-equality iterations across all pairs.
//!
//! The actual SAT encoding (atom creation, phase bias, VSIDS bump, triangle
//! axioms) remains in the `pipeline_encode_model_equality!` macro because it
//! requires `&mut TermStore` for `mk_eq`/`mk_le` calls. This module owns
//! the *policy* (when to encode, when to abort), not the *mechanism*.
//!
//! Reference: Z3 `arith_eq_adapter::mk_axioms` uses `m_already_processed` for
//! deduplication, not an abort threshold (`reference/z3/src/smt/arith_eq_adapter.cpp:81-231`).

// #8529: Use deterministic hash maps/sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;

use std::sync::{Arc, Mutex};

/// Tracks model-equality requests for diagnostics and global round budgeting.
///
/// Each incremental pipeline path should hold exactly one instance of this
/// tracker across all split-loop iterations. The tracker enforces:
///
/// - Per-pair request counting (diagnostic only, no abort)
/// - Global round budget (returns exhausted when exceeded)
/// - Deduplication of triangle axiom clauses for persistent theories
///
/// # Why no per-pair abort
///
/// The prior implementation (#6846) had `if *retry > 2 { return Unknown }`
/// in the no-split path, which caused false-SAT results. The Z3 reference
/// (`arith_eq_adapter`) uses deduplication, not an abort threshold. CDCL
/// converges by learning blocking clauses; aborting early is unsound.
#[derive(Debug)]
pub(crate) struct ModelEqualityTracker {
    /// Global round counter. Incremented once per NeedModelEquality/
    /// NeedModelEqualities dispatch (not per pair).
    rounds: usize,
    /// Maximum global rounds before returning exhausted.
    max_rounds: usize,
    /// Equality atoms whose triangle axioms have already been added.
    /// Used by persistent-theory paths to avoid re-adding identical clauses.
    added_triangle_atoms: HashSet<TermId>,
    /// Expression-split disequality terms whose encode round added NOTHING
    /// new (split clause, mutex clause, and index lemma all deduplicated).
    /// A repeat request for such a term is provably unproductive — the SAT
    /// solver already searched with every clause the split can contribute —
    /// so the lazy dispatch treats it like a stale model-equality request
    /// (#1771): fall through to the Sat handler and let the fail-closed
    /// model-validation gates decide. Without this, an EUF-derived shared
    /// disequality whose violated variable pair is disjoint from the split
    /// atoms livelocks the lazy loop re-requesting the same split every
    /// round (observed: false_unsat_array_ite_store_index, 1276 identical
    /// requests for one term until the 60s budget).
    stale_expr_splits: HashSet<TermId>,
}

impl ModelEqualityTracker {
    /// Create a new tracker with the given global round budget.
    pub(crate) fn new(max_rounds: usize) -> Self {
        Self {
            rounds: 0,
            max_rounds,
            added_triangle_atoms: HashSet::default(),
            stale_expr_splits: HashSet::default(),
        }
    }

    /// Record that an expression-split encode round for `diseq_term` added no
    /// new SAT-visible clause (fully deduplicated request).
    pub(crate) fn mark_stale_expr_split(&mut self, diseq_term: TermId) {
        self.stale_expr_splits.insert(diseq_term);
    }

    /// Whether a previous encode round for `diseq_term` was fully
    /// deduplicated, i.e. a repeat request can add nothing new.
    pub(crate) fn is_stale_expr_split(&self, diseq_term: TermId) -> bool {
        self.stale_expr_splits.contains(&diseq_term)
    }

    /// Increment the global round counter. Returns `true` if the budget is
    /// exhausted (caller should return Unknown), `false` if the round is allowed.
    ///
    /// Call this once per NeedModelEquality/NeedModelEqualities dispatch,
    /// NOT once per pair within a batch.
    pub(crate) fn increment_round(&mut self) -> bool {
        self.rounds += 1;
        self.rounds > self.max_rounds
    }

    /// Reset the round counter when a theory has made real progress.
    ///
    /// The round budget (#6851) exists to prevent infinite model-equality
    /// loops where the theory keeps emitting the same requests without the
    /// SAT solver learning anything new. When the SAT solver has learned at
    /// least one theory-conflict clause since the last call to this method,
    /// the solver *is* making progress and the budget should reset — otherwise
    /// benchmarks that need >`max_rounds` genuine theory conflicts to close
    /// will be falsely cut off as "incomplete" (#8727).
    ///
    /// Call this once per split-loop iteration, right after the SAT solve
    /// returns its theory-conflict count. When `num_theory_conflicts > 0`,
    /// the round counter is reset to zero. When it is zero (pure
    /// model-equality cycling with no new conflicts learned), the budget
    /// continues to count down so the loop still terminates.
    pub(crate) fn note_theory_progress(&mut self, num_theory_conflicts: u64) {
        if num_theory_conflicts > 0 {
            self.rounds = 0;
        }
    }

    /// Check whether triangle axiom clauses should be added for an equality atom.
    /// Returns `true` on the first call for a given atom (add the clauses),
    /// `false` on subsequent calls (already added).
    ///
    /// Used by persistent-theory paths where the same model equality may be
    /// requested many times while converging. Non-persistent paths always
    /// add triangle clauses (pass `true` to `pipeline_encode_model_equality!`).
    #[allow(dead_code)]
    pub(crate) fn should_add_triangle(&mut self, eq_atom: TermId) -> bool {
        self.added_triangle_atoms.insert(eq_atom)
    }

    /// Current round count (for diagnostics/logging).
    #[allow(dead_code)]
    pub(crate) fn rounds(&self) -> usize {
        self.rounds
    }

    /// Mutable access to the triangle-axiom deduplication set.
    ///
    /// Used by `pipeline_encode_model_equality!`'s `added_model_eqs:` variant
    /// which calls `.insert(eq_atom)` to determine whether to add triangle
    /// clauses. Returns the inner `HashSet<TermId>` so the macro can call
    /// `.insert()` directly.
    pub(crate) fn triangle_atoms_mut(&mut self) -> &mut HashSet<TermId> {
        &mut self.added_triangle_atoms
    }
}

/// Default global round budget for lazy and assumption split-loop arms.
///
/// These arms recreate the theory each iteration, so convergence is slower.
/// The budget must be high enough to allow AUFLIA model equalities to flow
/// until CDCL converges, but finite for termination.
pub(crate) const MODEL_EQ_MAX_ROUNDS_SPLIT: usize = 100;

/// Global round budget for the non-persistent eager arm.
///
/// Lower than the lazy/assume budget because the eager arm has a separate
/// no-progress iteration counter (`_ISLP_MAX_NO_PROGRESS_ITERS`) for
/// termination.
pub(crate) const MODEL_EQ_MAX_ROUNDS_EAGER: usize = 20;

/// Global round budget for the eager-persistent arm.
///
/// Same as the non-persistent eager arm. The persistent theory retains
/// convergence state, so fewer rounds are needed.
pub(crate) const MODEL_EQ_MAX_ROUNDS_EAGER_PERSISTENT: usize = 20;

/// Global round budget for the no-split incremental path.
///
/// The no-split path has no split-loop iteration counter, so this is the
/// only termination guard for model-equality divergence. Set high enough
/// to allow AUFLIA convergence.
pub(crate) const MODEL_EQ_MAX_ROUNDS_NO_SPLIT: usize = 100;

// =============================================================================
// Rescue-pair counter (#6367)
// =============================================================================

/// Persistent per-pair counter for array-rescue model equalities (#6367).
///
/// The `try_array_rescue_on_arith_conflict` path converts a LIA conflict into
/// a `NeedModelEquality` over some pair `(lhs, rhs)` when the arithmetic
/// infeasibility is conditional on an index equality that arrays can still
/// prove. When CDCL already encoded that equality and the next iteration
/// returns the *same* LIA Farkas conflict, re-requesting the same model
/// equality drives an infinite loop — the TL5 trace on
/// `qf_auflia_array_sum_bound` shows ~102 identical rescues for a single
/// pair (Discriminant(9)) before refinement cap.
///
/// The TheoryCombiner is recreated every outer refinement iteration, so a
/// counter on the combiner resets to zero each pass and cannot observe
/// cross-iteration divergence. This counter lives in the pipeline state
/// (outside `create_theory`) and is wired into each fresh combiner via an
/// `Arc<Mutex<>>` shared handle, mirroring how `ModelEqualityTracker` is
/// held across split-loop iterations.
///
/// The counter is deliberately conservative: it only *gates* the rescue. Once
/// a pair has been rescued more than the budget, the next rescue for that
/// pair is suppressed and the original arithmetic `UnsatWithFarkas` stands.
/// This is sound because the LIA conflict is always a valid refutation of
/// the current assignment — the rescue exists only as an optimization that
/// lets arrays inject an implied index equality instead of blocking on the
/// arithmetic conflict. When the rescue fails to make progress, falling
/// back to the conflict is the correct behaviour.
#[derive(Debug, Default)]
pub(crate) struct RescuePairCounter {
    /// Count of rescues that have been emitted for each normalized `(a, b)`
    /// pair. The pair is normalized so `(x, y)` and `(y, x)` share a counter.
    counts: HashMap<(TermId, TermId), u32>,
}

impl RescuePairCounter {
    /// Create an empty counter.
    pub(crate) fn new() -> Self {
        Self {
            counts: HashMap::default(),
        }
    }

    /// Normalize a `(lhs, rhs)` pair so `(x, y)` and `(y, x)` share a counter.
    fn normalize(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    /// Record a rescue for the given pair and return `true` if the per-pair
    /// budget has been exhausted (caller should refuse the rescue).
    pub(crate) fn record_and_check_exhausted(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        budget: u32,
    ) -> bool {
        let key = Self::normalize(lhs, rhs);
        let count = self.counts.entry(key).or_insert(0);
        *count = count.saturating_add(1);
        *count > budget
    }

    /// Return the current count for a pair (diagnostics/tests only).
    #[cfg(test)]
    pub(crate) fn count(&self, lhs: TermId, rhs: TermId) -> u32 {
        let key = Self::normalize(lhs, rhs);
        self.counts.get(&key).copied().unwrap_or(0)
    }

    /// Return `true` if any pair has exceeded the budget (diagnostics/tests).
    #[cfg(test)]
    pub(crate) fn is_exhausted(&self, lhs: TermId, rhs: TermId, budget: u32) -> bool {
        self.count(lhs, rhs) > budget
    }
}

/// Shared handle to the rescue-pair counter.
///
/// The pipeline holds the authoritative counter in its state. Each fresh
/// `TheoryCombiner` created inside the split loop receives a clone of the
/// `Arc<Mutex<>>` so all combiner instantiations across iterations share the
/// same counts.
pub(crate) type SharedRescuePairCounter = Arc<Mutex<RescuePairCounter>>;

/// Default per-pair rescue budget for array rescues over arithmetic conflicts.
///
/// Picked large enough that legitimate SAT rescues (e.g.,
/// `test_auflia_multi_assume_different_stores_6736`) never consume the budget,
/// but small enough that the 102-iteration divergence on
/// `qf_auflia_array_sum_bound` terminates quickly.
///
/// TL5's trace shows:
///  - `qf_auflia_array_sum_bound` requires ≤1 rescue per pair when the
///    conflict is legitimately resolved; when it diverges, the *same* pair
///    fires 102 times without progress. 32 stops divergence at ~32× the
///    useful count while leaving ample headroom.
///  - `test_auflia_multi_assume_different_stores_6736` uses rescues on the
///    SAT side; observed count in passing runs is < 4 per pair.
pub(crate) const DEFAULT_RESCUE_PAIR_BUDGET: u32 = 32;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracker_round_budget_enforcement() {
        let mut tracker = ModelEqualityTracker::new(3);
        assert!(!tracker.increment_round()); // round 1
        assert!(!tracker.increment_round()); // round 2
        assert!(!tracker.increment_round()); // round 3
        assert!(tracker.increment_round()); // round 4 > 3, exhausted
    }

    #[test]
    fn test_tracker_round_budget_zero() {
        let mut tracker = ModelEqualityTracker::new(0);
        assert!(tracker.increment_round()); // round 1 > 0, immediately exhausted
    }

    #[test]
    fn test_tracker_triangle_dedup() {
        let mut tracker = ModelEqualityTracker::new(10);
        let atom = TermId(42);
        assert!(tracker.should_add_triangle(atom)); // first time: add
        assert!(!tracker.should_add_triangle(atom)); // second time: skip
        assert!(tracker.should_add_triangle(TermId(43))); // different atom: add
    }

    #[test]
    fn test_tracker_rounds_counter() {
        let mut tracker = ModelEqualityTracker::new(10);
        assert_eq!(tracker.rounds(), 0);
        tracker.increment_round();
        assert_eq!(tracker.rounds(), 1);
        tracker.increment_round();
        assert_eq!(tracker.rounds(), 2);
    }

    // Verify the invariant from #6846: there is no per-pair abort mechanism.
    // The only abort is via the global round budget. This test ensures that
    // the tracker API does not expose any way to abort on a single pair.
    #[test]
    fn test_no_per_pair_abort_api() {
        let tracker = ModelEqualityTracker::new(1000);
        // The tracker has no note_pair/per-pair-abort method.
        // The only abort path is increment_round() which is per-dispatch,
        // not per-pair. This test documents that design invariant.
        assert_eq!(tracker.rounds(), 0);
    }

    // #8727: note_theory_progress must reset the round counter whenever
    // theory conflicts are learned, so benchmarks that require many
    // genuine theory conflicts (cascade_mod_8727) are not falsely cut off.
    #[test]
    fn test_note_theory_progress_resets_on_conflicts() {
        let mut tracker = ModelEqualityTracker::new(3);
        assert!(!tracker.increment_round()); // round 1
        assert!(!tracker.increment_round()); // round 2
        assert!(!tracker.increment_round()); // round 3
                                             // Theory learned one or more conflict clauses — real progress.
        tracker.note_theory_progress(1);
        assert_eq!(tracker.rounds(), 0, "one conflict must reset round counter");
        // After reset we should be allowed another full budget of rounds.
        assert!(!tracker.increment_round()); // round 1
        assert!(!tracker.increment_round()); // round 2
        assert!(!tracker.increment_round()); // round 3
        assert!(tracker.increment_round()); // round 4 > 3, exhausted
    }

    // #8727: note_theory_progress must NOT reset when no conflicts were
    // learned. Pure model-equality cycling without learning is the exact
    // failure mode that the round budget is meant to catch.
    #[test]
    fn test_note_theory_progress_no_reset_when_no_conflicts() {
        let mut tracker = ModelEqualityTracker::new(3);
        assert!(!tracker.increment_round()); // round 1
        assert!(!tracker.increment_round()); // round 2
        tracker.note_theory_progress(0); // no progress
        assert_eq!(tracker.rounds(), 2, "zero conflicts must not reset");
        assert!(!tracker.increment_round()); // round 3
        assert!(tracker.increment_round()); // round 4 > 3, exhausted
    }

    // #8727: Multiple conflicts behave the same as a single conflict —
    // any positive count means progress.
    #[test]
    fn test_note_theory_progress_many_conflicts() {
        let mut tracker = ModelEqualityTracker::new(3);
        tracker.increment_round();
        tracker.increment_round();
        tracker.note_theory_progress(42);
        assert_eq!(tracker.rounds(), 0);
    }

    // =========================================================================
    // RescuePairCounter tests (#6367)
    // =========================================================================

    #[test]
    fn test_rescue_pair_counter_budget_exhaustion() {
        let mut counter = RescuePairCounter::new();
        let lhs = TermId(10);
        let rhs = TermId(20);
        let budget = 3u32;
        // First three calls are within budget (count 1, 2, 3 <= 3)
        assert!(!counter.record_and_check_exhausted(lhs, rhs, budget));
        assert!(!counter.record_and_check_exhausted(lhs, rhs, budget));
        assert!(!counter.record_and_check_exhausted(lhs, rhs, budget));
        // Fourth call exceeds budget
        assert!(counter.record_and_check_exhausted(lhs, rhs, budget));
    }

    #[test]
    fn test_rescue_pair_counter_normalizes_order() {
        // Same pair asked in different orders must share the counter.
        let mut counter = RescuePairCounter::new();
        let a = TermId(10);
        let b = TermId(20);
        counter.record_and_check_exhausted(a, b, 100);
        counter.record_and_check_exhausted(b, a, 100);
        counter.record_and_check_exhausted(a, b, 100);
        assert_eq!(counter.count(a, b), 3);
        assert_eq!(counter.count(b, a), 3);
    }

    #[test]
    fn test_rescue_pair_counter_distinguishes_pairs() {
        let mut counter = RescuePairCounter::new();
        let a = TermId(10);
        let b = TermId(20);
        let c = TermId(30);
        counter.record_and_check_exhausted(a, b, 100);
        counter.record_and_check_exhausted(a, b, 100);
        counter.record_and_check_exhausted(a, c, 100);
        assert_eq!(counter.count(a, b), 2);
        assert_eq!(counter.count(a, c), 1);
        assert_eq!(counter.count(b, c), 0);
    }

    #[test]
    fn test_rescue_pair_counter_zero_budget_immediately_exhausted() {
        let mut counter = RescuePairCounter::new();
        let a = TermId(10);
        let b = TermId(20);
        // Budget zero means the very first rescue exhausts.
        assert!(counter.record_and_check_exhausted(a, b, 0));
    }

    #[test]
    fn test_rescue_pair_counter_is_exhausted() {
        let mut counter = RescuePairCounter::new();
        let a = TermId(10);
        let b = TermId(20);
        counter.record_and_check_exhausted(a, b, 2);
        counter.record_and_check_exhausted(a, b, 2);
        assert!(!counter.is_exhausted(a, b, 2));
        counter.record_and_check_exhausted(a, b, 2);
        assert!(counter.is_exhausted(a, b, 2));
    }

    #[test]
    fn test_rescue_pair_counter_default_is_empty() {
        let counter = RescuePairCounter::default();
        assert_eq!(counter.count(TermId(1), TermId(2)), 0);
    }
}
