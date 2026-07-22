// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mid-search BVE trigger policy (Phase 1, #8795).
//!
//! The trigger consumes an [`IncrementalCostTracker`] plus a small snapshot
//! of solver progress and decides whether the CDCL loop should invoke a
//! mid-search bounded-variable-elimination pass.
//!
//! ## Phase 1 scope
//!
//! * **No CDCL wiring.** The trigger is callable in isolation so Phase 2
//!   can plug it into `solver/solve/inprocessing_schedule.rs` without
//!   touching this file's public API.
//! * **Heuristic, not adaptive.** The policy is a static conflict-interval
//!   gate. Phase 2 will add adaptive pacing based on measured elimination
//!   yield.
//! * **Zero side effects.** `should_trigger_incremental_bve` only reads
//!   inputs; it does not mutate the tracker or run BVE.

use super::incremental_cost::{Cost, IncrementalCostTracker};

/// Minimal progress signal the trigger needs from the solver.
///
/// Phase 2 will replace this with a real `SolverStats` reference once the
/// trigger is wired into the CDCL loop. Defining it locally keeps this
/// module compilable in isolation and avoids import cycles in Phase 1.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct TriggerSignal {
    /// Total conflicts seen by the solver.
    pub(crate) conflicts: u64,
    /// Current decision level. Phase 2 may require `level == 0` for some
    /// elimination modes; Phase 1 does not gate on it directly but exposes
    /// it to the policy function for future use.
    pub(crate) decision_level: usize,
}

/// Policy configuration for the mid-search BVE trigger.
///
/// Fields are internal — Phase 1 callers construct this via
/// [`TriggerPolicy::default`] or the `with_*` builder methods.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TriggerPolicy {
    /// Fire the trigger at most once per this many conflicts.
    ///
    /// CaDiCaL's inprocessing schedule waits a few thousand conflicts
    /// between passes; we start at 2_000 and let Phase 2 tune.
    conflict_interval: u64,
    /// Fire only if the tracker reports at least this many variables below
    /// the cost threshold. Avoids scheduling for a handful of cheap vars
    /// when the inprocessing overhead would dominate.
    min_candidates: usize,
    /// Cost threshold passed to
    /// [`IncrementalCostTracker::variables_below_threshold`] when counting.
    cost_threshold: Cost,
}

impl TriggerPolicy {
    /// Default conflict interval (conflicts between trigger firings).
    pub(crate) const DEFAULT_CONFLICT_INTERVAL: u64 = 2_000;
    /// Default minimum number of cheap candidates required to trigger.
    pub(crate) const DEFAULT_MIN_CANDIDATES: usize = 16;
    /// Default cost threshold: variables with `cost < 2` are "cheap".
    pub(crate) const DEFAULT_COST_THRESHOLD: Cost = 2;

    /// Construct a policy from explicit tuning knobs. Phase 1 exposes this
    /// for tests; production code should prefer [`Self::default`].
    #[must_use]
    pub(crate) fn new(conflict_interval: u64, min_candidates: usize, cost_threshold: Cost) -> Self {
        Self {
            conflict_interval,
            min_candidates,
            cost_threshold,
        }
    }

    /// Conflict interval this policy is configured with.
    #[must_use]
    pub(crate) fn conflict_interval(&self) -> u64 {
        self.conflict_interval
    }

    /// Minimum candidate count this policy requires.
    #[must_use]
    pub(crate) fn min_candidates(&self) -> usize {
        self.min_candidates
    }

    /// Cost threshold this policy uses to classify candidates.
    #[must_use]
    pub(crate) fn cost_threshold(&self) -> Cost {
        self.cost_threshold
    }
}

impl Default for TriggerPolicy {
    fn default() -> Self {
        Self::new(
            Self::DEFAULT_CONFLICT_INTERVAL,
            Self::DEFAULT_MIN_CANDIDATES,
            Self::DEFAULT_COST_THRESHOLD,
        )
    }
}

/// Runtime state for the trigger. Remembers when it last fired so the
/// conflict-interval gate can be evaluated incrementally.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct TriggerState {
    /// Total conflicts observed at the last trigger firing. `0` before any
    /// firing, which also matches the initial `conflicts` of a fresh
    /// solver.
    last_fired_at_conflicts: u64,
}

impl TriggerState {
    /// Number of conflicts since the last firing.
    #[must_use]
    pub(crate) fn conflicts_since_last_fire(&self, now: u64) -> u64 {
        now.saturating_sub(self.last_fired_at_conflicts)
    }

    /// Record that the trigger fired at `conflicts`.
    pub(crate) fn note_fired(&mut self, conflicts: u64) {
        self.last_fired_at_conflicts = conflicts;
    }
}

/// Decide whether to run a mid-search BVE pass.
///
/// Returns `true` iff **all** of the following hold:
///
/// 1. At least [`TriggerPolicy::conflict_interval`] conflicts have occurred
///    since the previous firing (or since solver start).
/// 2. The tracker reports at least [`TriggerPolicy::min_candidates`]
///    variables below [`TriggerPolicy::cost_threshold`].
///
/// Callers that want to advance the conflict gate should pair this check
/// with [`TriggerState::note_fired`] on a true return.
///
/// Phase 1: no side effects. Phase 2 will extend this to consult
/// `scope.rs` (not yet written) and gate on `decision_level == 0` for the
/// "eliminate at restart only" safety mode.
#[must_use]
pub(crate) fn should_trigger_incremental_bve(
    tracker: &IncrementalCostTracker,
    signal: &TriggerSignal,
    policy: &TriggerPolicy,
    state: &TriggerState,
) -> bool {
    if state.conflicts_since_last_fire(signal.conflicts) < policy.conflict_interval {
        return false;
    }
    let candidate_count = tracker
        .variables_below_threshold(policy.cost_threshold)
        .len();
    candidate_count >= policy.min_candidates
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    fn v(i: u32) -> Variable {
        Variable::new(i)
    }

    fn pos(i: u32) -> Literal {
        Literal::positive(v(i))
    }

    fn tracker_with_cheap_vars(num_vars: usize, cheap_count: usize) -> IncrementalCostTracker {
        let mut t = IncrementalCostTracker::with_num_vars(num_vars);
        for i in 0..num_vars {
            // Seed every variable above the default cost threshold (2).
            t.set_initial_cost(v(i as u32), 10);
        }
        // Drop `cheap_count` of them below threshold.
        for i in 0..cheap_count {
            t.set_initial_cost(v(i as u32), 1);
        }
        t
    }

    #[test]
    fn test_default_policy_values() {
        let p = TriggerPolicy::default();
        assert_eq!(
            p.conflict_interval(),
            TriggerPolicy::DEFAULT_CONFLICT_INTERVAL
        );
        assert_eq!(p.min_candidates(), TriggerPolicy::DEFAULT_MIN_CANDIDATES);
        assert_eq!(p.cost_threshold(), TriggerPolicy::DEFAULT_COST_THRESHOLD);
    }

    #[test]
    fn test_state_reports_conflicts_since_last_fire() {
        let mut s = TriggerState::default();
        assert_eq!(s.conflicts_since_last_fire(1000), 1000);
        s.note_fired(1000);
        assert_eq!(s.conflicts_since_last_fire(1000), 0);
        assert_eq!(s.conflicts_since_last_fire(3500), 2500);
    }

    #[test]
    fn test_state_saturates_on_time_travel() {
        // Defensive: if a caller passes a smaller `now` than the recorded
        // last firing, saturating_sub keeps us at 0 instead of panicking.
        let mut s = TriggerState::default();
        s.note_fired(5_000);
        assert_eq!(s.conflicts_since_last_fire(1_000), 0);
    }

    #[test]
    fn test_no_trigger_below_conflict_interval() {
        let tracker = tracker_with_cheap_vars(64, 32);
        let policy = TriggerPolicy::default();
        let state = TriggerState::default();
        let signal = TriggerSignal {
            conflicts: policy.conflict_interval() - 1,
            decision_level: 0,
        };
        assert!(!should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));
    }

    #[test]
    fn test_trigger_fires_when_interval_and_candidates_met() {
        let tracker = tracker_with_cheap_vars(64, 32);
        let policy = TriggerPolicy::default();
        let state = TriggerState::default();
        let signal = TriggerSignal {
            conflicts: policy.conflict_interval(),
            decision_level: 3,
        };
        assert!(should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));
    }

    #[test]
    fn test_no_trigger_when_candidates_below_minimum() {
        let policy = TriggerPolicy::default();
        // Fewer cheap vars than the min-candidates gate.
        let tracker = tracker_with_cheap_vars(64, policy.min_candidates() - 1);
        let state = TriggerState::default();
        let signal = TriggerSignal {
            conflicts: policy.conflict_interval() * 10,
            decision_level: 0,
        };
        assert!(!should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));
    }

    #[test]
    fn test_trigger_resets_after_firing() {
        let tracker = tracker_with_cheap_vars(64, 32);
        let policy = TriggerPolicy::default();
        let mut state = TriggerState::default();
        let first = TriggerSignal {
            conflicts: policy.conflict_interval(),
            decision_level: 0,
        };
        assert!(should_trigger_incremental_bve(
            &tracker, &first, &policy, &state
        ));
        state.note_fired(first.conflicts);
        // Immediately after firing, the same conflict count must not
        // re-trigger.
        assert!(!should_trigger_incremental_bve(
            &tracker, &first, &policy, &state
        ));
        // Once another full interval has elapsed, it re-triggers.
        let second = TriggerSignal {
            conflicts: first.conflicts + policy.conflict_interval(),
            decision_level: 0,
        };
        assert!(should_trigger_incremental_bve(
            &tracker, &second, &policy, &state
        ));
    }

    #[test]
    fn test_trigger_with_tight_policy() {
        let tracker = tracker_with_cheap_vars(8, 2);
        // Tight policy: 1 conflict, 1 candidate, threshold 2 (default).
        let policy = TriggerPolicy::new(1, 1, TriggerPolicy::DEFAULT_COST_THRESHOLD);
        let state = TriggerState::default();
        let signal = TriggerSignal {
            conflicts: 1,
            decision_level: 0,
        };
        assert!(should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));
    }

    #[test]
    fn test_tracker_updates_feed_trigger() {
        // End-to-end: a clause satisfaction event pushes a variable below
        // threshold, which tips the policy into triggering.
        let mut tracker = IncrementalCostTracker::with_num_vars(16);
        for i in 0..16 {
            tracker.set_initial_cost(v(i), 3); // above threshold (2)
        }
        let policy = TriggerPolicy::new(1, 8, 2);
        let state = TriggerState::default();
        let signal = TriggerSignal {
            conflicts: 10,
            decision_level: 0,
        };
        assert!(!should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));

        // Mark 8 variables cheap via satisfied-clause hooks.
        for i in 0..8 {
            tracker.on_clause_sat(&[pos(i)]); // 3 -> 2
            tracker.on_clause_sat(&[pos(i)]); // 2 -> 1
        }
        assert!(should_trigger_incremental_bve(
            &tracker, &signal, &policy, &state
        ));
    }
}
