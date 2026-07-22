// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cumulative scheduling constraint propagator.
//!
//! Implements the time-tabling (compulsory part) algorithm for the cumulative
//! constraint: at every time point, the sum of demands of tasks that must be
//! executing does not exceed capacity.
//!
//! # Constraint
//!
//! Given n tasks, each with:
//! - `start[i]`: integer variable (start time)
//! - `duration[i]`: integer variable (processing time)
//! - `demand[i]`: integer variable (resource usage)
//! - `capacity`: constant (resource limit)
//!
//! The constraint requires: for all time points t,
//!   sum { demand\[i\] | start\[i\] <= t < start\[i\] + duration\[i\] } <= capacity
//!
//! Durations and demands may be constant (singleton-domain variables) or
//! truly variable. The propagator reads current bounds from the trail and
//! uses `lb(duration)` and `lb(demand)` for sound under-approximation of
//! compulsory parts.
//!
//! # Algorithm: Time-Tabling
//!
//! The **compulsory part** of task i is the interval `[lst(i), ect(i))` where:
//! - `lst(i) = ub(start[i])` — latest start time
//! - `ect(i) = lb(start[i]) + lb(duration[i])` — earliest completion time
//!
//! If `lst(i) < ect(i)`, the task MUST be executing during `[lst(i), ect(i))`
//! regardless of scheduling decisions. This generates a minimum resource profile.
//!
//! **Propagation:**
//! 1. Build resource profile from compulsory parts (event-point sweep)
//! 2. If profile exceeds capacity at any point → conflict
//! 3. For each task j, if scheduling j at time t would push the profile over
//!    capacity, prune t from start\[j\]'s domain (tighten bounds)
//!
//! # References
//!
//! - Letort, Beldiceanu, Carlsson. "A Scalable Sweep Algorithm for the
//!   Cumulative Constraint." CP 2012.
//! - Pumpkin `pumpkin-crates/propagators/src/propagators/cumulative/`
//! - OR-Tools CP-SAT `CumulativeConstraint`
//! - Chuffed `chuffed/globals/cumulative.cpp`

use rustc_hash::FxHashSet;

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

mod propagation;

/// Cumulative constraint propagator using time-tabling.
///
/// Tasks must not exceed resource capacity at any time point.
/// Uses compulsory parts to detect conflicts and prune bounds.
///
/// Durations and demands are `IntVarId` variables. For the common case of
/// constant durations/demands, these are singleton-domain variables whose
/// bounds never change, incurring negligible overhead.
#[derive(Debug)]
pub struct Cumulative {
    /// Start-time variables for each task
    starts: Vec<IntVarId>,
    /// Duration variables for each task (may be constant via singleton domain)
    durations: Vec<IntVarId>,
    /// Demand variables for each task (may be constant via singleton domain)
    demands: Vec<IntVarId>,
    /// Resource capacity
    capacity: i64,
    /// All watched variables (starts + durations + demands)
    all_vars: Vec<IntVarId>,
    /// Pre-allocated workspace for profile sweep events.
    ws_events: Vec<ProfileEvent>,
    /// Pre-allocated workspace for active-task flags during overload check.
    ws_active_tasks: Vec<bool>,
    /// Pre-allocated workspace for profile step function.
    ws_profile_steps: Vec<(i64, i64)>,
}

/// An event in the resource profile sweep.
#[derive(Debug, Clone, Copy)]
struct ProfileEvent {
    /// Time point
    time: i64,
    /// Change in resource usage (+demand at start, -demand at end)
    delta: i64,
    /// Index of the task causing this event
    task: usize,
}

/// A precomputed step-function profile: sorted list of (time, cumulative_load) pairs.
/// Between consecutive entries, the load is constant.
/// Used for O(log n) point queries instead of O(n) per-task scans.
#[derive(Debug)]
pub(super) struct ProfileStepFunction {
    /// Sorted by time. `steps[i] = (time_i, load_i)` means at `time >= time_i`
    /// (until the next entry), the total compulsory load is `load_i`.
    steps: Vec<(i64, i64)>,
}

impl ProfileStepFunction {
    /// Build a step-function profile from sweep events into a workspace Vec.
    /// Reuses the workspace's capacity to avoid per-call allocation.
    fn from_events_ws(events: &[ProfileEvent], ws: &mut Vec<(i64, i64)>) -> Self {
        ws.clear();
        if !events.is_empty() {
            let mut current_load: i64 = 0;
            let mut i = 0;
            while i < events.len() {
                let t = events[i].time;
                while i < events.len() && events[i].time == t {
                    current_load += events[i].delta;
                    i += 1;
                }
                ws.push((t, current_load));
            }
        }
        // Take the Vec out; caller returns it via return_steps_ws.
        Self {
            steps: std::mem::take(ws),
        }
    }

    /// Return the steps Vec back to the workspace for reuse.
    fn return_steps_ws(self, ws: &mut Vec<(i64, i64)>) {
        *ws = self.steps;
    }

    /// Query the load at time point `t`. O(log n) via binary search.
    fn load_at(&self, t: i64) -> i64 {
        if self.steps.is_empty() {
            return 0;
        }
        // Find the last step with time <= t
        match self.steps.binary_search_by_key(&t, |&(time, _)| time) {
            Ok(idx) => self.steps[idx].1,
            Err(0) => 0, // t is before all steps
            Err(idx) => self.steps[idx - 1].1,
        }
    }

    /// Find the first time point in `[start, end)` where
    /// `load_at(t) - exclude_contribution(t) + demand > capacity`.
    /// Returns None if no such time point exists.
    ///
    /// `exclude_cp` is the compulsory part of the task to exclude:
    /// `Some((cp_start, cp_end, demand))` means subtract `demand` from the
    /// profile in the range `[cp_start, cp_end)`.
    fn find_conflict_in_range(
        &self,
        start: i64,
        end: i64,
        demand: i64,
        capacity: i64,
        exclude_cp: Option<(i64, i64, i64)>,
    ) -> Option<i64> {
        if self.steps.is_empty() {
            return None;
        }

        // We need to check all profile change points within [start, end),
        // plus the start point itself. Collect the distinct time points to check.
        // Instead of iterating every integer in [start, end), we only check
        // time points where the profile changes value.

        // First, check the start point
        let load = self.adjusted_load(start, exclude_cp);
        if load + demand > capacity {
            return Some(start);
        }

        // Then check each profile step change point in (start, end)
        let first_idx = match self.steps.binary_search_by_key(&(start + 1), |&(t, _)| t) {
            Ok(idx) => idx,
            Err(idx) => idx,
        };

        for &(t, _) in &self.steps[first_idx..] {
            if t >= end {
                break;
            }
            let load = self.adjusted_load(t, exclude_cp);
            if load + demand > capacity {
                return Some(t);
            }
        }

        // Also check the boundary of the excluded task's compulsory part,
        // since removing the exclude contribution can create a step change
        // within [start, end) that isn't in the profile steps.
        if let Some((cp_start, cp_end, _)) = exclude_cp {
            for boundary in [cp_start, cp_end] {
                if boundary > start && boundary < end {
                    let load = self.adjusted_load(boundary, exclude_cp);
                    if load + demand > capacity {
                        return Some(boundary);
                    }
                }
            }
        }

        None
    }

    /// Load at time `t` adjusted for an excluded task's compulsory part.
    fn adjusted_load(&self, t: i64, exclude_cp: Option<(i64, i64, i64)>) -> i64 {
        let base = self.load_at(t);
        if let Some((cp_start, cp_end, dem)) = exclude_cp {
            if cp_start <= t && t < cp_end {
                return base - dem;
            }
        }
        base
    }
}

impl Cumulative {
    /// Create a new Cumulative propagator.
    ///
    /// # Panics
    ///
    /// Panics if `starts`, `durations`, and `demands` have different lengths.
    pub fn new(
        starts: Vec<IntVarId>,
        durations: Vec<IntVarId>,
        demands: Vec<IntVarId>,
        capacity: i64,
    ) -> Self {
        assert_eq!(
            starts.len(),
            durations.len(),
            "starts and durations must have same length"
        );
        assert_eq!(
            starts.len(),
            demands.len(),
            "starts and demands must have same length"
        );

        // Watch all variables: starts, durations, and demands.
        // For constant (singleton) vars, bounds never change so no overhead.
        // Use a seen set for O(1) dedup instead of O(n) .contains().
        let mut all_vars = Vec::with_capacity(starts.len() * 3);
        let mut seen = FxHashSet::default();
        for &v in starts.iter().chain(durations.iter()).chain(demands.iter()) {
            if seen.insert(v) {
                all_vars.push(v);
            }
        }

        let n = starts.len();
        Self {
            starts,
            durations,
            demands,
            capacity,
            all_vars,
            ws_events: Vec::with_capacity(n * 2),
            ws_active_tasks: vec![false; n],
            ws_profile_steps: Vec::with_capacity(n * 2),
        }
    }

    /// Compute the compulsory part of task i using current trail bounds.
    ///
    /// Uses `lb(duration[i])` for sound under-approximation: the task must
    /// run for at least `lb(dur)` time units, so the compulsory part computed
    /// with `lb(dur)` is always valid.
    ///
    /// Returns `Some((lst, ect))` if the compulsory part is non-empty.
    fn compulsory_part(&self, i: usize, trail: &IntegerTrail) -> Option<(i64, i64)> {
        let dur_lb = trail.lb(self.durations[i]);
        let dem_lb = trail.lb(self.demands[i]);

        if dur_lb <= 0 || dem_lb <= 0 {
            return None;
        }

        let lst = trail.ub(self.starts[i]); // latest start time
        let ect = trail.lb(self.starts[i]) + dur_lb; // earliest completion time

        if lst < ect {
            Some((lst, ect))
        } else {
            None
        }
    }

    /// Get the lower bound of demand for task i (minimum resource usage).
    fn demand_lb(&self, i: usize, trail: &IntegerTrail) -> i64 {
        trail.lb(self.demands[i])
    }

    /// Get the lower bound of duration for task i (minimum processing time).
    fn duration_lb(&self, i: usize, trail: &IntegerTrail) -> i64 {
        trail.lb(self.durations[i])
    }

    /// Build the resource profile from compulsory parts into `self.ws_events`.
    fn build_profile_events(&mut self, trail: &IntegerTrail) {
        self.ws_events.clear();

        for i in 0..self.starts.len() {
            if let Some((lst, ect)) = self.compulsory_part(i, trail) {
                let dem = self.demand_lb(i, trail);
                self.ws_events.push(ProfileEvent {
                    time: lst,
                    delta: dem,
                    task: i,
                });
                self.ws_events.push(ProfileEvent {
                    time: ect,
                    delta: -dem,
                    task: i,
                });
            }
        }

        // Sort by time, then by delta (decrements before increments at same time
        // for correct peak computation). Actually, increments first to detect peak.
        self.ws_events
            .sort_unstable_by(|a, b| a.time.cmp(&b.time).then(a.delta.cmp(&b.delta)));
    }

    // check_overload_from_events, build_overload_explanation,
    // propagate_bounds_with_profile, find_earliest_start, find_latest_start,
    // build_pruning_reasons, build_pruning_explanation extracted to propagation.rs
}

impl Propagator for Cumulative {
    fn variables(&self) -> &[IntVarId] {
        &self.all_vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Global
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        // Build profile events into workspace, reuse for both overload check and bounds.
        self.build_profile_events(trail);
        if self.ws_events.is_empty() {
            return PropagationResult::NoChange;
        }

        // Step 1: Check for overload conflict (sweep the events)
        if let Some(conflict) = self.check_overload_from_events(trail, encoder) {
            return PropagationResult::Conflict(conflict);
        }

        // Step 2: Propagate bounds using precomputed step function.
        // Use workspace for profile steps to avoid per-call allocation.
        let profile =
            ProfileStepFunction::from_events_ws(&self.ws_events, &mut self.ws_profile_steps);
        let result = self.propagate_bounds_with_profile(trail, encoder, &profile);
        profile.return_steps_ws(&mut self.ws_profile_steps);
        result
    }

    fn name(&self) -> &'static str {
        "cumulative"
    }
}

#[cfg(test)]
mod tests;
