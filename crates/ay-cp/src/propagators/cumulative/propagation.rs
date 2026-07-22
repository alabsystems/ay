// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Overload checking, bound propagation, and explanation building for
//! the cumulative constraint.
//!
//! Extracted from `mod.rs` to keep each file under 500 lines.
//! Contains the propagation core: profile-based overload detection,
//! forward/backward bound tightening, and SAT-literal explanation
//! construction.

use ay_sat::Literal;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult};
use crate::trail::IntegerTrail;

use super::{Cumulative, ProfileStepFunction};

impl Cumulative {
    /// Check for overload using pre-built events. Avoids rebuilding events
    /// since `propagate()` already builds them once.
    pub(super) fn check_overload_from_events(
        &mut self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<Literal>> {
        // Sweep the profile to find the peak
        let mut current_load: i64 = 0;

        // Reuse pre-allocated active-task flags
        self.ws_active_tasks.fill(false);

        let mut i = 0;
        while i < self.ws_events.len() {
            let t = self.ws_events[i].time;

            // Process all events at time t
            while i < self.ws_events.len() && self.ws_events[i].time == t {
                let ev = &self.ws_events[i];
                current_load += ev.delta;
                self.ws_active_tasks[ev.task] = ev.delta > 0;
                i += 1;
            }

            // Check if current load exceeds capacity
            if current_load > self.capacity {
                return self.build_overload_explanation(trail, encoder, &self.ws_active_tasks);
            }
        }

        None
    }

    /// Build a conflict explanation from the tasks whose compulsory parts
    /// contribute to overload.
    ///
    /// The explanation includes bound literals for start, duration, and demand
    /// variables that create the compulsory parts of the overloading tasks.
    ///
    /// Returns `None` if any required literal lookup fails (#5986).
    fn build_overload_explanation(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        active_tasks: &[bool],
    ) -> Option<Vec<Literal>> {
        let mut reasons = Vec::new();

        for (i, &active) in active_tasks.iter().enumerate() {
            if !active {
                continue;
            }

            let est = trail.lb(self.starts[i]); // earliest start time
            let lst = trail.ub(self.starts[i]); // latest start time

            // Reason: start[i] >= est (creates the ect = est + dur)
            reasons.push(encoder.lookup_ge(self.starts[i], est)?);
            // Reason: start[i] <= lst (creates the lst)
            reasons.push(encoder.lookup_le(self.starts[i], lst)?);

            // Reason: duration[i] >= lb(dur) (used in ect computation)
            let dur_lb = self.duration_lb(i, trail);
            reasons.push(encoder.lookup_ge(self.durations[i], dur_lb)?);

            // Reason: demand[i] >= lb(dem) (used in load computation)
            let dem_lb = self.demand_lb(i, trail);
            reasons.push(encoder.lookup_ge(self.demands[i], dem_lb)?);
        }

        let explanation = Explanation::new(reasons);
        Some(explanation.into_conflict_clause())
    }

    /// Propagate: tighten start-time bounds based on the resource profile.
    ///
    /// For each task j, find the earliest feasible start time by checking the
    /// precomputed profile. If placing j at time t would push the profile over
    /// capacity, prune t from start[j]'s domain (tighten bounds).
    ///
    /// Uses a precomputed sweep profile (O(n log n) to build) for O(log n)
    /// per-point queries instead of O(n) per-point scans.
    pub(super) fn propagate_bounds_with_profile(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        profile: &ProfileStepFunction,
    ) -> PropagationResult {
        let mut clauses = Vec::new();

        for j in 0..self.starts.len() {
            let dur_j = self.duration_lb(j, trail);
            let dem_j = self.demand_lb(j, trail);
            if dur_j <= 0 || dem_j <= 0 {
                continue;
            }

            let est_j = trail.lb(self.starts[j]);
            let lst_j = trail.ub(self.starts[j]);

            // Compute task j's own compulsory part for exclusion from profile
            let exclude_cp = self
                .compulsory_part(j, trail)
                .map(|(lst, ect)| (lst, ect, dem_j));

            // Forward propagation: find earliest feasible start time
            let new_est = Self::find_earliest_start(
                profile,
                est_j,
                lst_j,
                dur_j,
                dem_j,
                self.capacity,
                exclude_cp,
            );
            if new_est > est_j {
                if new_est > lst_j {
                    if let Some(conflict) =
                        self.build_pruning_explanation(trail, encoder, j, est_j, new_est - 1, true)
                    {
                        return PropagationResult::Conflict(conflict);
                    }
                    return PropagationResult::NoChange;
                }
                if let Some(conclusion) = encoder.lookup_ge(self.starts[j], new_est) {
                    if let Some(reasons) =
                        self.build_pruning_reasons(trail, encoder, j, est_j, new_est - 1, true)
                    {
                        let explanation = Explanation::new(reasons);
                        clauses.push(explanation.into_clause(conclusion));
                    }
                }
            }

            // Backward propagation: find latest feasible start time
            let new_lst = Self::find_latest_start(
                profile,
                est_j,
                lst_j,
                dur_j,
                dem_j,
                self.capacity,
                exclude_cp,
            );
            if new_lst < lst_j {
                if new_lst < est_j {
                    if let Some(conflict) =
                        self.build_pruning_explanation(trail, encoder, j, new_lst + 1, lst_j, false)
                    {
                        return PropagationResult::Conflict(conflict);
                    }
                    return PropagationResult::NoChange;
                }
                if let Some(conclusion) = encoder.lookup_le(self.starts[j], new_lst) {
                    if let Some(reasons) =
                        self.build_pruning_reasons(trail, encoder, j, new_lst + 1, lst_j, false)
                    {
                        let explanation = Explanation::new(reasons);
                        clauses.push(explanation.into_clause(conclusion));
                    }
                }
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// Find the earliest feasible start time for task j using the precomputed
    /// profile step function. Checks only profile change points (O(k log n)
    /// where k = number of steps) instead of every integer time point (O(n·d)).
    fn find_earliest_start(
        profile: &ProfileStepFunction,
        est_j: i64,
        lst_j: i64,
        dur_j: i64,
        dem_j: i64,
        capacity: i64,
        exclude_cp: Option<(i64, i64, i64)>,
    ) -> i64 {
        let mut candidate = est_j;

        while candidate <= lst_j {
            let range_end = candidate + dur_j;
            match profile.find_conflict_in_range(candidate, range_end, dem_j, capacity, exclude_cp)
            {
                Some(t) => candidate = t + 1,
                None => break,
            }
        }

        candidate
    }

    /// Find the latest feasible start time for task j using the precomputed
    /// profile step function.
    fn find_latest_start(
        profile: &ProfileStepFunction,
        est_j: i64,
        lst_j: i64,
        dur_j: i64,
        dem_j: i64,
        capacity: i64,
        exclude_cp: Option<(i64, i64, i64)>,
    ) -> i64 {
        let mut candidate = lst_j;

        while candidate >= est_j {
            let range_end = candidate + dur_j;
            match profile.find_conflict_in_range(candidate, range_end, dem_j, capacity, exclude_cp)
            {
                Some(t) => candidate = t - dur_j,
                None => break,
            }
        }

        candidate
    }

    /// Build explanation reasons for pruning start[j]'s bounds.
    /// The reasons are the bound literals of tasks whose compulsory parts
    /// overlap with the time range [from_t, to_t].
    ///
    /// Includes start, duration, and demand bound literals.
    ///
    /// Returns `None` if any required literal lookup fails (#5986).
    fn build_pruning_reasons(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        j: usize,
        from_t: i64,
        to_t: i64,
        is_lower_bound: bool,
    ) -> Option<Vec<Literal>> {
        let mut reasons = Vec::new();

        for i in 0..self.starts.len() {
            if i == j {
                continue;
            }
            let dur_lb = self.duration_lb(i, trail);
            let dem_lb = self.demand_lb(i, trail);
            if dur_lb <= 0 || dem_lb <= 0 {
                continue;
            }

            if let Some((lst, ect)) = self.compulsory_part(i, trail) {
                // Does this compulsory part overlap [from_t, to_t]?
                if lst <= to_t && from_t < ect {
                    let est_i = trail.lb(self.starts[i]);
                    let lst_i = trail.ub(self.starts[i]);

                    reasons.push(encoder.lookup_ge(self.starts[i], est_i)?);
                    reasons.push(encoder.lookup_le(self.starts[i], lst_i)?);
                    reasons.push(encoder.lookup_ge(self.durations[i], dur_lb)?);
                    reasons.push(encoder.lookup_ge(self.demands[i], dem_lb)?);
                }
            }
        }

        // Also include the current bounds of task j as reasons
        if is_lower_bound {
            let est_j = trail.lb(self.starts[j]);
            reasons.push(encoder.lookup_ge(self.starts[j], est_j)?);
        } else {
            let lst_j = trail.ub(self.starts[j]);
            reasons.push(encoder.lookup_le(self.starts[j], lst_j)?);
        }

        // Include task j's duration and demand bounds
        let dur_j = self.duration_lb(j, trail);
        let dem_j = self.demand_lb(j, trail);
        let dur_lit = encoder.lookup_ge(self.durations[j], dur_j)?;
        if !reasons.contains(&dur_lit) {
            reasons.push(dur_lit);
        }
        let dem_lit = encoder.lookup_ge(self.demands[j], dem_j)?;
        if !reasons.contains(&dem_lit) {
            reasons.push(dem_lit);
        }

        Some(reasons)
    }

    /// Build a conflict clause for pruning that results in domain wipeout.
    ///
    /// Returns `None` if any required literal lookup fails (#5986).
    fn build_pruning_explanation(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        j: usize,
        from_t: i64,
        to_t: i64,
        is_lower_bound: bool,
    ) -> Option<Vec<Literal>> {
        let mut all_reasons =
            self.build_pruning_reasons(trail, encoder, j, from_t, to_t, is_lower_bound)?;
        // For a wipeout, include both bounds of task j
        let est_j = trail.lb(self.starts[j]);
        let lst_j = trail.ub(self.starts[j]);
        let est_lit = encoder.lookup_ge(self.starts[j], est_j)?;
        if !all_reasons.contains(&est_lit) {
            all_reasons.push(est_lit);
        }
        let lst_lit = encoder.lookup_le(self.starts[j], lst_j)?;
        if !all_reasons.contains(&lst_lit) {
            all_reasons.push(lst_lit);
        }
        let explanation = Explanation::new(all_reasons);
        Some(explanation.into_conflict_clause())
    }
}
