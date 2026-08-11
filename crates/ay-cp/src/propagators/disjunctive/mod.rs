// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Disjunctive (unary resource) scheduling propagator with edge-finding.
//!
//! Implements Vilím 2008 O(n log n) edge-finding using a Theta-Lambda tree.
//! For n tasks on a machine with capacity 1, propagates lower/upper bounds.
//!
//! Reference: Vilím 2008 "Filtering algorithms for the unary resource constraint"
//! Ported from Pumpkin (MIT): pumpkin-crates/propagators/src/propagators/disjunctive/

pub(crate) mod theta_lambda_tree;

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;
use ay_sat::Literal;
use theta_lambda_tree::ThetaLambdaTree;

/// Disjunctive constraint: n tasks on a unary resource (no overlap).
/// Task i occupies [start_i, start_i + duration_i).
#[derive(Debug)]
pub struct Disjunctive {
    /// Start time variables for each task.
    starts: Vec<IntVarId>,
    /// Constant processing times for each task.
    durations: Vec<i64>,
    /// All variables (same as starts, for the Propagator trait).
    all_vars: Vec<IntVarId>,
    /// Theta-Lambda tree workspace.
    tree: ThetaLambdaTree,
    /// Workspace: (task_idx, lct) sorted by decreasing LCT.
    ws_by_lct: Vec<(usize, i128)>,
    /// Workspace: (task_idx, est) sorted by increasing EST.
    ws_by_est: Vec<(usize, i128)>,
}

impl Disjunctive {
    pub fn new(starts: Vec<IntVarId>, durations: Vec<i64>) -> Self {
        let n = starts.len();
        debug_assert_eq!(n, durations.len());
        let all_vars = starts.clone();
        Self {
            starts,
            durations,
            all_vars,
            tree: ThetaLambdaTree::new(n),
            ws_by_lct: Vec::with_capacity(n),
            ws_by_est: Vec::with_capacity(n),
        }
    }

    /// Edge-finding for lower bounds.
    ///
    /// For each task j (by decreasing LCT):
    /// 1. If ect(Theta) > lct(j) → conflict
    /// 2. Move j from Theta to Lambda
    /// 3. While ect_bar > lct(j): the responsible Lambda task i
    ///    must start after all Theta tasks → lb(i) >= ect(Theta)
    fn edge_finding_lower(
        &mut self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> PropagationResult {
        let n = self.starts.len();

        // Sort tasks by EST to build tree ordering
        self.ws_by_est.clear();
        for i in 0..n {
            let est = i128::from(trail.lb(self.starts[i]));
            self.ws_by_est.push((i, est));
        }
        self.ws_by_est.sort_unstable_by_key(|&(_, est)| est);

        let sorted_indices: Vec<usize> = self.ws_by_est.iter().map(|&(i, _)| i).collect();
        self.tree.reset(&sorted_indices);

        // Add all tasks to Theta
        for &(i, est) in &self.ws_by_est {
            let duration = i128::from(self.durations[i]);
            let ect = est + duration;
            self.tree.add_to_theta(i, ect, duration);
        }

        // Sort tasks by decreasing LCT
        self.ws_by_lct.clear();
        for i in 0..n {
            let lct = i128::from(trail.ub(self.starts[i])) + i128::from(self.durations[i]);
            self.ws_by_lct.push((i, lct));
        }
        self.ws_by_lct
            .sort_unstable_by_key(|b| std::cmp::Reverse(b.1));

        let mut clauses: Vec<Vec<Literal>> = Vec::new();

        for idx in 0..n {
            let (j, lct_j) = self.ws_by_lct[idx];

            // Check for overload: ect(Theta) > lct(j)
            if self.tree.ect() > lct_j {
                // Conflict: tasks in Theta cannot fit before lct(j)
                return self.build_overload_conflict(trail, encoder);
            }

            // Move j from Theta to Lambda
            let est_j = i128::from(trail.lb(self.starts[j]));
            let duration_j = i128::from(self.durations[j]);
            let ect_j = est_j + duration_j;
            self.tree.remove_from_theta(j);
            self.tree.add_to_lambda(j, ect_j, duration_j);

            // Edge-finding: while some Lambda task must come after all Theta tasks
            while self.tree.ect_bar() > lct_j {
                if let Some(i) = self.tree.responsible_ect_bar() {
                    let new_lb = self.tree.ect();
                    let current_lb = i128::from(trail.lb(self.starts[i]));

                    if new_lb > current_lb {
                        // Propagate: lb(s_i) >= ect(Theta)
                        let Ok(new_lb) = i64::try_from(new_lb) else {
                            return self.build_overload_conflict(trail, encoder);
                        };
                        if let Some(clause) = self.build_lb_clause(trail, encoder, i, new_lb) {
                            clauses.push(clause);
                        }
                    }

                    // Remove i from Lambda to continue
                    self.tree.remove_from_lambda(i);
                } else {
                    break;
                }
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// Edge-finding for upper bounds (mirror of lower bounds).
    ///
    /// Negate times: est' = -lct, lct' = -est, ect' = -lst.
    /// Run the same algorithm, convert back: new_ub = -(new_lb') - duration.
    fn edge_finding_upper(
        &mut self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> PropagationResult {
        let n = self.starts.len();

        // Mirror: est' = -(ub + dur), lct' = -lb
        // ect' = est' + dur = -(ub + dur) + dur = -ub
        self.ws_by_est.clear();
        for i in 0..n {
            let ub = i128::from(trail.ub(self.starts[i]));
            let est_mirror = -(ub + i128::from(self.durations[i]));
            self.ws_by_est.push((i, est_mirror));
        }
        self.ws_by_est.sort_unstable_by_key(|&(_, est)| est);

        let sorted_indices: Vec<usize> = self.ws_by_est.iter().map(|&(i, _)| i).collect();
        self.tree.reset(&sorted_indices);

        // Add all tasks to Theta in mirrored coordinates
        for &(i, est_mirror) in &self.ws_by_est {
            let duration = i128::from(self.durations[i]);
            let ect_mirror = est_mirror + duration; // = -ub
            self.tree.add_to_theta(i, ect_mirror, duration);
        }

        // Sort by decreasing mirrored LCT (lct' = -lb, so decreasing lct' = increasing lb)
        self.ws_by_lct.clear();
        for i in 0..n {
            let lb = i128::from(trail.lb(self.starts[i]));
            let lct_mirror = -lb;
            self.ws_by_lct.push((i, lct_mirror));
        }
        self.ws_by_lct
            .sort_unstable_by_key(|b| std::cmp::Reverse(b.1));

        let mut clauses: Vec<Vec<Literal>> = Vec::new();

        for idx in 0..n {
            let (j, lct_j_mirror) = self.ws_by_lct[idx];

            if self.tree.ect() > lct_j_mirror {
                return self.build_overload_conflict_upper(trail, encoder);
            }

            let ub_j = i128::from(trail.ub(self.starts[j]));
            let duration_j = i128::from(self.durations[j]);
            let ect_j_mirror = -(ub_j + duration_j) + duration_j; // = -ub_j
            self.tree.remove_from_theta(j);
            self.tree.add_to_lambda(j, ect_j_mirror, duration_j);

            while self.tree.ect_bar() > lct_j_mirror {
                if let Some(i) = self.tree.responsible_ect_bar() {
                    // In mirrored coords: new_lb_mirror = ect(Theta)
                    // Convert back: new_ub_original = -(new_lb_mirror) - duration_i
                    let new_lb_mirror = self.tree.ect();
                    let new_ub = -new_lb_mirror - i128::from(self.durations[i]);
                    let current_ub = i128::from(trail.ub(self.starts[i]));

                    if new_ub < current_ub {
                        let Ok(new_ub) = i64::try_from(new_ub) else {
                            return self.build_overload_conflict_upper(trail, encoder);
                        };
                        if let Some(clause) = self.build_ub_clause(trail, encoder, i, new_ub) {
                            clauses.push(clause);
                        }
                    }

                    self.tree.remove_from_lambda(i);
                } else {
                    break;
                }
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// Build conflict clause for overload detection (lower-bound direction).
    /// All tasks' lower bounds contribute to the conflict.
    fn build_overload_conflict(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> PropagationResult {
        let mut clause = Vec::new();

        // Every task's current bounds contribute to the overload.
        // Conflict: conjunction of all bounds is contradictory.
        // Clause: ¬reason1 ∨ ¬reason2 ∨ ...
        for i in 0..self.starts.len() {
            let lb = trail.lb(self.starts[i]);
            let ub = trail.ub(self.starts[i]);

            if let Some(ge_lit) = encoder.lookup_ge(self.starts[i], lb) {
                clause.push(ge_lit.negated());
            }
            if let Some(le_lit) = encoder.lookup_le(self.starts[i], ub) {
                clause.push(le_lit.negated());
            }
        }

        PropagationResult::Conflict(clause)
    }

    /// Build conflict clause for upper-bound overload.
    fn build_overload_conflict_upper(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> PropagationResult {
        // Same structure: all bounds contribute.
        self.build_overload_conflict(trail, encoder)
    }

    /// Build propagation clause for lower-bound inference.
    ///
    /// Clause: conclusion ∨ ¬reason1 ∨ ¬reason2 ∨ ...
    /// where conclusion = [s_target >= new_lb]
    /// and reasons = lower bounds of all other tasks + target's upper bound.
    fn build_lb_clause(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        target_task: usize,
        new_lb: i64,
    ) -> Option<Vec<Literal>> {
        // Propagated literal: [s_target >= new_lb]
        let conclusion = encoder.lookup_ge(self.starts[target_task], new_lb)?;

        let mut clause = Vec::with_capacity(self.starts.len() + 1);
        clause.push(conclusion);

        // Reason: all other tasks' lower bounds force target to start later
        for i in 0..self.starts.len() {
            if i == target_task {
                continue;
            }
            let lb = trail.lb(self.starts[i]);
            {
                let ge_lit = encoder.lookup_ge(self.starts[i], lb)?;
                clause.push(ge_lit.negated());
            }
        }

        // Target upper bound also contributes
        let target_ub = trail.ub(self.starts[target_task]);
        {
            let le_lit = encoder.lookup_le(self.starts[target_task], target_ub)?;
            clause.push(le_lit.negated());
        }

        Some(clause)
    }

    /// Build propagation clause for upper-bound inference.
    ///
    /// Clause: conclusion ∨ ¬reason1 ∨ ¬reason2 ∨ ...
    /// where conclusion = [s_target <= new_ub] = ¬[s_target >= new_ub + 1]
    /// and reasons = upper bounds of all other tasks + target's lower bound.
    fn build_ub_clause(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        target_task: usize,
        new_ub: i64,
    ) -> Option<Vec<Literal>> {
        // Propagated literal: [s_target <= new_ub] = ¬[s_target >= new_ub + 1]
        let conclusion = encoder.lookup_le(self.starts[target_task], new_ub)?;

        let mut clause = Vec::with_capacity(self.starts.len() + 1);
        clause.push(conclusion);

        // Reason: all other tasks' upper bounds
        for i in 0..self.starts.len() {
            if i == target_task {
                continue;
            }
            let ub = trail.ub(self.starts[i]);
            {
                let le_lit = encoder.lookup_le(self.starts[i], ub)?;
                clause.push(le_lit.negated());
            }
        }

        // Target lower bound also contributes
        let target_lb = trail.lb(self.starts[target_task]);
        {
            let ge_lit = encoder.lookup_ge(self.starts[target_task], target_lb)?;
            clause.push(ge_lit.negated());
        }

        Some(clause)
    }
}

impl Propagator for Disjunctive {
    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Global
    }

    fn variables(&self) -> &[IntVarId] {
        &self.all_vars
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        // Lower-bound edge-finding
        let lower = self.edge_finding_lower(trail, encoder);
        if matches!(lower, PropagationResult::Conflict(_)) {
            return lower;
        }

        // Upper-bound edge-finding
        let upper = self.edge_finding_upper(trail, encoder);
        if matches!(upper, PropagationResult::Conflict(_)) {
            return upper;
        }

        // Merge results
        match (lower, upper) {
            (PropagationResult::NoChange, PropagationResult::NoChange) => {
                PropagationResult::NoChange
            }
            (PropagationResult::Propagated(c), PropagationResult::NoChange)
            | (PropagationResult::NoChange, PropagationResult::Propagated(c)) => {
                PropagationResult::Propagated(c)
            }
            (PropagationResult::Propagated(mut a), PropagationResult::Propagated(b)) => {
                a.extend(b);
                PropagationResult::Propagated(a)
            }
            _ => unreachable!(),
        }
    }

    fn name(&self) -> &'static str {
        "disjunctive"
    }
}
