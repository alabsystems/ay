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

#[cfg(test)]
mod tests;

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

    /// Edge-finding for lower bounds (Vilím 2008, Algorithm 3).
    ///
    /// For each task j (by decreasing LCT):
    /// 1. If ect(Theta) > lct(j) = lct(Theta) → conflict
    /// 2. Move j from Theta to Lambda
    /// 3. While ect_bar(Theta, Lambda) > lct(Theta): the responsible Lambda
    ///    task i must end after all Theta tasks → lb(i) >= ect(Theta)
    ///
    /// Throughout, Theta is exactly `ws_by_lct[idx + 1..]` once j =
    /// `ws_by_lct[idx]` has moved to Lambda (and `ws_by_lct[idx..]` before),
    /// which is what the explanations below name.
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

            // Check for overload: ect(Theta) > lct(Theta) = lct(j)
            let ect_theta = self.tree.ect();
            if ect_theta > lct_j {
                // Conflict: the Theta tasks cannot all end by ect(Theta) - 1.
                return self.overload_conflict(
                    trail,
                    encoder,
                    idx,
                    ect_theta - 1,
                    Direction::Lower,
                );
            }

            // Move j from Theta to Lambda
            let est_j = i128::from(trail.lb(self.starts[j]));
            let duration_j = i128::from(self.durations[j]);
            let ect_j = est_j + duration_j;
            self.tree.remove_from_theta(j);
            self.tree.add_to_lambda(j, ect_j, duration_j);

            // lct(Theta) is the largest LCT still in Theta; with Theta empty
            // there is nothing for a Lambda task to come after.
            let Some(&(_, lct_theta)) = self.ws_by_lct.get(idx + 1) else {
                break;
            };

            // Edge-finding: while some Lambda task must come after all Theta tasks
            while self.tree.ect_bar() > lct_theta {
                let ect_bar = self.tree.ect_bar();
                let Some(i) = self.tree.responsible_ect_bar() else {
                    break;
                };
                let new_lb = self.tree.ect();
                let current_lb = i128::from(trail.lb(self.starts[i]));

                if new_lb > current_lb {
                    // Propagate: lb(s_i) >= ect(Theta). The detection holds for
                    // any common completion bound of Theta below ect_bar.
                    let edge = Edge {
                        theta_from: idx + 1,
                        completion: ect_bar - 1,
                        target: i,
                        direction: Direction::Lower,
                    };
                    if let Some(clause) = self.edge_finding_clause(trail, encoder, edge, new_lb) {
                        clauses.push(clause);
                    }
                }

                // Remove i from Lambda to continue
                self.tree.remove_from_lambda(i);
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
    /// Mirrored, a task's est' comes from its upper bound and its lct' from
    /// its lower bound, so the explanations swap the two.
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

            let ect_theta_mirror = self.tree.ect();
            if ect_theta_mirror > lct_j_mirror {
                return self.overload_conflict(
                    trail,
                    encoder,
                    idx,
                    ect_theta_mirror - 1,
                    Direction::Upper,
                );
            }

            let ub_j = i128::from(trail.ub(self.starts[j]));
            let duration_j = i128::from(self.durations[j]);
            let ect_j_mirror = -(ub_j + duration_j) + duration_j; // = -ub_j
            self.tree.remove_from_theta(j);
            self.tree.add_to_lambda(j, ect_j_mirror, duration_j);

            let Some(&(_, lct_theta_mirror)) = self.ws_by_lct.get(idx + 1) else {
                break;
            };

            while self.tree.ect_bar() > lct_theta_mirror {
                let ect_bar_mirror = self.tree.ect_bar();
                let Some(i) = self.tree.responsible_ect_bar() else {
                    break;
                };
                // In mirrored coords: new_lb_mirror = ect(Theta)
                // Convert back: new_ub_original = -(new_lb_mirror) - duration_i
                let new_lb_mirror = self.tree.ect();
                let new_ub = -new_lb_mirror - i128::from(self.durations[i]);
                let current_ub = i128::from(trail.ub(self.starts[i]));

                if new_ub < current_ub {
                    let edge = Edge {
                        theta_from: idx + 1,
                        completion: ect_bar_mirror - 1,
                        target: i,
                        direction: Direction::Upper,
                    };
                    if let Some(clause) = self.edge_finding_clause(trail, encoder, edge, new_ub) {
                        clauses.push(clause);
                    }
                }

                self.tree.remove_from_lambda(i);
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// Push the reason for "every task `k` of Theta (`ws_by_lct[theta_from..]`)
    /// starts no earlier than its current earliest start and completes by
    /// `completion`", in the pass's own coordinates.
    ///
    /// The detection rules (overload `ect(Θ) > lct(Θ)`, edge-finding
    /// `ect(Θ ∪ {i}) > lct(Θ)`) read both the earliest start and the latest
    /// completion of every Theta task, so a reason must bound both. A reason
    /// that names only the earliest starts (as the propagator did before
    /// 2026-11-18) is a clause the SAT core learns permanently although
    /// solutions of the constraint falsify it (AY-N8).
    ///
    /// The completion side is lifted: any common completion bound below the
    /// detection's ect still detects, so the literal names that bound, not
    /// each task's current latest start, and is left out where the root
    /// domain implies it. In the lower pass, the earliest start is the lower
    /// bound and "completes by c" is `s_k <= c - d_k`; mirrored (upper pass,
    /// `t' = -t - d`), the earliest start is the upper bound and "completes
    /// by c" is `s_k >= -c`.
    ///
    /// Returns `None` when a literal is missing; the caller then drops the
    /// inference rather than weaken its reason.
    fn push_theta_reason(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        theta_from: usize,
        completion: i128,
        direction: Direction,
        clause: &mut Vec<Literal>,
    ) -> Option<()> {
        for &(k, _) in &self.ws_by_lct[theta_from..] {
            let var = self.starts[k];
            let (root_lb, root_ub) = encoder.var_bounds(var);
            match direction {
                Direction::Lower => {
                    push_lb_reason(trail, encoder, var, clause)?;
                    let latest_start = completion - i128::from(self.durations[k]);
                    if latest_start < i128::from(root_ub) {
                        let latest_start = i64::try_from(latest_start).ok()?;
                        clause.push(encoder.lookup_le(var, latest_start)?.negated());
                    }
                }
                Direction::Upper => {
                    push_ub_reason(trail, encoder, var, clause)?;
                    let earliest_start = -completion;
                    if earliest_start > i128::from(root_lb) {
                        let earliest_start = i64::try_from(earliest_start).ok()?;
                        clause.push(encoder.lookup_ge(var, earliest_start)?.negated());
                    }
                }
            }
        }
        Some(())
    }

    /// Conflict for overload detection: the tasks `ws_by_lct[theta_from..]`
    /// (every task whose lct is at most the current lct(j)) cannot all
    /// complete by `completion` = ect(Theta) - 1. Only their bounds are the
    /// reason.
    fn overload_conflict(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        theta_from: usize,
        completion: i128,
        direction: Direction,
    ) -> PropagationResult {
        let mut clause = Vec::with_capacity(2 * (self.starts.len() - theta_from));
        match self.push_theta_reason(
            trail,
            encoder,
            theta_from,
            completion,
            direction,
            &mut clause,
        ) {
            Some(()) => PropagationResult::Conflict(clause),
            None => PropagationResult::NoChange,
        }
    }

    /// Explain an edge-finding inference `s_target >= bound` (lower pass) or
    /// `s_target <= bound` (upper pass): `conclusion ∨ ¬(Theta reason) ∨
    /// ¬(target's earliest start)`, where the target's earliest start is its
    /// lower bound in the lower pass and, mirrored, its upper bound in the
    /// upper pass.
    ///
    /// A bound outside the target's root domain makes the conclusion
    /// literal false at the root, so the clause acts as a conflict. Returns
    /// `None` when a literal is missing (the inference is dropped).
    fn edge_finding_clause(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        edge: Edge,
        bound: i128,
    ) -> Option<Vec<Literal>> {
        let var = self.starts[edge.target];
        let (root_lb, root_ub) = encoder.var_bounds(var);
        let conclusion = match edge.direction {
            // [s >= bound] with bound clamped to root_ub + 1 (root-false
            // literal) is implied by s >= bound, so the clause stays valid.
            Direction::Lower => {
                let clamped = bound.min(i128::from(root_ub) + 1);
                i64::try_from(clamped)
                    .ok()
                    .and_then(|v| encoder.lookup_ge(var, v))
            }
            Direction::Upper => {
                let clamped = bound.max(i128::from(root_lb) - 1);
                i64::try_from(clamped)
                    .ok()
                    .and_then(|v| encoder.lookup_le(var, v))
            }
        };
        let conclusion = conclusion?;
        let mut clause = Vec::with_capacity(2 * (self.starts.len() - edge.theta_from) + 2);
        clause.push(conclusion);
        let explained = self
            .push_theta_reason(
                trail,
                encoder,
                edge.theta_from,
                edge.completion,
                edge.direction,
                &mut clause,
            )
            .and_then(|()| match edge.direction {
                Direction::Lower => push_lb_reason(trail, encoder, var, &mut clause),
                Direction::Upper => push_ub_reason(trail, encoder, var, &mut clause),
            });
        explained.map(|()| clause)
    }
}

/// One edge-finding inference: the Theta set `ws_by_lct[theta_from..]`, a
/// completion bound every Theta task must meet for the detection to fire
/// (pass coordinates), and the Lambda task it moves.
#[derive(Debug, Clone, Copy)]
struct Edge {
    theta_from: usize,
    completion: i128,
    target: usize,
    direction: Direction,
}

/// Which bound an edge-finding pass tightens.
#[derive(Debug, Clone, Copy)]
enum Direction {
    /// Earliest starts (lower bounds) move up.
    Lower,
    /// Latest starts (upper bounds) move down; the pass runs mirrored.
    Upper,
}

/// Push `¬[s >= lb]` for the current lower bound of `var`.
fn push_lb_reason(
    trail: &IntegerTrail,
    encoder: &IntegerEncoder,
    var: IntVarId,
    clause: &mut Vec<Literal>,
) -> Option<()> {
    clause.push(encoder.lookup_ge(var, trail.lb(var))?.negated());
    Some(())
}

/// Push `¬[s <= ub]` for the current upper bound of `var`.
fn push_ub_reason(
    trail: &IntegerTrail,
    encoder: &IntegerEncoder,
    var: IntVarId,
    clause: &mut Vec<Literal>,
) -> Option<()> {
    clause.push(encoder.lookup_le(var, trail.ub(var))?.negated());
    Some(())
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
