// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Optimization and incremental solving helpers for the CP-SAT engine.
//!
//! Methods for incremental optimization: objective registration, bound
//! tightening, solution blocking, VSIDS activity boosting, and phase guidance.

use crate::variable::IntVarId;

use super::CpSatEngine;

impl CpSatEngine {
    /// Set the optimization objective variable and direction.
    ///
    /// When set, the CP extension's `suggest_phase` callback persistently
    /// guides the SAT solver's phase decisions for the objective variable
    /// toward the optimal direction. This is stronger than `bias_objective_phase`
    /// (which only sets the initial phase and gets overwritten by phase-saving):
    /// `suggest_phase` takes priority over the solver's internal phase heuristic
    /// on every decision throughout the entire search.
    ///
    /// For minimization: suggests `[obj >= v]` = false (prefer small values).
    /// For maximization: suggests `[obj >= v]` = true (prefer large values).
    pub fn set_objective(&mut self, var: IntVarId, minimize: bool) {
        self.objective = Some((var, minimize));
    }

    /// Block a specific solution so the solver cannot find it again.
    ///
    /// Adds a SAT clause asserting that at least one variable must differ
    /// from the given assignment. Uses the order encoding directly:
    /// `OR_i(¬[x_i >= v_i] ∨ [x_i >= v_i + 1])`.
    ///
    /// Must be called after at least one `solve()` call (so that order-
    /// encoding literals are pre-allocated).
    pub fn block_assignment(&mut self, assignment: &[(IntVarId, i64)]) {
        let mut clause = Vec::new();
        for &(var, val) in assignment {
            // x_i != v_i ↔ (x_i < v_i) ∨ (x_i > v_i)
            // In order encoding: ¬[x_i >= v_i] ∨ [x_i >= v_i + 1]
            if let Some(lit) = self.encoder.lookup_ge(var, val) {
                clause.push(lit.negated()); // x_i < v_i
            }
            if let Some(next_value) = val.checked_add(1) {
                if let Some(lit) = self.encoder.lookup_ge(var, next_value) {
                    clause.push(lit); // x_i > v_i
                }
            }
        }
        if !clause.is_empty() {
            self.sat.add_clause(clause);
        }
    }

    /// Add a direct SAT-level upper bound: `x <= value`.
    ///
    /// In order encoding this is `¬[x >= value + 1]`, added as a unit clause.
    /// Must be called after at least one `solve()` call.
    pub fn add_upper_bound(&mut self, var: IntVarId, value: i64) {
        if let Some(next_value) = value.checked_add(1) {
            if let Some(lit) = self.encoder.lookup_ge(var, next_value) {
                self.sat.add_clause(vec![lit.negated()]);
            }
        }
    }

    /// Add a direct SAT-level lower bound: `x >= value`.
    ///
    /// In order encoding this is `[x >= value]`, added as a unit clause.
    /// Must be called after at least one `solve()` call.
    pub fn add_lower_bound(&mut self, var: IntVarId, value: i64) {
        if let Some(lit) = self.encoder.lookup_ge(var, value) {
            self.sat.add_clause(vec![lit]);
        }
    }

    /// Boost VSIDS activity of the objective variable's order-encoding literals
    /// near the current bound.
    ///
    /// After finding a solution with objective value `current_val`, this bumps
    /// the activity of SAT variables encoding `[obj >= v]` for values near the
    /// new bound. This biases CDCL search toward decisions that tighten the
    /// objective, making subsequent optimization iterations find better solutions
    /// faster.
    ///
    /// The boost window covers literals from `current_val - window` to
    /// `current_val + window` (clamped to the variable's domain). Literals
    /// closer to the current value receive stronger boosts (bumped multiple
    /// times).
    pub fn boost_objective(&mut self, var: IntVarId, current_val: i64, minimize: bool) {
        let (lb, ub) = self.encoder.var_bounds(var);
        // Dynamic boost window: scale with domain size so we cover a meaningful
        // fraction of the objective range (at least 5, up to 50, roughly 10%
        // of the domain). Larger windows help on big-domain optimization
        // problems where the fixed-5 window was negligible.
        let range = ub.saturating_sub(lb).max(1);
        let window = 5i64.max(range / 10).min(50);
        // Boost window: bump literals near the active objective frontier.
        // For minimization, the frontier is just below current_val.
        // For maximization, just above.
        let (range_lo, range_hi) = if minimize {
            (current_val.saturating_sub(window).max(lb), current_val)
        } else {
            (current_val, current_val.saturating_add(window).min(ub))
        };

        for v in range_lo..=range_hi {
            if let Some(lit) = self.encoder.lookup_ge(var, v) {
                let sat_var = lit.variable();
                // Bump multiple times for literals closer to the frontier.
                let distance = if minimize {
                    current_val - v
                } else {
                    v - current_val
                };
                let bumps = (window - distance + 1) as usize;
                for _ in 0..bumps {
                    self.sat.bump_variable_activity(sat_var);
                }
            }
        }
    }

    /// Bias the objective variable's phase-save values toward the optimal
    /// direction before the first solve.
    ///
    /// For minimization: set `[obj >= v]` phases to false (prefer small obj).
    /// For maximization: set `[obj >= v]` phases to true (prefer large obj).
    ///
    /// This gives the solver a strong initial bias toward a good first solution,
    /// which is critical for MiniZinc scoring (even suboptimal solutions earn
    /// points if they have a good objective value). Without this, the default
    /// phase (typically false) produces trivially bad initial solutions for
    /// maximization problems (e.g., peaceable_queens with obj=0).
    ///
    /// Must be called after `pre_compile()` so that order-encoding literals
    /// are pre-allocated.
    pub fn bias_objective_phase(&mut self, var: IntVarId, minimize: bool) {
        let (lb, ub) = self.encoder.var_bounds(var);
        let Some(mut v) = lb.checked_add(1) else {
            return;
        };
        while v <= ub {
            if let Some(lit) = self.encoder.lookup_ge(var, v) {
                let sat_var = lit.variable();
                // For minimization: prefer [x >= v] = false → small x.
                // For maximization: prefer [x >= v] = true → large x.
                let phase = if lit.is_positive() {
                    !minimize
                } else {
                    minimize
                };
                self.sat.set_var_phase(sat_var, phase);
            }
            let Some(next_v) = v.checked_add(1) else {
                break;
            };
            v = next_v;
        }
    }

    /// Set SAT variable phases to match the current best solution.
    ///
    /// After finding a solution, this sets the phase-save value of each
    /// order-encoding literal to match the solution's assignment. On restarts,
    /// the SAT solver will first try the solution's values, then branch away
    /// to explore improvements — focusing search near known-good regions.
    pub fn set_solution_phases(&mut self, assignment: &[(IntVarId, i64)]) {
        for &(var, val) in assignment {
            let (lb, ub) = self.encoder.var_bounds(var);
            // For [x >= v]: true if val >= v, false if val < v
            let Some(mut v) = lb.checked_add(1) else {
                continue;
            };
            while v <= ub {
                if let Some(lit) = self.encoder.lookup_ge(var, v) {
                    let sat_var = lit.variable();
                    let phase = if lit.is_positive() { val >= v } else { val < v };
                    self.sat.set_var_phase(sat_var, phase);
                }
                let Some(next_v) = v.checked_add(1) else {
                    break;
                };
                v = next_v;
            }
        }
    }

    /// Probe whether an objective bound is feasible using SAT-only solving
    /// with assumptions.
    ///
    /// Uses a SAT-level assumption to temporarily constrain the objective,
    /// solve without the CP extension, and get a quick feasibility check.
    /// Assumptions are automatically retracted after the solve — no push/pop
    /// needed.
    ///
    /// This is a **sound approximation** for infeasibility:
    /// - If the probe returns UNSAT, the bound is definitely infeasible
    ///   (removing CP propagators can only weaken constraints, so SAT-UNSAT
    ///   implies CP-SAT-UNSAT).
    /// - If the probe returns SAT, the bound *might* be feasible (the CP
    ///   extension could find additional conflicts).
    ///
    /// Used by binary search optimization to quickly narrow the objective range
    /// before committing to expensive full CP-SAT iterations.
    ///
    /// `probe_timeout` limits each probe call. Returns `None` on timeout/unknown
    /// or if the bound literal doesn't exist, `Some(true)` if the SAT solver
    /// found a model, `Some(false)` if UNSAT.
    pub fn probe_bound_feasible(
        &mut self,
        var: IntVarId,
        value: i64,
        minimize: bool,
        probe_timeout: Option<std::time::Duration>,
    ) -> Option<bool> {
        // Get the assumption literal for the bound.
        let assumption = if minimize {
            // obj <= value  →  assume ¬[obj >= value + 1]
            value
                .checked_add(1)
                .and_then(|next_value| self.encoder.lookup_ge(var, next_value))
                .map(ay_sat::Literal::negated)
        } else {
            // obj >= value  →  assume [obj >= value]
            self.encoder.lookup_ge(var, value)
        };

        // Set a short timeout for probing.
        if let Some(duration) = probe_timeout {
            self.clear_interrupt();
            self.set_timeout(duration);
        }

        // SAT-only solve with assumption (no CP extension). This leverages
        // all existing learned clauses and eagerly-encoded constraints, but
        // skips lazy propagators. The assumption is temporary and automatically
        // retracted after the solve.
        let result = if let Some(assumption) = assumption {
            self.sat.solve_with_assumptions(&[assumption])
        } else {
            self.sat.solve_with_assumptions(&[])
        };

        // Clear interrupt to prevent stale timeout from affecting later solves.
        self.clear_interrupt();

        match result.into_inner() {
            ay_sat::AssumeResult::Sat(_) => Some(true),
            ay_sat::AssumeResult::Unsat(..) => Some(false),
            ay_sat::AssumeResult::Unknown | _ => None,
        }
    }

    /// Binary-search the objective range using SAT-level probing to establish
    /// a proven lower bound on the optimal value.
    ///
    /// After finding a solution with value `current_best`, this probes
    /// midpoints of the objective range using `probe_bound_feasible`. UNSAT
    /// results are trustworthy (the bound is definitely too tight), while SAT
    /// results are used heuristically (the bound might be feasible).
    ///
    /// Returns a proven lower bound `lo` such that the optimal value is
    /// guaranteed to be >= `lo`. The caller can then add `obj >= lo` as a
    /// permanent constraint to narrow the search space for linear iterations.
    ///
    /// `max_probes` limits the number of binary search steps. Each probe uses
    /// `probe_timeout` as its time limit.
    pub fn binary_probe_lower_bound(
        &mut self,
        var: IntVarId,
        current_best: i64,
        minimize: bool,
        max_probes: usize,
        probe_timeout: std::time::Duration,
    ) -> i64 {
        let (domain_lb, domain_ub) = self.encoder.var_bounds(var);

        let (mut lo, mut hi) = if minimize {
            // Search range for minimization: optimal is in [domain_lb, current_best - 1]
            (domain_lb, current_best - 1)
        } else {
            // Search range for maximization: optimal is in [current_best + 1, domain_ub]
            (current_best + 1, domain_ub)
        };

        let mut proven_bound = if minimize { domain_lb } else { domain_ub };
        let mut probes_done = 0;

        while lo <= hi && probes_done < max_probes {
            let mid = lo + (hi - lo) / 2;

            let result = self.probe_bound_feasible(var, mid, minimize, Some(probe_timeout));
            probes_done += 1;

            match result {
                Some(false) => {
                    // UNSAT: bound is too tight (trustworthy).
                    if minimize {
                        // obj <= mid is UNSAT → optimal > mid
                        proven_bound = mid + 1;
                        lo = mid + 1;
                    } else {
                        // obj >= mid is UNSAT → optimal < mid
                        proven_bound = mid - 1;
                        hi = mid - 1;
                    }
                }
                Some(true) => {
                    // SAT (may be false positive): bound might be feasible.
                    if minimize {
                        hi = mid;
                    } else {
                        lo = mid;
                    }
                    // Avoid infinite loop when lo == hi == mid
                    if lo == hi {
                        break;
                    }
                }
                None => {
                    // Unknown/timeout: can't conclude anything, stop probing.
                    break;
                }
            }
        }

        proven_bound
    }
}
