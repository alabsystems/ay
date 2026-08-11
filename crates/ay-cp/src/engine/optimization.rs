// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Optimization and incremental solving helpers for the CP-SAT engine.
//!
//! Methods for incremental optimization: objective registration, bound
//! tightening, solution blocking, VSIDS activity boosting, and phase guidance.

use std::collections::BTreeSet;

use crate::variable::IntVarId;

use super::CpSatEngine;

/// Errors from incremental constraints that require an existing order literal.
///
/// [`CpSatEngine::pre_compile`] and [`CpSatEngine::solve`] allocate every
/// in-domain order literal. Receiving this error therefore means an
/// incremental constraint was requested before either operation completed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum IncrementalEncodingError {
    /// An exact assignment to block contains a value outside the variable's
    /// declared domain, so it is not a solver assignment.
    #[error("cannot block value {value} for {variable:?}: value is outside domain [{lb}, {ub}]")]
    AssignmentValueOutsideDomain {
        /// Variable whose alleged assignment value is invalid.
        variable: IntVarId,
        /// Value supplied by the caller.
        value: i64,
        /// Declared lower bound.
        lb: i64,
        /// Declared upper bound.
        ub: i64,
    },

    /// An assignment slice named the same integer variable more than once.
    #[error("cannot block assignment: {variable:?} appears more than once")]
    DuplicateAssignmentVariable {
        /// Repeated variable identifier.
        variable: IntVarId,
    },

    /// A non-trivial incremental bound needs an order literal that has not
    /// been allocated yet.
    #[error(
        "{operation} requires an unallocated order literal for {variable:?} at bound {value}; call pre_compile() or solve() first"
    )]
    MissingOrderLiteral {
        /// Incremental operation requesting the literal.
        operation: &'static str,
        /// Variable constrained by the operation.
        variable: IntVarId,
        /// User-facing bound or assignment value.
        value: i64,
    },
}

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
    /// Must normally be called after [`Self::pre_compile`] or [`Self::solve`]
    /// so that order-encoding literals are allocated. Empty assignments and
    /// assignments consisting only of fixed variables need no literals and
    /// immediately add a contradiction.
    ///
    /// # Panics
    ///
    /// Panics when the assignment is invalid or a required order literal has
    /// not been allocated. Use [`Self::try_block_assignment`] to handle that
    /// misuse as a typed error.
    pub fn block_assignment(&mut self, assignment: &[(IntVarId, i64)]) {
        self.try_block_assignment(assignment)
            .expect("cannot block assignment");
    }

    /// Fallible form of [`Self::block_assignment`].
    ///
    /// The blocking clause is assembled completely before it is installed, so
    /// an error leaves the SAT solver unchanged.
    pub fn try_block_assignment(
        &mut self,
        assignment: &[(IntVarId, i64)],
    ) -> Result<(), IncrementalEncodingError> {
        // Validate the entire alleged assignment before looking up any order
        // literal. This makes duplicate/out-of-domain diagnostics independent
        // of preallocation state and keeps every failure atomic.
        let mut seen = BTreeSet::new();
        for &(var, val) in assignment {
            if !seen.insert(var) {
                return Err(IncrementalEncodingError::DuplicateAssignmentVariable {
                    variable: var,
                });
            }
            let (lb, ub) = self.encoder.var_bounds(var);
            if val < lb || val > ub {
                return Err(IncrementalEncodingError::AssignmentValueOutsideDomain {
                    variable: var,
                    value: val,
                    lb,
                    ub,
                });
            }
        }

        let mut clause = Vec::new();
        for &(var, val) in assignment {
            let (lb, ub) = self.encoder.var_bounds(var);
            // x_i != v_i ↔ (x_i < v_i) ∨ (x_i > v_i)
            // In order encoding: ¬[x_i >= v_i] ∨ [x_i >= v_i + 1]
            // Domain-impossible disjuncts are omitted. If every variable is
            // fixed to the supplied value, the resulting empty clause is the
            // required contradiction: there is no different assignment.
            if val > lb {
                let lit = self.encoder.lookup_ge(var, val).ok_or(
                    IncrementalEncodingError::MissingOrderLiteral {
                        operation: "blocking an assignment",
                        variable: var,
                        value: val,
                    },
                )?;
                clause.push(lit.negated()); // x_i < val
            }
            if val < ub {
                // `val < ub <= i64::MAX`, so the successor exists.
                let next_value = val + 1;
                let lit = self.encoder.lookup_ge(var, next_value).ok_or(
                    IncrementalEncodingError::MissingOrderLiteral {
                        operation: "blocking an assignment",
                        variable: var,
                        value: val,
                    },
                )?;
                clause.push(lit); // x_i > val
            }
        }

        // An empty clause is intentional for an empty projection or a
        // projection made entirely of fixed variables: it blocks the sole
        // projected solution and makes the next solve UNSAT.
        if clause.is_empty() {
            self.mark_permanently_inconsistent();
        } else {
            self.sat.add_clause(clause);
        }
        Ok(())
    }

    /// Add a direct SAT-level upper bound: `x <= value`.
    ///
    /// In order encoding this is `¬[x >= value + 1]`, added as a unit clause.
    /// # Panics
    ///
    /// Panics when a non-trivial bound needs an order literal that has not
    /// been allocated. Use [`Self::try_add_upper_bound`] to handle that misuse
    /// as a typed error.
    pub fn add_upper_bound(&mut self, var: IntVarId, value: i64) {
        self.try_add_upper_bound(var, value)
            .expect("cannot add upper bound");
    }

    /// Fallible form of [`Self::add_upper_bound`].
    ///
    /// Bounds at or above the declared upper bound are tautologies. Bounds
    /// below the declared lower bound add an empty clause immediately. Only a
    /// bound strictly inside the domain requires a pre-allocated literal.
    pub fn try_add_upper_bound(
        &mut self,
        var: IntVarId,
        value: i64,
    ) -> Result<(), IncrementalEncodingError> {
        let (lb, ub) = self.encoder.var_bounds(var);
        if value >= ub {
            return Ok(());
        }
        if value < lb {
            self.mark_permanently_inconsistent();
            return Ok(());
        }

        let lit = self.encoder.lookup_le(var, value).ok_or(
            IncrementalEncodingError::MissingOrderLiteral {
                operation: "adding an upper bound",
                variable: var,
                value,
            },
        )?;
        self.sat.add_clause(vec![lit]);
        Ok(())
    }

    /// Add a direct SAT-level lower bound: `x >= value`.
    ///
    /// In order encoding this is `[x >= value]`, added as a unit clause.
    /// # Panics
    ///
    /// Panics when a non-trivial bound needs an order literal that has not
    /// been allocated. Use [`Self::try_add_lower_bound`] to handle that misuse
    /// as a typed error.
    pub fn add_lower_bound(&mut self, var: IntVarId, value: i64) {
        self.try_add_lower_bound(var, value)
            .expect("cannot add lower bound");
    }

    /// Fallible form of [`Self::add_lower_bound`].
    ///
    /// Bounds at or below the declared lower bound are tautologies. Bounds
    /// above the declared upper bound add an empty clause immediately. Only a
    /// bound strictly inside the domain requires a pre-allocated literal.
    pub fn try_add_lower_bound(
        &mut self,
        var: IntVarId,
        value: i64,
    ) -> Result<(), IncrementalEncodingError> {
        let (lb, ub) = self.encoder.var_bounds(var);
        if value <= lb {
            return Ok(());
        }
        if value > ub {
            self.mark_permanently_inconsistent();
            return Ok(());
        }

        let lit = self.encoder.lookup_ge(var, value).ok_or(
            IncrementalEncodingError::MissingOrderLiteral {
                operation: "adding a lower bound",
                variable: var,
                value,
            },
        )?;
        self.sat.add_clause(vec![lit]);
        Ok(())
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
        if self.permanently_inconsistent {
            return Some(false);
        }
        let (lb, ub) = self.encoder.var_bounds(var);

        // Classify bounds against the declared domain before looking up an
        // order literal. Outside bounds can be decided exactly, while a
        // domain-tautological bound intentionally probes the base SAT model.
        let assumption = if minimize {
            if value < lb {
                return Some(false);
            }
            if value >= ub {
                None
            } else {
                // obj <= value, where lb <= value < ub.
                Some(self.encoder.lookup_le(var, value)?)
            }
        } else if value > ub {
            return Some(false);
        } else if value <= lb {
            None
        } else {
            // obj >= value, where lb < value <= ub.
            Some(self.encoder.lookup_ge(var, value)?)
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
            // Search range for minimization: optimal is in
            // [domain_lb, current_best - 1]. At i64::MIN there is no strictly
            // better representable value.
            let Some(hi) = current_best.checked_sub(1) else {
                return domain_lb;
            };
            (domain_lb, hi)
        } else {
            // Search range for maximization: optimal is in
            // [current_best + 1, domain_ub]. At i64::MAX there is no strictly
            // better representable value.
            let Some(lo) = current_best.checked_add(1) else {
                return domain_ub;
            };
            (lo, domain_ub)
        };

        let mut proven_bound = if minimize { domain_lb } else { domain_ub };
        let mut probes_done = 0;

        while lo <= hi && probes_done < max_probes {
            let mid = if minimize {
                floor_midpoint(lo, hi)
            } else {
                ceil_midpoint(lo, hi)
            };

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

/// Midpoint rounded toward the lower endpoint, without overflowing i64.
fn floor_midpoint(lo: i64, hi: i64) -> i64 {
    debug_assert!(lo <= hi);
    let midpoint = i128::from(lo) + (i128::from(hi) - i128::from(lo)) / 2;
    midpoint as i64
}

/// Midpoint rounded toward the upper endpoint, without overflowing i64.
fn ceil_midpoint(lo: i64, hi: i64) -> i64 {
    debug_assert!(lo <= hi);
    let distance = i128::from(hi) - i128::from(lo);
    let midpoint = i128::from(lo) + (distance + 1) / 2;
    midpoint as i64
}

#[cfg(test)]
mod midpoint_tests {
    use super::{ceil_midpoint, floor_midpoint};

    #[test]
    fn negative_adjacent_midpoint_makes_lower_progress() {
        assert_eq!(floor_midpoint(-2, -1), -2);
    }

    #[test]
    fn positive_adjacent_midpoint_makes_upper_progress() {
        assert_eq!(ceil_midpoint(1, 2), 2);
    }
}
