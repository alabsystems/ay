// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main IntSat solver loop.
//!
//! Implements the CDCL-style ILP solving algorithm:
//! 1. Normalize all input constraints.
//! 2. Set up initial bounds from input constraints.
//! 3. Loop: propagate, handle conflict or decide.
//!
//! The solver maintains a constraint database (input + learned), a bound trail,
//! and a VSIDS-like decision heuristic.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use num_bigint::BigInt;
use num_traits::Zero;

use crate::conflict::analyze_conflict;
use crate::decide::DecisionHeuristic;
use crate::normalize::normalize_constraint;
use crate::propagate;
use crate::trail::Trail;
use crate::types::PropagationResult;
use crate::types::{Constraint, IntSatResult, VarId};

/// Configuration for the IntSat solver.
pub struct IntSatConfig {
    /// Maximum number of conflicts before giving up.
    pub max_conflicts: usize,
    /// Maximum number of learned constraints to keep.
    pub max_learned: usize,
    /// Optional wall-clock deadline. When set, the solver returns
    /// `IntSatResult::Unknown` as soon as the deadline has passed (checked at
    /// iteration boundaries and periodically inside the conflict loop). This
    /// is what lets callers honour `--timeout` reliably for large integer
    /// problems (#8749): the conflict budget alone can take multiple seconds
    /// to exhaust on BigInt-heavy inputs, overshooting any configured timeout.
    pub deadline: Option<Instant>,
}

impl Default for IntSatConfig {
    fn default() -> Self {
        Self {
            max_conflicts: 100_000,
            max_learned: 10_000,
            deadline: None,
        }
    }
}

/// The IntSat solver state.
pub struct IntSatSolver {
    /// All constraints (input + learned). Input constraints come first.
    constraints: Vec<Constraint>,
    /// Number of input constraints (always the first N entries).
    num_input_constraints: usize,
    /// Number of variables.
    num_vars: usize,
    /// The bound trail.
    pub(crate) trail: Trail,
    /// Decision heuristic.
    heuristic: DecisionHeuristic,
    /// Configuration.
    config: IntSatConfig,
    /// Conflict counter.
    conflicts: usize,
}

impl IntSatSolver {
    /// Create a new solver with the given constraints and number of variables.
    #[must_use]
    pub fn new(mut constraints: Vec<Constraint>, num_vars: usize, config: IntSatConfig) -> Self {
        // Normalize all input constraints.
        for c in &mut constraints {
            // Sort coefficients by VarId for determinism.
            c.coeffs.sort_by_key(|(v, _)| *v);
            // Remove zero coefficients.
            c.coeffs.retain(|(_, coeff)| !coeff.is_zero());
            normalize_constraint(c);
        }

        let num_input = constraints.len();

        Self {
            constraints,
            num_input_constraints: num_input,
            num_vars,
            trail: Trail::new(),
            heuristic: DecisionHeuristic::new(num_vars),
            config,
            conflicts: 0,
        }
    }

    /// Solve the ILP problem.
    pub fn solve(&mut self) -> IntSatResult {
        let deadline = self.config.deadline;

        // Initial propagation at level 0.
        match propagate::propagate_with_deadline(
            &self.constraints,
            &mut self.trail,
            self.num_vars,
            deadline,
        ) {
            PropagationResult::Conflict { .. } => {
                return IntSatResult::Unsat;
            }
            PropagationResult::Ok => {}
        }

        // #8749: deadline may have tripped before the first decision.
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            return IntSatResult::Unknown;
        }

        let mut decisions: u64 = 0;
        loop {
            // #8749: Honour wall-clock deadline before the next decision so
            // large BigInt problems do not overshoot `--timeout` while still
            // below the conflict budget.
            if self.config.deadline.is_some_and(|dl| Instant::now() >= dl) {
                return IntSatResult::Unknown;
            }

            // Process-memory gate, amortized to one poll per 256 decisions
            // (two syscalls). The BigInt coefficient churn in this loop is
            // what grew a deadline-less in-process solve past 300 GB — with
            // no counting allocator and no TermStore involvement, the global
            // footprint gate is the only signal that sees it. Deadline-less
            // callers (embedders that never set `:timeout`) are exactly the
            // ones this protects.
            decisions = decisions.wrapping_add(1);
            if decisions.is_multiple_of(256) && ay_core::term::TermStore::global_memory_exceeded() {
                return IntSatResult::Unknown;
            }

            // Check resource limits.
            if self.conflicts >= self.config.max_conflicts {
                return IntSatResult::Unknown;
            }

            // Check if all variables are defined.
            if self.all_vars_defined() {
                return self.extract_model();
            }

            // Make a decision.
            let Some(mut decision) = self.heuristic.decide(&self.trail, self.num_vars) else {
                // No undecided variables with both bounds? Check if all defined.
                if self.all_vars_defined() {
                    return self.extract_model();
                }
                // Some variables lack bounds entirely -- cannot make progress.
                return IntSatResult::Unknown;
            };

            // Start new decision level.
            self.trail.new_decision_level();
            decision.level = self.trail.current_level();
            self.trail.push_bound(decision);

            // Propagate after decision.
            loop {
                match propagate::propagate_with_deadline(
                    &self.constraints,
                    &mut self.trail,
                    self.num_vars,
                    deadline,
                ) {
                    PropagationResult::Ok => break,
                    PropagationResult::Conflict { constraint_idx } => {
                        self.conflicts += 1;

                        // #8749: Periodic deadline check inside the tight
                        // conflict loop. Every 64 conflicts is roughly a few
                        // hundred microseconds to tens of milliseconds even
                        // on BigInt-heavy inputs, which keeps overshoot well
                        // under the 500 ms target for any `--timeout >= 100ms`.
                        if self.conflicts.is_multiple_of(64)
                            && self.config.deadline.is_some_and(|dl| Instant::now() >= dl)
                        {
                            return IntSatResult::Unknown;
                        }

                        if self.trail.current_level() == 0 {
                            return IntSatResult::Unsat;
                        }

                        // Analyze conflict.
                        let Some(analysis) =
                            analyze_conflict(constraint_idx, &self.constraints, &self.trail)
                        else {
                            return IntSatResult::Unsat;
                        };

                        // Bump activity of variables in the learned constraint.
                        self.heuristic.bump_conflict_vars(&analysis.learned);

                        // Add learned constraint.
                        if self.constraints.len() - self.num_input_constraints
                            < self.config.max_learned
                        {
                            self.constraints.push(analysis.learned);
                        }

                        // Backjump.
                        self.trail.backtrack_to_level(analysis.backjump_level);

                        // Decay activities periodically.
                        if self.conflicts.is_multiple_of(256) {
                            self.heuristic.decay_activities();
                        }

                        // Continue propagation after backjump.
                    }
                }
            }
        }
    }

    /// Check if all variables are fully defined (lower == upper bound).
    fn all_vars_defined(&self) -> bool {
        for i in 0..self.num_vars {
            if !self.trail.is_defined(VarId(i as u32)) {
                return false;
            }
        }
        true
    }

    /// Extract the model from fully defined variables.
    fn extract_model(&self) -> IntSatResult {
        let mut model = HashMap::default();
        for i in 0..self.num_vars {
            let var = VarId(i as u32);
            if let Some(val) = self.trail.value(var) {
                model.insert(var, val.clone());
            }
        }

        // Verify model against all input constraints.
        for constraint in &self.constraints[..self.num_input_constraints] {
            let mut lhs = BigInt::zero();
            for (var, coeff) in &constraint.coeffs {
                if let Some(val) = model.get(var) {
                    lhs += coeff * val;
                }
            }
            debug_assert!(
                lhs <= constraint.rhs,
                "invariant: model violates constraint: {lhs} > {}",
                constraint.rhs
            );
        }

        IntSatResult::Sat(model)
    }

    /// Get the number of conflicts encountered.
    #[must_use]
    pub fn num_conflicts(&self) -> usize {
        self.conflicts
    }

    /// Get the number of learned constraints.
    #[must_use]
    pub fn num_learned(&self) -> usize {
        self.constraints.len() - self.num_input_constraints
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{BoundEntry, BoundReason, VarId};

    fn make_constraint(coeffs: &[(u32, i64)], rhs: i64) -> Constraint {
        Constraint {
            coeffs: coeffs
                .iter()
                .map(|(v, c)| (VarId(*v), BigInt::from(*c)))
                .collect(),
            rhs: BigInt::from(rhs),
        }
    }

    #[test]
    fn test_trivial_sat() {
        // x0 in [0, 5]: x0 <= 5 and -x0 <= 0
        let constraints = vec![
            make_constraint(&[(0, 1)], 5),
            make_constraint(&[(0, -1)], 0),
        ];

        let mut solver = IntSatSolver::new(constraints, 1, IntSatConfig::default());

        // Add initial bounds.
        solver.trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(0),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        solver.trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        let result = solver.solve();
        assert!(matches!(result, IntSatResult::Sat(_)));
    }

    #[test]
    fn test_trivial_unsat() {
        // x0 >= 5 AND x0 <= 3 (infeasible)
        // As <= constraints: x0 <= 3, -x0 <= -5
        let constraints = vec![
            make_constraint(&[(0, 1)], 3),
            make_constraint(&[(0, -1)], -5),
        ];

        let mut solver = IntSatSolver::new(constraints, 1, IntSatConfig::default());

        // Add bounds that will conflict.
        solver.trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        solver.trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(3),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        let result = solver.solve();
        assert!(matches!(result, IntSatResult::Unsat));
    }

    #[test]
    fn test_two_var_sat() {
        // x + y <= 10, x >= 3, y >= 4
        // As <= constraints: x + y <= 10, -x <= -3, -y <= -4
        let constraints = vec![
            make_constraint(&[(0, 1), (1, 1)], 10),
            make_constraint(&[(0, -1)], -3),
            make_constraint(&[(1, -1)], -4),
        ];

        let mut solver = IntSatSolver::new(constraints, 2, IntSatConfig::default());

        // Bounds: x in [3, 100], y in [4, 100]
        for (var, lb, ub) in [(0, 3, 100), (1, 4, 100)] {
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(lb),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(ub),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let result = solver.solve();
        match result {
            IntSatResult::Sat(model) => {
                let x = model[&VarId(0)].clone();
                let y = model[&VarId(1)].clone();
                assert!(&x + &y <= BigInt::from(10));
                assert!(x >= BigInt::from(3));
                assert!(y >= BigInt::from(4));
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn test_two_var_unsat() {
        // x + y <= 5, x >= 3, y >= 4 (infeasible: 3 + 4 = 7 > 5)
        let constraints = vec![
            make_constraint(&[(0, 1), (1, 1)], 5),
            make_constraint(&[(0, -1)], -3),
            make_constraint(&[(1, -1)], -4),
        ];

        let mut solver = IntSatSolver::new(constraints, 2, IntSatConfig::default());

        for (var, lb, ub) in [(0, 3, 100), (1, 4, 100)] {
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(lb),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(ub),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let result = solver.solve();
        assert!(matches!(result, IntSatResult::Unsat));
    }

    #[test]
    fn test_gcd_cut_power() {
        // 4x + 6y <= 9
        // With normalization: GCD(4,6) = 2, so becomes 2x + 3y <= 4
        // x in [0, 10], y in [0, 10]
        let constraints = vec![
            make_constraint(&[(0, 4), (1, 6)], 9),
            make_constraint(&[(0, -1)], 0),
            make_constraint(&[(1, -1)], 0),
        ];

        let mut solver = IntSatSolver::new(constraints, 2, IntSatConfig::default());

        for var in 0..2 {
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(0),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            solver.trail.push_bound(BoundEntry {
                var: VarId(var),
                value: BigInt::from(10),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let result = solver.solve();
        // Feasible: e.g., x=0, y=0 or x=1, y=0 etc.
        assert!(matches!(result, IntSatResult::Sat(_)));
    }

    /// #8749: A hard wall-clock deadline must fire before the conflict
    /// budget on BigInt-heavy instances. Prior to this fix, IntSat only
    /// honoured `max_conflicts`, which could take multiple seconds of
    /// BigInt arithmetic on inputs like
    /// `ring_2exp16_5vars_cascade_unsat.smt2`, overshooting any
    /// `--timeout` set at the executor level.
    #[test]
    fn test_deadline_triggers_unknown_on_large_problem() {
        use ay_core::time::Instant;
        use std::time::Duration;

        // Build a deliberately dense instance: 32 variables with wide
        // bounds and many constraints that force branch-and-bound search.
        // The exact shape does not matter; the test only asserts that the
        // deadline short-circuits the search regardless of the conflict
        // budget.
        let n_vars = 32usize;
        let mut constraints = Vec::new();
        // Pairwise sum constraints: x_i + x_{i+1} <= 100.
        for i in 0..n_vars - 1 {
            constraints.push(make_constraint(&[(i as u32, 1), ((i + 1) as u32, 1)], 100));
        }
        // Each variable lower-bounded: -x_i <= -1 (i.e. x_i >= 1).
        for i in 0..n_vars {
            constraints.push(make_constraint(&[(i as u32, -1)], -1));
        }

        let config = IntSatConfig {
            max_conflicts: 1_000_000,
            max_learned: 100_000,
            deadline: Some(Instant::now() + Duration::from_millis(50)),
        };
        let mut solver = IntSatSolver::new(constraints, n_vars, config);

        // Wide bounds to force meaningful search.
        for i in 0..n_vars {
            solver.trail.push_bound(BoundEntry {
                var: VarId(i as u32),
                value: BigInt::from(1),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            solver.trail.push_bound(BoundEntry {
                var: VarId(i as u32),
                value: BigInt::from(1_000_000),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let start = Instant::now();
        let result = solver.solve();
        let elapsed = start.elapsed();

        // The short deadline must cut the search well before the million
        // conflict budget. Even with generous wiggle room for test hosts
        // under load, 500 ms is orders of magnitude below the pre-fix
        // behaviour observed on the bug repro.
        assert!(
            elapsed < Duration::from_millis(500),
            "deadline must short-circuit solve(); took {elapsed:?}"
        );
        // Result may be SAT (instance is trivially feasible) or Unknown
        // (deadline fired first). Either is acceptable; the load-bearing
        // invariant is wall-clock, not the verdict.
        let _ = result;
    }

    /// #8751 / #4785 investigation: the LIA test `test_multivar_dioph_bounded_sat`
    /// times out at 10s on HEAD, yet the formula is trivially SAT
    /// (`6a+10b+15c=4` with `-10<=a,b,c<=10`; e.g. `a=4, b=-2, c=0` or
    /// `a=-1, b=1, c=0`). This test replicates the IntSat constraints the
    /// LIA bridge feeds it and asserts that the probe terminates in a
    /// reasonable budget rather than spinning.
    #[test]
    fn test_multivar_dioph_bounded_sat_4785_repro() {
        use ay_core::time::Instant;
        use std::time::Duration;
        // C1: 6a + 10b + 15c <= 4
        // C2: -6a - 10b - 15c <= -4
        let constraints = vec![
            make_constraint(&[(0, 6), (1, 10), (2, 15)], 4),
            make_constraint(&[(0, -6), (1, -10), (2, -15)], -4),
        ];

        let config = IntSatConfig {
            max_conflicts: 5_000,
            max_learned: 2_000,
            // No deadline -- mirror the test-runner path (not the CLI).
            deadline: None,
        };
        let mut solver = IntSatSolver::new(constraints, 3, config);
        for i in 0..3u32 {
            solver.trail.push_bound(BoundEntry {
                var: VarId(i),
                value: BigInt::from(-10),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            solver.trail.push_bound(BoundEntry {
                var: VarId(i),
                value: BigInt::from(10),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let start = Instant::now();
        let result = solver.solve();
        let elapsed = start.elapsed();
        eprintln!(
            "#4785 repro: {result:?} in {elapsed:?} after {} conflicts",
            solver.num_conflicts()
        );
        // Must terminate within a few seconds on ANY modern machine.
        // The formula is small (3 vars, 2 constraints); spending >3s is a bug.
        assert!(
            elapsed < Duration::from_secs(3),
            "IntSat probe on #4785 formula took {elapsed:?} (> 3s budget)"
        );
    }
}
