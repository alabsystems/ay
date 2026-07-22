// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Decision heuristics for the IntSat solver.
//!
//! Picks an unresolved variable (one whose lower bound < upper bound) and
//! sets a decision bound that splits its domain. Uses VSIDS-style activity
//! scores bumped on conflict involvement.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;

use crate::trail::Trail;
use crate::types::{BoundEntry, BoundReason, Constraint, VarId};

/// Activity-based variable selection heuristic.
pub(crate) struct DecisionHeuristic {
    /// Activity scores for each variable (bumped on conflict involvement).
    activity: HashMap<VarId, f64>,
    /// Decay factor applied to all activities periodically.
    decay: f64,
    /// Bump increment (increases over time to prioritize recent conflicts).
    bump_amount: f64,
}

impl DecisionHeuristic {
    /// Create a new decision heuristic for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        let mut activity = HashMap::default();
        for i in 0..num_vars {
            activity.insert(VarId(i as u32), 0.0);
        }
        Self {
            activity,
            decay: 0.95,
            bump_amount: 1.0,
        }
    }

    /// Bump the activity of variables appearing in a learned constraint.
    pub(crate) fn bump_conflict_vars(&mut self, constraint: &Constraint) {
        for (var, coeff) in &constraint.coeffs {
            if !coeff.is_zero() {
                *self.activity.entry(*var).or_default() += self.bump_amount;
            }
        }
        self.bump_amount /= self.decay;

        // Rescale if activities get too large.
        if self.bump_amount > 1e100 {
            let scale = 1e-100;
            for val in self.activity.values_mut() {
                *val *= scale;
            }
            self.bump_amount *= scale;
        }
    }

    /// Decay all activities (called periodically).
    pub(crate) fn decay_activities(&mut self) {
        for val in self.activity.values_mut() {
            *val *= self.decay;
        }
    }

    /// Pick the unresolved variable with highest activity and create a decision
    /// bound that splits its domain.
    ///
    /// Returns None if all variables are defined (SAT).
    pub(crate) fn decide(&self, trail: &Trail, num_vars: usize) -> Option<BoundEntry> {
        let mut best_var: Option<VarId> = None;
        let mut best_activity = -1.0_f64;

        for i in 0..num_vars {
            let var = VarId(i as u32);
            if trail.is_defined(var) {
                continue;
            }

            // Must have both bounds to split.
            let Some(lb) = trail.lower_bound(var) else {
                continue;
            };
            let Some(ub) = trail.upper_bound(var) else {
                continue;
            };

            if lb >= ub {
                continue; // Already defined or infeasible.
            }

            let act = self.activity.get(&var).copied().unwrap_or(0.0);
            if best_var.is_none() || act > best_activity {
                best_var = Some(var);
                best_activity = act;
            }
        }

        let var = best_var?;
        let lb = trail.lower_bound(var)?.clone();
        let ub = trail.upper_bound(var)?.clone();

        // Split at midpoint using FLOOR division (not truncation toward zero).
        //
        // Bug fix (#8748): `BigInt::Div` rounds toward zero, which for negative
        // sums can produce `mid == ub` when the range is small, e.g.,
        // lb=-10, ub=-9: `(-10 + -9) / 2 = -19 / 2 = -9` (trunc toward 0).
        // The resulting "decision" `x <= -9` is NOT tighter than the current
        // upper bound, so push_bound silently drops it, but new_decision_level
        // was already called, causing infinite decision level escalation with
        // zero progress (observed as `conflicts=0, level=3M+` on
        // `6a+10b+15c=4` with [-10,10] bounds).
        //
        // Using floor division guarantees `mid <= (lb+ub)/2 < ub` for `lb<ub`,
        // so the decision strictly tightens the upper bound.
        let sum = &lb + &ub;
        let mid = sum.div_floor(&BigInt::from(2));

        debug_assert!(
            mid < ub,
            "invariant: decide produced non-tightening mid={mid} with lb={lb} ub={ub}",
        );

        // Decision: set upper bound to mid (try the lower half first).
        Some(BoundEntry {
            var,
            value: mid,
            is_upper: true,
            reason: BoundReason::Decision,
            level: trail.current_level() + 1, // Will be set properly by caller.
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::BoundReason;

    #[test]
    fn test_decide_picks_undecided() {
        let heuristic = DecisionHeuristic::new(2);
        let mut trail = Trail::new();

        // x0 in [0, 10], x1 in [0, 10]
        for var_id in 0..2 {
            trail.push_bound(BoundEntry {
                var: VarId(var_id),
                value: BigInt::from(0),
                is_upper: false,
                reason: BoundReason::Input,
                level: 0,
            });
            trail.push_bound(BoundEntry {
                var: VarId(var_id),
                value: BigInt::from(10),
                is_upper: true,
                reason: BoundReason::Input,
                level: 0,
            });
        }

        let decision = heuristic.decide(&trail, 2);
        assert!(decision.is_some());
        let entry = decision.expect("should have a decision");
        assert!(entry.is_upper);
        assert_eq!(entry.value, BigInt::from(5)); // floor((0+10)/2)
    }

    #[test]
    fn test_decide_returns_none_when_all_defined() {
        let heuristic = DecisionHeuristic::new(1);
        let mut trail = Trail::new();

        // x0 defined at 5.
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        assert!(heuristic.decide(&trail, 1).is_none());
    }

    #[test]
    fn test_bump_activity() {
        let mut heuristic = DecisionHeuristic::new(3);
        let constraint = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(1)), (VarId(2), BigInt::from(-1))],
            rhs: BigInt::from(5),
        };

        heuristic.bump_conflict_vars(&constraint);
        assert!(heuristic.activity[&VarId(0)] > 0.0);
        assert!(heuristic.activity[&VarId(2)] > 0.0);
        assert_eq!(heuristic.activity[&VarId(1)], 0.0);
    }
}
