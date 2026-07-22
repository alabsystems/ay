// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound propagation with integer rounding for IntSat.
//!
//! For each constraint `a1*x1 + ... + an*xn <= b`, propagation derives new
//! bounds on each variable `xj`:
//!
//! - Compute `slack_j = b - sum_{i!=j} min(ai*xi)` where `min` uses the
//!   current best bound (lower for positive coeff, upper for negative).
//! - If `aj > 0`: derive upper bound `xj <= floor(slack_j / aj)`
//! - If `aj < 0`: derive lower bound `xj >= ceil(slack_j / aj)`
//!   (dividing by negative flips the inequality direction)
//!
//! Integer rounding (floor/ceil) is built into propagation, following the
//! IntSat paper's design. This is the key difference from real-valued simplex.

use ay_core::time::Instant;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use crate::normalize::floor_div;
use crate::trail::Trail;
use crate::types::{BoundEntry, BoundReason, Constraint, PropagationResult};

/// Run one round of bound propagation across all constraints.
///
/// Returns `Ok` if no conflict was detected, `Conflict` with the index of the
/// falsified constraint, or `Ok` early if `deadline` is reached. #8749: the
/// fixed-point loop below can process many constraints per invocation on
/// BigInt-heavy inputs, so we check the deadline every few outer rounds to
/// ensure wall-clock timeouts are honoured without waiting for the full
/// fixpoint.
#[cfg(test)]
pub(crate) fn propagate(
    constraints: &[Constraint],
    trail: &mut Trail,
    num_vars: usize,
) -> PropagationResult {
    propagate_with_deadline(constraints, trail, num_vars, None)
}

/// Deadline-aware variant of [`propagate`]. When `deadline` is `Some` and the
/// current time exceeds it, the function returns [`PropagationResult::Ok`]
/// without completing the fixed-point. The caller (the main `solve` loop) is
/// responsible for re-checking the deadline and returning
/// [`crate::types::IntSatResult::Unknown`] once control returns.
pub(crate) fn propagate_with_deadline(
    constraints: &[Constraint],
    trail: &mut Trail,
    num_vars: usize,
    deadline: Option<Instant>,
) -> PropagationResult {
    // Fixed-point loop: keep propagating until no new bounds are derived.
    let mut changed = true;
    // Check the deadline every N constraints to amortise the syscall.
    const DEADLINE_CHECK_STRIDE: usize = 32;
    let mut since_deadline_check: usize = 0;
    while changed {
        changed = false;
        for (cidx, constraint) in constraints.iter().enumerate() {
            if deadline.is_some() {
                since_deadline_check += 1;
                if since_deadline_check >= DEADLINE_CHECK_STRIDE {
                    since_deadline_check = 0;
                    if deadline.is_some_and(|dl| Instant::now() >= dl) {
                        // Bail out of the fixpoint. Returning `Ok` is safe: any
                        // conflict that would have been discovered here will
                        // simply be found on the next `solve()` iteration, at
                        // which point the outer deadline check aborts cleanly.
                        return PropagationResult::Ok;
                    }
                }
            }
            match propagate_constraint(cidx, constraint, trail, num_vars) {
                ConstraintPropResult::NewBounds(bounds) => {
                    for entry in bounds {
                        trail.push_bound(entry);
                        changed = true;
                    }
                }
                ConstraintPropResult::Conflict => {
                    return PropagationResult::Conflict {
                        constraint_idx: cidx,
                    };
                }
                ConstraintPropResult::NoBounds => {}
            }
        }
    }
    PropagationResult::Ok
}

enum ConstraintPropResult {
    NewBounds(Vec<BoundEntry>),
    Conflict,
    NoBounds,
}

/// Propagate bounds from a single constraint.
fn propagate_constraint(
    constraint_idx: usize,
    constraint: &Constraint,
    trail: &Trail,
    _num_vars: usize,
) -> ConstraintPropResult {
    let level = trail.current_level();

    // First, check if the constraint is already falsified.
    // A constraint `sum(ai*xi) <= b` is falsified when `min(sum(ai*xi)) > b`.
    let total_min = compute_min_lhs(constraint, trail);
    let Some(total_min) = total_min else {
        // Some variable has no bound in the required direction -- cannot propagate.
        return ConstraintPropResult::NoBounds;
    };

    if total_min > constraint.rhs {
        return ConstraintPropResult::Conflict;
    }

    // For each variable, compute the slack and derive a new bound.
    let mut new_bounds = Vec::new();

    for (var, coeff) in &constraint.coeffs {
        if coeff.is_zero() {
            continue;
        }

        // Compute min of all other terms: total_min - min(coeff * var)
        let Some(self_min) = trail.min_contribution(*var, coeff) else {
            continue; // Cannot compute slack for this variable.
        };
        let others_min = &total_min - &self_min;
        let slack = &constraint.rhs - &others_min;

        if coeff.is_positive() {
            // Upper bound: xj <= floor(slack / aj)
            let new_ub = floor_div(&slack, coeff);
            let current_ub = trail.upper_bound(*var);
            let tighter =
                current_ub.is_none() || new_ub < *current_ub.expect("invariant: checked is_none");

            if tighter {
                // Check for conflict: new upper < current lower.
                if let Some(lb) = trail.lower_bound(*var) {
                    if new_ub < *lb {
                        return ConstraintPropResult::Conflict;
                    }
                }
                new_bounds.push(BoundEntry {
                    var: *var,
                    value: new_ub,
                    is_upper: true,
                    reason: BoundReason::Propagation { constraint_idx },
                    level,
                });
            }
        } else {
            // Negative coefficient: lower bound.
            // xj >= ceil(slack / aj) where aj < 0.
            // Dividing by negative flips: xj >= ceil(slack / |aj|) with adjusted sign.
            // More precisely: aj*xj <= slack => xj >= slack/aj (flip because aj < 0).
            // ceil(slack / aj) for aj < 0: since aj < 0, slack/aj = -slack/|aj|.
            // ceil(-slack/|aj|) = -floor(slack/|aj|)
            let abs_coeff = coeff.abs();
            let new_lb = -floor_div(&slack, &abs_coeff);
            let current_lb = trail.lower_bound(*var);
            let tighter =
                current_lb.is_none() || new_lb > *current_lb.expect("invariant: checked is_none");

            if tighter {
                // Check for conflict: new lower > current upper.
                if let Some(ub) = trail.upper_bound(*var) {
                    if new_lb > *ub {
                        return ConstraintPropResult::Conflict;
                    }
                }
                new_bounds.push(BoundEntry {
                    var: *var,
                    value: new_lb,
                    is_upper: false,
                    reason: BoundReason::Propagation { constraint_idx },
                    level,
                });
            }
        }
    }

    if new_bounds.is_empty() {
        ConstraintPropResult::NoBounds
    } else {
        ConstraintPropResult::NewBounds(new_bounds)
    }
}

/// Compute the minimum value of the LHS `sum(ai*xi)` given current bounds.
///
/// Returns None if some variable lacks the required bound.
#[must_use]
pub(crate) fn compute_min_lhs(constraint: &Constraint, trail: &Trail) -> Option<BigInt> {
    let mut total = BigInt::zero();
    for (var, coeff) in &constraint.coeffs {
        total += trail.min_contribution(*var, coeff)?;
    }
    Some(total)
}

/// Check if a constraint is currently falsified.
#[must_use]
#[allow(dead_code)]
pub(crate) fn is_falsified(constraint: &Constraint, trail: &Trail) -> bool {
    compute_min_lhs(constraint, trail).is_some_and(|min_lhs| min_lhs > constraint.rhs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{BoundEntry, BoundReason, VarId};

    fn setup_bounded_trail() -> Trail {
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
        trail
    }

    #[test]
    fn test_propagate_upper_bound() {
        let mut trail = setup_bounded_trail();
        // x0 + x1 <= 5
        let constraints = vec![Constraint {
            coeffs: vec![(VarId(0), BigInt::from(1)), (VarId(1), BigInt::from(1))],
            rhs: BigInt::from(5),
        }];

        let result = propagate(&constraints, &mut trail, 2);
        assert!(matches!(result, PropagationResult::Ok));

        // Should derive: x0 <= 5, x1 <= 5 (since other var's min is 0)
        assert!(trail.upper_bound(VarId(0)).expect("should have upper") <= &BigInt::from(5));
        assert!(trail.upper_bound(VarId(1)).expect("should have upper") <= &BigInt::from(5));
    }

    #[test]
    fn test_propagate_conflict() {
        let mut trail = Trail::new();
        // x0 >= 5
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        // x0 <= 10
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(10),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        // x0 <= 3 (conflicts with x0 >= 5)
        let constraints = vec![Constraint {
            coeffs: vec![(VarId(0), BigInt::from(1))],
            rhs: BigInt::from(3),
        }];

        let result = propagate(&constraints, &mut trail, 1);
        assert!(matches!(result, PropagationResult::Conflict { .. }));
    }

    #[test]
    fn test_propagate_negative_coeff() {
        let mut trail = Trail::new();
        // x0 in [0, 10]
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(0),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(10),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });
        // x1 in [0, 10]
        trail.push_bound(BoundEntry {
            var: VarId(1),
            value: BigInt::from(0),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        trail.push_bound(BoundEntry {
            var: VarId(1),
            value: BigInt::from(10),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        // -x0 + x1 <= 2 means x1 - x0 <= 2
        // With x0 >= 0, x1 >= 0: propagates x1 <= 2 + max(x0) = 12 (but x1 <= 10 tighter)
        // With x1 <= 10: propagates x0 >= x1_min - 2 = -2 (but x0 >= 0 tighter)
        let constraints = vec![Constraint {
            coeffs: vec![(VarId(0), BigInt::from(-1)), (VarId(1), BigInt::from(1))],
            rhs: BigInt::from(2),
        }];

        let result = propagate(&constraints, &mut trail, 2);
        assert!(matches!(result, PropagationResult::Ok));
    }
}
