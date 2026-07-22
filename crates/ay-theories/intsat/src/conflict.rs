// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict analysis via the cut rule for IntSat.
//!
//! When a constraint is falsified, IntSat traces back through the trail
//! using the cut rule (analogous to resolution in SAT) to derive a learned
//! constraint. The cut rule eliminates a variable from two constraints that
//! have opposite-sign coefficients for that variable.
//!
//! The analysis continues until reaching 1UIP: exactly one bound at the
//! current decision level appears in the conflict constraint. The resulting
//! constraint is the learned clause, and the backjump level is determined
//! by the second-highest decision level among the constraint's bounds.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};

use crate::normalize::normalize_constraint;
use crate::trail::Trail;
use crate::types::{AnalysisResult, BoundReason, Constraint, VarId};

/// Perform 1UIP conflict analysis starting from a falsified constraint.
///
/// Returns the learned constraint and the backjump level.
pub(crate) fn analyze_conflict(
    conflict_constraint_idx: usize,
    constraints: &[Constraint],
    trail: &Trail,
) -> Option<AnalysisResult> {
    let current_level = trail.current_level();
    if current_level == 0 {
        return None; // UNSAT at level 0
    }

    let mut conflict = constraints[conflict_constraint_idx].clone();

    // Iteratively resolve against reason constraints until 1UIP.
    // Walk the trail backwards, resolving variables at the current level.
    let entries = trail.entries();
    let mut resolved_count = 0;
    const MAX_RESOLUTIONS: usize = 10_000;

    // Process trail entries from most recent to oldest.
    for i in (0..entries.len()).rev() {
        if resolved_count >= MAX_RESOLUTIONS {
            break;
        }

        // Check 1UIP condition: count bounds at current level in the conflict.
        let current_level_vars = count_current_level_bounds(&conflict, trail, current_level);
        if current_level_vars <= 1 {
            break;
        }

        let entry = &entries[i];
        if entry.level != current_level {
            continue;
        }

        // Check if this variable appears in the conflict constraint.
        let var = entry.var;
        let coeff_in_conflict = get_coefficient(&conflict, var);
        if coeff_in_conflict.is_zero() {
            continue;
        }

        // Find the reason constraint for this bound.
        let BoundReason::Propagation { constraint_idx } = &entry.reason else {
            continue; // Can only resolve against propagation reasons.
        };

        let reason = &constraints[*constraint_idx];

        // Apply the cut rule to eliminate `var` from the conflict.
        if let Some(resolved) = cut_rule(&conflict, reason, var) {
            conflict = resolved;
            resolved_count += 1;
        }
    }

    // Normalize the learned constraint.
    normalize_constraint(&mut conflict);

    // Determine backjump level: second-highest decision level among the
    // constraint's variable bounds.
    let backjump = compute_backjump_level(&conflict, trail, current_level);

    Some(AnalysisResult {
        learned: conflict,
        backjump_level: backjump,
    })
}

/// Count how many variables in the constraint have their most recent relevant
/// bound at the given decision level.
fn count_current_level_bounds(constraint: &Constraint, trail: &Trail, level: u32) -> usize {
    let mut count = 0;
    for (var, coeff) in &constraint.coeffs {
        if coeff.is_zero() {
            continue;
        }
        // For a constraint `... + a*x + ... <= b`:
        // - If a > 0, the bound on x that matters is its lower bound (for falsification).
        // - If a < 0, the bound on x that matters is its upper bound.
        let is_upper = coeff.is_negative();
        if let Some(bound_level) = trail.level_of_bound(*var, is_upper) {
            if bound_level == level {
                count += 1;
            }
        }
    }
    count
}

/// Get the coefficient of `var` in the constraint (0 if not present).
#[must_use]
fn get_coefficient(constraint: &Constraint, var: VarId) -> BigInt {
    for (v, c) in &constraint.coeffs {
        if *v == var {
            return c.clone();
        }
    }
    BigInt::zero()
}

/// Apply the cut rule to eliminate `var` from two constraints.
///
/// Given:
///   C1: ... + a*var + ... <= r1  (with a having some sign)
///   C2: ... + b*var + ... <= r2  (with b having opposite sign)
///
/// Multiply C1 by |b| and C2 by |a|, then add. The `var` terms cancel.
/// The result is GCD-normalized.
fn cut_rule(c1: &Constraint, c2: &Constraint, var: VarId) -> Option<Constraint> {
    let a = get_coefficient(c1, var);
    let b = get_coefficient(c2, var);

    if a.is_zero() || b.is_zero() {
        return None;
    }

    // The coefficients must have opposite signs for cancellation.
    if a.signum() == b.signum() {
        return None;
    }

    let abs_a = a.abs();
    let abs_b = b.abs();

    // Multipliers: multiply C1 by abs_b, C2 by abs_a.
    // After addition, var's coefficient becomes: abs_b * a + abs_a * b.
    // Since a and b have opposite signs, this is zero.
    let l = abs_a.lcm(&abs_b);
    let mult1 = &l / &abs_a;
    let mult2 = &l / &abs_b;

    let mut combined: HashMap<VarId, BigInt> = HashMap::default();

    for (v, c) in &c1.coeffs {
        *combined.entry(*v).or_insert_with(BigInt::zero) += &mult1 * c;
    }
    for (v, c) in &c2.coeffs {
        *combined.entry(*v).or_insert_with(BigInt::zero) += &mult2 * c;
    }

    // Remove zero coefficients and the eliminated variable.
    combined.retain(|_, c| !c.is_zero());

    let rhs = &mult1 * &c1.rhs + &mult2 * &c2.rhs;

    let mut coeffs: Vec<(VarId, BigInt)> = combined.into_iter().collect();
    coeffs.sort_by_key(|(v, _)| *v);

    let mut result = Constraint { coeffs, rhs };
    normalize_constraint(&mut result);

    Some(result)
}

/// Compute the backjump level: the second-highest decision level among the
/// bounds referenced by the constraint's variables.
fn compute_backjump_level(constraint: &Constraint, trail: &Trail, current_level: u32) -> u32 {
    let mut max_level: u32 = 0;

    for (var, coeff) in &constraint.coeffs {
        if coeff.is_zero() {
            continue;
        }
        let is_upper = coeff.is_negative();
        if let Some(bound_level) = trail.level_of_bound(*var, is_upper) {
            if bound_level < current_level && bound_level > max_level {
                max_level = bound_level;
            }
        }
    }

    max_level
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cut_rule_basic() {
        // C1: x + y <= 5
        let c1 = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(1)), (VarId(1), BigInt::from(1))],
            rhs: BigInt::from(5),
        };
        // C2: -x + z <= 3
        let c2 = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(-1)), (VarId(2), BigInt::from(1))],
            rhs: BigInt::from(3),
        };

        let result = cut_rule(&c1, &c2, VarId(0));
        assert!(result.is_some());
        let result = result.expect("should produce a result");
        // Eliminating x: 1*C1 + 1*C2 = y + z <= 8
        assert_eq!(result.rhs, BigInt::from(8));
        assert_eq!(result.coeffs.len(), 2);
    }

    #[test]
    fn test_cut_rule_same_sign_fails() {
        // Both positive for x: can't eliminate.
        let c1 = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(2))],
            rhs: BigInt::from(5),
        };
        let c2 = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(3))],
            rhs: BigInt::from(7),
        };

        assert!(cut_rule(&c1, &c2, VarId(0)).is_none());
    }
}
