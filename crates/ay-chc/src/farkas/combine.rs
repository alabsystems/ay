// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas combination strategies for linear constraint sets.
//!
//! Given UNSAT linear constraints, finds non-negative coefficients
//! that combine them into a contradiction or a simpler constraint.

use crate::proof_interpolation::rational64_abs;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_rational::Rational64;

use super::build_linear_inequality;
use super::linear::{checked_r64_add, checked_r64_mul, checked_r64_neg, LinearConstraint};

/// Result of Farkas combination
#[derive(Debug, Clone)]
pub(crate) struct FarkasCombination {
    /// The combined constraint as a ChcExpr
    pub(crate) combined: ChcExpr,
}

/// Try to combine linear constraints using Farkas coefficients.
///
/// Given a set of linear inequalities that are UNSAT, this finds non-negative
/// coefficients λᵢ such that the weighted sum of constraints produces a
/// contradiction (0 < 0 or sum < 0).
///
/// Returns the combined constraint if successful.
///
/// # Contracts
///
/// REQUIRES: All expressions in `constraints` are linear arithmetic inequalities
///           (operators: ≤, <, ≥, >, = over LIA terms).
///
/// ENSURES: If `Some(fc)` is returned:
///          1. `fc.combined` is implied by `∧constraints`
///          2. `fc.combined` uses only variables from `constraints`
///          3. `fc.combined` is a weaker (more general) constraint than the input
///
/// ENSURES: `None` is returned if:
///          - Fewer than 2 constraints can be parsed as linear inequalities
///          - No combination strategy finds a useful result
///          - All variables have zero coefficient after combination
///
/// # Known Limitations
///
/// - Only supports 4 strategies: equal weights, variable elimination,
///   transitivity chains, and bound tightening
///
/// Note: Rational coefficient handling was fixed in #1025 via LCM normalization.
///
/// Rational64 arithmetic can overflow i64 on large BV-derived coefficients.
/// Each strategy is wrapped in catch_unwind so overflow panics degrade to
/// "strategy unavailable" instead of crashing the solver (Part of #6047).
pub(crate) fn farkas_combine(constraints: &[ChcExpr]) -> Option<FarkasCombination> {
    use super::linear::parse_linear_constraint;

    // Parse all constraints as linear inequalities
    let linear: Vec<LinearConstraint> = constraints
        .iter()
        .filter_map(parse_linear_constraint)
        .collect();

    if linear.len() < 2 {
        return None; // Need at least 2 constraints to combine
    }

    // Collect all variables
    let mut all_vars: Vec<String> = linear
        .iter()
        .flat_map(|c| c.coeffs.keys().cloned())
        .collect();
    all_vars.sort();
    all_vars.dedup();

    if all_vars.is_empty() {
        return None; // No variables, nothing to combine
    }

    // Strategy 1: Equal weights (λᵢ = 1 for all i)
    // This works when the constraints directly sum to a contradiction.
    if let Some(fc) = try_equal_weights(&linear) {
        return Some(fc);
    }

    // Strategy 2: Variable elimination by opposite signs
    // If a variable appears with opposite signs in exactly 2 constraints,
    // combine them to eliminate that variable.
    if let Some(fc) = try_variable_elimination(&linear, &all_vars) {
        return Some(fc);
    }

    // Strategy 3: Transitivity chains
    // For constraints like x <= y + c1, y <= z + c2, derive x <= z + (c1+c2)
    if let Some(fc) = try_transitivity_chain(&linear, &all_vars) {
        return Some(fc);
    }

    // Strategy 4: Bound tightening
    // Combine multiple bounds on the same variable to get tighter bounds
    if let Some(fc) = try_bound_tightening(&linear, &all_vars) {
        return Some(fc);
    }

    None
}

/// Strategy 1: Try equal weights (all λᵢ = 1)
fn try_equal_weights(linear: &[LinearConstraint]) -> Option<FarkasCombination> {
    let mut sum_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut sum_bound = Rational64::from_integer(0);
    let mut any_strict = false;

    for c in linear {
        for (var, coeff) in &c.coeffs {
            let current = sum_coeffs
                .get(var)
                .copied()
                .unwrap_or(Rational64::from_integer(0));
            sum_coeffs.insert(var.clone(), checked_r64_add(current, *coeff)?);
        }
        sum_bound = checked_r64_add(sum_bound, c.bound)?;
        any_strict = any_strict || c.strict;
    }

    // Check if coefficients cancel (Σᵢ aᵢ = 0 for all variables)
    let coeffs_cancel = sum_coeffs
        .values()
        .all(|c| *c == Rational64::from_integer(0));

    if coeffs_cancel
        && (sum_bound < Rational64::from_integer(0)
            || (any_strict && sum_bound <= Rational64::from_integer(0)))
    {
        // Pure contradiction: 0 ≤ negative or 0 < 0
        return Some(FarkasCombination {
            combined: ChcExpr::Bool(false),
        });
    }

    None
}

/// Strategy 2: Variable elimination by opposite signs
fn try_variable_elimination(
    linear: &[LinearConstraint],
    all_vars: &[String],
) -> Option<FarkasCombination> {
    for var in all_vars {
        let relevant: Vec<usize> = linear
            .iter()
            .enumerate()
            .filter(|(_, c)| c.coeffs.contains_key(var))
            .map(|(i, _)| i)
            .collect();

        if relevant.len() == 2 {
            let c1 = &linear[relevant[0]];
            let c2 = &linear[relevant[1]];
            let coeff1 = c1.get_coeff(var);
            let coeff2 = c2.get_coeff(var);

            // Check if they have opposite signs
            if (coeff1 > Rational64::from_integer(0)) != (coeff2 > Rational64::from_integer(0)) {
                // Combine with weights |coeff2| and |coeff1| to eliminate var
                let w1 = rational64_abs(coeff2);
                let w2 = rational64_abs(coeff1);

                let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
                for (v, c) in &c1.coeffs {
                    combined_coeffs.insert(v.clone(), checked_r64_mul(*c, w1)?);
                }
                for (v, c) in &c2.coeffs {
                    let current = combined_coeffs
                        .get(v)
                        .copied()
                        .unwrap_or(Rational64::from_integer(0));
                    let term = checked_r64_mul(*c, w2)?;
                    combined_coeffs.insert(v.clone(), checked_r64_add(current, term)?);
                }
                let combined_bound = checked_r64_add(
                    checked_r64_mul(c1.bound, w1)?,
                    checked_r64_mul(c2.bound, w2)?,
                )?;
                let combined_strict = c1.strict || c2.strict;

                // Remove zero coefficients
                combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

                // Build the combined expression.
                // i128-lockstep: scaling overflow → abstain (no combination).
                let combined_expr =
                    build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)?;

                return Some(FarkasCombination {
                    combined: combined_expr,
                });
            }
        }
    }
    None
}

/// Strategy 3: Transitivity chains
/// For constraints like x - y <= c1, y - z <= c2, derive x - z <= c1 + c2
fn try_transitivity_chain(
    linear: &[LinearConstraint],
    all_vars: &[String],
) -> Option<FarkasCombination> {
    // Look for difference constraints: x - y <= c
    // These have exactly two variables with coefficients +1 and -1

    #[derive(Clone)]
    struct DiffConstraint {
        from: String, // positive coefficient variable
        to: String,   // negative coefficient variable
        bound: Rational64,
        strict: bool,
    }

    let mut diff_constraints: Vec<DiffConstraint> = Vec::new();

    for c in linear {
        if c.coeffs.len() == 2 {
            let coeffs: Vec<_> = c.coeffs.iter().collect();
            let (v1, c1) = coeffs[0];
            let (v2, c2) = coeffs[1];

            // Check for +1/-1 pattern
            if *c1 == Rational64::from_integer(1) && *c2 == Rational64::from_integer(-1) {
                diff_constraints.push(DiffConstraint {
                    from: v1.clone(),
                    to: v2.clone(),
                    bound: c.bound,
                    strict: c.strict,
                });
            } else if *c1 == Rational64::from_integer(-1) && *c2 == Rational64::from_integer(1) {
                diff_constraints.push(DiffConstraint {
                    from: v2.clone(),
                    to: v1.clone(),
                    bound: c.bound,
                    strict: c.strict,
                });
            }
        }
    }

    // Try to find a chain: x -> y -> z (3 or more variables)
    for start_var in all_vars {
        // Find all paths from start_var
        let mut visited: ay_core::kani_compat::DetHashSet<String> =
            ay_core::kani_compat::DetHashSet::default();
        visited.insert(start_var.clone());

        let mut frontier: Vec<(String, Rational64, bool)> =
            vec![(start_var.clone(), Rational64::from_integer(0), false)];

        while let Some((current, current_bound, current_strict)) = frontier.pop() {
            for dc in &diff_constraints {
                if dc.from == current && !visited.contains(&dc.to) {
                    let new_bound = match checked_r64_add(current_bound, dc.bound) {
                        Some(b) => b,
                        None => continue, // overflow — skip this edge
                    };
                    let new_strict = current_strict || dc.strict;

                    // Check if we've found a path back to start (cycle)
                    // Or if we can combine with another constraint on the end variable
                    for c in linear {
                        // Look for a constraint on dc.to that would create a contradiction
                        // or a useful combination
                        if c.coeffs.len() == 1 {
                            if let Some(coeff) = c.coeffs.get(&dc.to) {
                                if *coeff == Rational64::from_integer(1) {
                                    // dc.to <= c.bound, and start_var - dc.to <= new_bound
                                    // so start_var <= new_bound + c.bound
                                    let combined_bound = match checked_r64_add(new_bound, c.bound) {
                                        Some(b) => b,
                                        None => continue,
                                    };
                                    let combined_strict = new_strict || c.strict;

                                    let mut combined_coeffs = FxHashMap::default();
                                    combined_coeffs
                                        .insert(start_var.clone(), Rational64::from_integer(1));

                                    // i128-lockstep: overflow → skip (abstention).
                                    let Some(combined) = build_linear_inequality(
                                        &combined_coeffs,
                                        combined_bound,
                                        combined_strict,
                                    ) else {
                                        continue;
                                    };
                                    return Some(FarkasCombination { combined });
                                } else if *coeff == Rational64::from_integer(-1) {
                                    // -dc.to <= c.bound means dc.to >= -c.bound
                                    // Combined with start_var - dc.to <= new_bound:
                                    // start_var >= -c.bound + (dc.to - start_var) >= -c.bound - new_bound
                                    // So start_var >= -(c.bound + new_bound)
                                    let sum = match checked_r64_add(c.bound, new_bound) {
                                        Some(s) => s,
                                        None => continue,
                                    };
                                    let combined_bound = match checked_r64_neg(sum) {
                                        Some(b) => b,
                                        None => continue,
                                    };
                                    let combined_strict = new_strict || c.strict;

                                    let mut combined_coeffs = FxHashMap::default();
                                    combined_coeffs
                                        .insert(start_var.clone(), Rational64::from_integer(-1));

                                    // i128-lockstep: overflow → skip (abstention).
                                    let Some(combined) = build_linear_inequality(
                                        &combined_coeffs,
                                        combined_bound,
                                        combined_strict,
                                    ) else {
                                        continue;
                                    };
                                    return Some(FarkasCombination { combined });
                                }
                            }
                        }
                    }

                    visited.insert(dc.to.clone());
                    frontier.push((dc.to.clone(), new_bound, new_strict));
                }
            }
        }
    }

    None
}

/// Strategy 4: Bound tightening
/// Combine multiple bounds on the same variable
fn try_bound_tightening(
    linear: &[LinearConstraint],
    all_vars: &[String],
) -> Option<FarkasCombination> {
    // For single-variable constraints, find the tightest bounds
    for var in all_vars {
        let mut upper_bounds: Vec<(Rational64, bool)> = Vec::new();
        let mut lower_bounds: Vec<(Rational64, bool)> = Vec::new();

        for c in linear {
            if c.coeffs.len() == 1 {
                if let Some(coeff) = c.coeffs.get(var) {
                    if *coeff == Rational64::from_integer(1) {
                        // var <= bound (after flipping sign)
                        upper_bounds.push((c.bound, c.strict));
                    } else if *coeff == Rational64::from_integer(-1) {
                        // -var <= bound means var >= -bound
                        let neg = checked_r64_neg(c.bound)?;
                        lower_bounds.push((neg, c.strict));
                    }
                }
            }
        }

        // If we have both upper and lower bounds, check for contradiction
        if !upper_bounds.is_empty() && !lower_bounds.is_empty() {
            let (min_upper, upper_strict) = upper_bounds
                .iter()
                .min_by(|a, b| a.0.cmp(&b.0))
                .expect("non-empty");
            let (max_lower, lower_strict) = lower_bounds
                .iter()
                .max_by(|a, b| a.0.cmp(&b.0))
                .expect("non-empty");

            if max_lower > min_upper || ((*upper_strict || *lower_strict) && max_lower >= min_upper)
            {
                // Contradiction: var >= max_lower and var <= min_upper but max_lower > min_upper
                return Some(FarkasCombination {
                    combined: ChcExpr::Bool(false),
                });
            }
        }
    }

    None
}
