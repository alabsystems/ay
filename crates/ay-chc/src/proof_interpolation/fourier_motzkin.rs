// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fourier-Motzkin variable elimination.

use super::*;

/// Minimal Fourier-Motzkin bound elimination.
///
/// Instead of generating all |L| × |U| pairs (which causes exponential blowup),
/// this picks a representative bound from the smaller set and generates only
/// min(|L|, |U|) new constraints.
///
/// For variable `x` with lower bounds `L_i ≤ x` and upper bounds `x ≤ U_j`:
/// - Pick `L_rep` from lowers (prefer small support, coefficient ±1)
/// - Generate: `L_rep ≤ U_j` for all upper bounds
///
/// This is sound because each derived constraint `L_rep ≤ U_j` is implied by
/// the conjunction `L_rep ≤ x ∧ x ≤ U_j`.
///
/// Note: Limited to MAX_ELIMINATIONS (5) iterations to prevent blowup.
/// Returns None if non-shared variables remain after the limit.
pub(crate) fn try_fourier_motzkin_elimination(
    conjuncts: &[ChcExpr],
    vars_to_eliminate: &FxHashSet<&str>,
) -> Option<ChcExpr> {
    use crate::farkas::parse_linear_constraint;

    // Parse all conjuncts as linear constraints
    let mut constraints: Vec<(ChcExpr, Option<LinearConstraint>)> = conjuncts
        .iter()
        .map(|c| (c.clone(), parse_linear_constraint(c)))
        .collect();

    let mut eliminated = 0;
    const MAX_ELIMINATIONS: usize = 5; // Limit iterations to prevent blowup

    for &var in vars_to_eliminate {
        if eliminated >= MAX_ELIMINATIONS {
            iuc_trace!(
                "try_fourier_motzkin_elimination: hit elimination limit at {} vars",
                MAX_ELIMINATIONS
            );
            break;
        }

        // Partition constraints by bound direction for this variable
        let mut upper_bounds: Vec<(usize, Rational64)> = Vec::new(); // (index, coeff)
        let mut lower_bounds: Vec<(usize, Rational64)> = Vec::new(); // (index, abs_coeff)
        let mut unrelated: Vec<usize> = Vec::new();
        let mut cannot_eliminate = false; // Flag: variable appears in non-linear constraint

        for (idx, (expr, lin_opt)) in constraints.iter().enumerate() {
            let Some(lin) = lin_opt else {
                // Non-linear constraint - check if it contains the variable being eliminated
                if expr.vars().iter().any(|v| v.name == var) {
                    // This constraint contains var but isn't in linear form.
                    // We cannot eliminate var using F-M - skip this variable.
                    iuc_trace!(
                        "try_fourier_motzkin_elimination: {} appears in non-linear constraint, skipping",
                        var
                    );
                    cannot_eliminate = true;
                    break;
                }
                // Doesn't contain var - truly unrelated
                unrelated.push(idx);
                continue;
            };

            let coeff = lin
                .coeffs
                .get(var)
                .copied()
                .unwrap_or(Rational64::from_integer(0));
            if coeff == Rational64::from_integer(0) {
                unrelated.push(idx);
            } else if coeff > Rational64::from_integer(0) {
                // Positive coeff means: coeff * var + ... ≤ b => var ≤ (b - ...) / coeff
                upper_bounds.push((idx, coeff));
            } else {
                // Negative coeff means: coeff * var + ... ≤ b => var ≥ (... - b) / |coeff|
                lower_bounds.push((idx, rational64_abs(coeff)));
            }
        }

        // If var appears in a non-linear constraint, we can't eliminate it - skip
        if cannot_eliminate {
            continue;
        }

        if upper_bounds.is_empty() || lower_bounds.is_empty() {
            // Variable is unbounded on one side - can eliminate trivially by dropping
            // constraints that mention only this variable
            iuc_trace!(
                "try_fourier_motzkin_elimination: {} is unbounded (upper={}, lower={})",
                var,
                upper_bounds.len(),
                lower_bounds.len()
            );

            // Exactly eliminate the variable by dropping all its bounds.
            let kept: Vec<_> = unrelated.iter().map(|&i| constraints[i].clone()).collect();

            constraints = kept;
            eliminated += 1;
            continue;
        }

        // Pick representative from smaller side
        // Heuristic: prefer coefficient = 1 (no scaling needed), then smallest support
        let pick_representative = |bounds: &[(usize, Rational64)]| -> usize {
            let mut best = bounds[0].0;
            let mut best_score = i32::MAX;

            for &(idx, ref coeff) in bounds {
                let Some(lin) = &constraints[idx].1 else {
                    continue;
                };
                let support = lin.coeffs.len() as i32;
                let unit_coeff = if *coeff == Rational64::from_integer(1) {
                    0
                } else {
                    100
                };
                let score = support + unit_coeff;
                if score < best_score {
                    best_score = score;
                    best = idx;
                }
            }
            best
        };

        // Generate new constraints by combining representative with opposing bounds
        let mut new_constraints: Vec<(ChcExpr, Option<LinearConstraint>)> = Vec::new();

        // Keep unrelated constraints
        for &idx in &unrelated {
            new_constraints.push(constraints[idx].clone());
        }

        if lower_bounds.len() <= upper_bounds.len() {
            // Pick a lower bound representative, combine with each upper bound
            let lb_rep_idx = pick_representative(&lower_bounds);
            let Some(lb_lin) = &constraints[lb_rep_idx].1 else {
                continue;
            };

            for &(ub_idx, _) in &upper_bounds {
                let Some(ub_lin) = &constraints[ub_idx].1 else {
                    continue;
                };

                // Combine: lb ≤ x ≤ ub => lb ≤ ub
                // lb_lin: -a*x + ... ≤ b1  (where a > 0, so x ≥ (...-b1)/a)
                // ub_lin: c*x + ... ≤ b2   (where c > 0, so x ≤ (b2-...)/c)
                //
                // Multiply lb by c, ub by a, then add:
                // -ac*x + c*... + ac*x + a*... ≤ c*b1 + a*b2
                // => c*(...) + a*(...) ≤ c*b1 + a*b2
                let Some(lb_coeff_raw) = lb_lin.coeffs.get(var).copied() else {
                    // Unreachable: constraint was classified as lower bound for this var
                    safe_eprintln!(
                        "BUG: lower bound constraint missing variable coefficient for {var}"
                    );
                    return None;
                };
                let Some(ub_coeff) = ub_lin.coeffs.get(var).copied() else {
                    // Unreachable: constraint was classified as upper bound for this var
                    safe_eprintln!(
                        "BUG: upper bound constraint missing variable coefficient for {var}"
                    );
                    return None;
                };
                let lb_coeff = rational64_abs(lb_coeff_raw);

                let mut new_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
                let new_bound = ub_coeff * lb_lin.bound + lb_coeff * ub_lin.bound;

                // Add scaled coefficients from lb (excluding var)
                for (v, c) in &lb_lin.coeffs {
                    if v != var {
                        let entry = new_coeffs
                            .entry(v.clone())
                            .or_insert(Rational64::from_integer(0));
                        *entry += ub_coeff * *c;
                    }
                }

                // Add scaled coefficients from ub (excluding var)
                for (v, c) in &ub_lin.coeffs {
                    if v != var {
                        let entry = new_coeffs
                            .entry(v.clone())
                            .or_insert(Rational64::from_integer(0));
                        *entry += lb_coeff * *c;
                    }
                }

                // Remove zeros
                new_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

                // Build new constraint expression
                let new_strict = lb_lin.strict || ub_lin.strict;
                if let Some(new_expr) = build_linear_inequality(&new_coeffs, new_bound, new_strict)
                {
                    let new_lin = LinearConstraint {
                        coeffs: new_coeffs,
                        bound: new_bound,
                        strict: new_strict,
                        // Int-only proof-interpolation path (#chc25-lra-convergence).
                        var_sort: crate::ChcSort::Int,
                    };
                    new_constraints.push((new_expr, Some(new_lin)));
                }
            }
        } else {
            // Pick an upper bound representative, combine with each lower bound
            let ub_rep_idx = pick_representative(&upper_bounds);
            let Some(ub_lin) = &constraints[ub_rep_idx].1 else {
                continue;
            };

            for &(lb_idx, _) in &lower_bounds {
                let Some(lb_lin) = &constraints[lb_idx].1 else {
                    continue;
                };

                let Some(lb_coeff_raw) = lb_lin.coeffs.get(var).copied() else {
                    // Unreachable: constraint was classified as lower bound for this var
                    safe_eprintln!(
                        "BUG: lower bound constraint missing variable coefficient for {var}"
                    );
                    return None;
                };
                let Some(ub_coeff) = ub_lin.coeffs.get(var).copied() else {
                    // Unreachable: constraint was classified as upper bound for this var
                    safe_eprintln!(
                        "BUG: upper bound constraint missing variable coefficient for {var}"
                    );
                    return None;
                };
                let lb_coeff = rational64_abs(lb_coeff_raw);

                let mut new_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
                let new_bound = ub_coeff * lb_lin.bound + lb_coeff * ub_lin.bound;

                for (v, c) in &lb_lin.coeffs {
                    if v != var {
                        let entry = new_coeffs
                            .entry(v.clone())
                            .or_insert(Rational64::from_integer(0));
                        *entry += ub_coeff * *c;
                    }
                }

                for (v, c) in &ub_lin.coeffs {
                    if v != var {
                        let entry = new_coeffs
                            .entry(v.clone())
                            .or_insert(Rational64::from_integer(0));
                        *entry += lb_coeff * *c;
                    }
                }

                new_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

                let new_strict = lb_lin.strict || ub_lin.strict;
                if let Some(new_expr) = build_linear_inequality(&new_coeffs, new_bound, new_strict)
                {
                    let new_lin = LinearConstraint {
                        coeffs: new_coeffs,
                        bound: new_bound,
                        strict: new_strict,
                        // Int-only proof-interpolation path (#chc25-lra-convergence).
                        var_sort: crate::ChcSort::Int,
                    };
                    new_constraints.push((new_expr, Some(new_lin)));
                }
            }
        }

        constraints = new_constraints;
        eliminated += 1;
        iuc_trace!(
            "try_fourier_motzkin_elimination: eliminated {}, {} constraints remaining",
            var,
            constraints.len()
        );
    }

    // Check if we eliminated all non-shared variables
    let result_exprs: Vec<ChcExpr> = constraints.into_iter().map(|(e, _)| e).collect();
    let result_vars: FxHashSet<String> = result_exprs
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|v| v.name.clone())
        .collect();
    let still_non_shared: Vec<&String> = result_vars
        .iter()
        .filter(|v| vars_to_eliminate.contains(v.as_str()))
        .collect();

    if !still_non_shared.is_empty() {
        iuc_trace!(
            "try_fourier_motzkin_elimination: still have non-shared vars: {:?}",
            still_non_shared
        );
        return None;
    }

    // Filter out trivial constraints
    let filtered: Vec<ChcExpr> = result_exprs
        .into_iter()
        .filter(|e| !matches!(e, ChcExpr::Bool(true)))
        .collect();

    Some(ChcExpr::and_all(filtered))
}
