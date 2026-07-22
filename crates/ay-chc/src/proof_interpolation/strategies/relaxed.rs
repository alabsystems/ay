// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Strategy 1.25: Relaxed B-origin combination that allows locals to cancel.
pub(crate) fn try_relaxed_b_origin_combination(
    conflict_terms: &[TermId],
    origins: &[Partition],
    polarities: &[bool],
    coefficients: &[Rational64],
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    use crate::farkas::parse_linear_constraint;

    if origins.len() != conflict_terms.len() {
        iuc_trace!("try_relaxed_b_origin_combination: origins not available");
        return None;
    }

    let mut b_origin_contribs: Vec<(Rational64, FxHashMap<String, Rational64>, Rational64, bool)> =
        Vec::new();

    for (idx, ((&atom, &polarity), &coeff)) in conflict_terms
        .iter()
        .zip(polarities.iter())
        .zip(coefficients.iter())
        .enumerate()
    {
        let weight = rational64_abs(coeff);
        if weight == Rational64::from_integer(0) {
            continue;
        }

        let Some(expr) = atom_to_expr.get(&atom) else {
            continue;
        };

        if origins[idx] != Partition::B {
            continue;
        }

        let constraint_expr = if polarity {
            expr.clone()
        } else {
            ChcExpr::not(expr.clone())
        };

        let Some(lin) = parse_linear_constraint(&constraint_expr) else {
            continue;
        };

        b_origin_contribs.push((weight, lin.coeffs, lin.bound, lin.strict));
    }

    if b_origin_contribs.is_empty() {
        iuc_trace!("try_relaxed_b_origin_combination: no B-origin literals found");
        return None;
    }

    let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut combined_bound: Rational64 = Rational64::from_integer(0);
    let mut combined_strict = false;

    for (weight, coeffs, bound, strict) in &b_origin_contribs {
        combined_strict |= *strict;
        combined_bound += *weight * *bound;
        for (var, c) in coeffs {
            let entry = combined_coeffs
                .entry(var.clone())
                .or_insert(Rational64::from_integer(0));
            *entry += *weight * *c;
        }
    }

    combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

    let non_shared: Vec<&String> = combined_coeffs
        .keys()
        .filter(|v| !shared_vars.contains(*v))
        .collect();

    if !non_shared.is_empty() {
        let mut subst_bound_adj: Rational64 = Rational64::from_integer(0);
        let mut vars_eliminated: Vec<String> = Vec::new();
        let non_shared_set: FxHashSet<String> = non_shared.iter().map(|s| (*s).clone()).collect();

        for (_, coeffs, bound, _) in &b_origin_contribs {
            let non_shared_in_eq: Vec<(&String, &Rational64)> = coeffs
                .iter()
                .filter(|(v, _)| non_shared_set.contains(*v) && !vars_eliminated.contains(v))
                .collect();

            if non_shared_in_eq.len() != 1 {
                continue;
            }

            let (elim_var, elim_coeff) = non_shared_in_eq[0];
            if *elim_coeff == Rational64::from_integer(0) {
                continue;
            }

            if let Some(&combined_coeff) = combined_coeffs.get(elim_var) {
                let ratio = combined_coeff / *elim_coeff;
                combined_coeffs.remove(elim_var);
                for (var, c) in coeffs {
                    if var == elim_var {
                        continue;
                    }
                    let entry = combined_coeffs
                        .entry(var.clone())
                        .or_insert(Rational64::from_integer(0));
                    *entry -= ratio * *c;
                }
                subst_bound_adj -= ratio * *bound;
                vars_eliminated.push(elim_var.clone());
            }
        }

        if !vars_eliminated.is_empty() {
            combined_bound += subst_bound_adj;
            combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

            let remaining_non_shared: Vec<&String> = combined_coeffs
                .keys()
                .filter(|v| !shared_vars.contains(*v))
                .collect();

            if !remaining_non_shared.is_empty() {
                iuc_trace!(
                    "try_relaxed_b_origin_combination: equality substitution eliminated {:?} but {:?} remain",
                    vars_eliminated,
                    remaining_non_shared
                );
                return None;
            }
        } else {
            return None;
        }
    }

    let combined = build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)?;
    let candidate = ChcExpr::not(combined)
        .normalize_negations()
        .normalize_strict_int_comparisons()
        .simplify_constants();

    if matches!(candidate, ChcExpr::Bool(true | false)) {
        iuc_trace!("try_relaxed_b_origin_combination: trivial constraint");
        return None;
    }

    iuc_trace!(
        "try_relaxed_b_origin_combination: success! candidate = {} (locals canceled/substituted)",
        candidate
    );
    Some(candidate)
}

/// Strategy 1.5: Per-clause interpolation without Farkas combination.
pub(crate) fn try_per_clause_interpolation(
    conflict_terms: &[TermId],
    origins: &[Partition],
    polarities: &[bool],
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    if origins.len() != conflict_terms.len() {
        iuc_trace!("try_per_clause_interpolation: origins not available");
        return None;
    }

    let mut clause_literals: Vec<ChcExpr> = Vec::new();

    for (idx, ((&atom, &polarity), &origin)) in conflict_terms
        .iter()
        .zip(polarities.iter())
        .zip(origins.iter())
        .enumerate()
    {
        if origin != Partition::B {
            continue;
        }

        let Some(expr) = atom_to_expr.get(&atom) else {
            continue;
        };

        if !vars_all_shared(expr, shared_vars) {
            continue;
        }

        let lit = if polarity {
            ChcExpr::not(expr.clone())
        } else {
            expr.clone()
        };

        let normalized = lit
            .normalize_negations()
            .normalize_strict_int_comparisons()
            .simplify_constants();

        if matches!(normalized, ChcExpr::Bool(true)) {
            continue;
        }
        if matches!(normalized, ChcExpr::Bool(false)) {
            iuc_trace!(
                "try_per_clause_interpolation: literal {} normalized to false",
                idx
            );
            continue;
        }

        clause_literals.push(normalized);
    }

    if clause_literals.is_empty() {
        iuc_trace!("try_per_clause_interpolation: no B-pure literals found");
        return None;
    }

    let candidate = ChcExpr::or_all(clause_literals);
    iuc_trace!("try_per_clause_interpolation: candidate = {}", candidate);
    Some(candidate)
}
