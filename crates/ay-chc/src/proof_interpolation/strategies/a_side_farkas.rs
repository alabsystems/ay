// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Strategy 1.75: A-side Farkas combination with FM projection (#2450).
pub(crate) fn try_a_side_farkas_projection(
    conflict_terms: &[TermId],
    origins: &[Partition],
    polarities: &[bool],
    coefficients: &[Rational64],
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
    a_atoms_in_a: &FxHashSet<TermId>,
) -> Option<ChcExpr> {
    use crate::farkas::parse_linear_constraint;

    if origins.len() != conflict_terms.len() || coefficients.len() != conflict_terms.len() {
        return None;
    }

    let mut a_contribs: Vec<(Rational64, LinearConstraint)> = Vec::new();

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

        let is_a_side = origins[idx] == Partition::A
            || (origins[idx] == Partition::AB && a_atoms_in_a.contains(&atom));
        if !is_a_side {
            continue;
        }

        let Some(expr) = atom_to_expr.get(&atom) else {
            continue;
        };

        let constraint_expr = if polarity {
            expr.clone()
        } else {
            ChcExpr::not(expr.clone())
        };

        let Some(lin) = parse_linear_constraint(&constraint_expr) else {
            continue;
        };

        a_contribs.push((weight, lin));
    }

    if a_contribs.is_empty() {
        iuc_trace!("try_a_side_farkas_projection: no A-origin literals");
        return None;
    }

    let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut combined_bound: Rational64 = Rational64::from_integer(0);
    let mut combined_strict = false;

    for (weight, lin) in &a_contribs {
        combined_strict |= lin.strict;
        combined_bound += *weight * lin.bound;
        for (var, c) in &lin.coeffs {
            let entry = combined_coeffs
                .entry(var.clone())
                .or_insert(Rational64::from_integer(0));
            *entry += *weight * *c;
        }
    }

    combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

    if combined_coeffs.is_empty() {
        iuc_trace!("try_a_side_farkas_projection: A-sum is constant (no variables)");
        return None;
    }

    let non_shared: Vec<String> = combined_coeffs
        .keys()
        .filter(|v| !shared_vars.contains(*v))
        .cloned()
        .collect();

    if non_shared.is_empty() {
        let candidate = build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)?;
        if matches!(candidate, ChcExpr::Bool(true | false)) {
            return None;
        }
        iuc_trace!(
            "try_a_side_farkas_projection: direct A-sum candidate = {}",
            candidate
        );
        return Some(candidate);
    }

    let a_exprs: Vec<ChcExpr> = a_contribs
        .iter()
        .filter_map(|(_, lin)| build_linear_inequality(&lin.coeffs, lin.bound, lin.strict))
        .filter(|e| !matches!(e, ChcExpr::Bool(true | false)))
        .collect();

    if a_exprs.is_empty() {
        return None;
    }

    let vars_to_eliminate: FxHashSet<String> = non_shared.into_iter().collect();
    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();

    if let Some(fm_result) = try_fourier_motzkin_elimination(&a_exprs, &vars_to_eliminate_names) {
        if !matches!(fm_result, ChcExpr::Bool(true)) {
            return Some(fm_result);
        }
    }

    let mut result_parts: Vec<ChcExpr> = Vec::new();
    for (_, lin) in &a_contribs {
        let has_local = lin.coeffs.keys().any(|v| !shared_vars.contains(v));
        if !has_local {
            if let Some(expr) = build_linear_inequality(&lin.coeffs, lin.bound, lin.strict) {
                if !matches!(expr, ChcExpr::Bool(true | false)) {
                    result_parts.push(expr);
                }
            }
        }
    }

    if result_parts.is_empty() {
        return None;
    }

    Some(ChcExpr::and_all(result_parts))
}
