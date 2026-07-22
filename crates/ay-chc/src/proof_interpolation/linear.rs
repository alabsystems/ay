// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear constraint arithmetic.

use super::*;

/// Safe absolute value for Rational64 that handles i64::MIN numerator.
/// Rational64::abs() panics in debug (wraps in release) when numer == i64::MIN.
pub(crate) fn rational64_abs(r: Rational64) -> Rational64 {
    if *r.numer() == i64::MIN {
        Rational64::new(i64::MAX, *r.denom())
    } else {
        r.abs()
    }
}

pub(super) fn i64_gcd(a: i64, b: i64) -> i64 {
    let mut ua = a.unsigned_abs();
    let mut ub = b.unsigned_abs();
    while ub != 0 {
        let r = ua % ub;
        ua = ub;
        ub = r;
    }
    ua.min(i64::MAX as u64) as i64
}

pub(super) fn i64_lcm(a: i64, b: i64) -> Option<i64> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = i64_gcd(a, b);
    let a_abs = a.unsigned_abs();
    let b_abs = b.unsigned_abs();
    let lcm = (a_abs / g as u64).checked_mul(b_abs)?;
    if lcm > i64::MAX as u64 {
        None
    } else {
        Some(lcm as i64)
    }
}

pub(crate) fn build_linear_inequality(
    coeffs: &FxHashMap<String, Rational64>,
    bound: Rational64,
    strict: bool,
) -> Option<ChcExpr> {
    // We represent coefficients/bounds using i64, so clear denominators first.
    let mut lcm: i64 = 1;
    for c in coeffs.values() {
        let d = *c.denom();
        lcm = i64_lcm(lcm, d)?;
    }
    lcm = i64_lcm(lcm, *bound.denom())?;
    if lcm == 0 {
        return None;
    }

    let scale = Rational64::from_integer(lcm);
    let mut scaled_coeffs: Vec<(String, i64)> = Vec::with_capacity(coeffs.len());
    for (var, c) in coeffs {
        let scaled = *c * scale;
        if *scaled.denom() != 1 {
            return None;
        }
        scaled_coeffs.push((var.clone(), *scaled.numer()));
    }
    let scaled_bound = bound * scale;
    if *scaled_bound.denom() != 1 {
        return None;
    }
    let rhs_i64 = *scaled_bound.numer();

    scaled_coeffs.retain(|(_, c)| *c != 0);

    if scaled_coeffs.is_empty() {
        let ok = if strict { 0 < rhs_i64 } else { 0 <= rhs_i64 };
        return Some(ChcExpr::Bool(ok));
    }

    scaled_coeffs.sort_by(|a, b| a.0.cmp(&b.0));

    let mut terms: Vec<ChcExpr> = Vec::with_capacity(scaled_coeffs.len());
    for (var_name, coeff) in scaled_coeffs {
        let var = ChcVar::new(&var_name, ChcSort::Int);
        let var_expr = ChcExpr::var(var);
        match coeff {
            1 => terms.push(var_expr),
            -1 => terms.push(ChcExpr::neg(var_expr)),
            _ => terms.push(ChcExpr::mul(ChcExpr::int(coeff), var_expr)),
        }
    }

    let lhs = if terms.len() == 1 {
        terms.pop().expect("len==1")
    } else {
        ChcExpr::Op(
            ChcOp::Add,
            terms.into_iter().map(std::sync::Arc::new).collect(),
        )
    };

    let rhs = ChcExpr::int(rhs_i64);

    Some(if strict {
        ChcExpr::lt(lhs, rhs)
    } else {
        ChcExpr::le(lhs, rhs)
    })
}

/// Check if an expression is an equality constraint (not a disequality).
pub(super) fn is_equality_constraint(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => true,
        // NOT(x = c) is a disequality, not an equality
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => false,
        _ => false,
    }
}

/// Strengthen strict integer inequalities to equivalent non-strict form.
///
/// For integer arithmetic, `t < c` is equivalent to `t <= c - 1`.
/// This mirrors OpenSMT's LIA interpolator strengthening pass and keeps
/// decomposition in the non-strict domain.
pub(crate) fn strengthen_strict_lia_constraint(mut c: LinearConstraint) -> LinearConstraint {
    let is_integer_linear = *c.bound.denom() == 1 && c.coeffs.values().all(|v| *v.denom() == 1);
    if c.strict && is_integer_linear {
        c.bound -= Rational64::from_integer(1);
        c.strict = false;
    }
    c
}

/// Flip inequality direction while keeping it in canonical `<=` form.
///
/// If `a*x <= b`, then `-a*x <= -b` represents the opposite direction.
pub(super) fn flip_linear_constraint(c: &LinearConstraint) -> LinearConstraint {
    let mut flipped = c.clone();
    for coeff in flipped.coeffs.values_mut() {
        *coeff = -*coeff;
    }
    flipped.bound = -flipped.bound;
    flipped
}

pub(super) fn weighted_sum_linear_constraints(
    constraints: &[LinearConstraint],
    weights: &[Rational64],
) -> Option<(FxHashMap<String, Rational64>, Rational64, bool)> {
    if constraints.len() != weights.len() || constraints.is_empty() {
        return None;
    }

    let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut combined_bound = Rational64::from_integer(0);
    let mut combined_strict = false;

    for (constraint, weight) in constraints.iter().zip(weights.iter()) {
        if *weight == Rational64::from_integer(0) {
            continue;
        }
        combined_strict |= constraint.strict;
        combined_bound += *weight * constraint.bound;
        for (var, coeff) in &constraint.coeffs {
            // Avoid String clone when key already exists (#2956).
            if let Some(entry) = combined_coeffs.get_mut(var) {
                *entry += *weight * *coeff;
            } else {
                combined_coeffs.insert(var.clone(), *weight * *coeff);
            }
        }
    }

    combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));
    Some((combined_coeffs, combined_bound, combined_strict))
}
