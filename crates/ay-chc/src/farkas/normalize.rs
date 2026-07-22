// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint normalization: LCM scaling and GCD reduction.

use num_rational::Rational64;

use super::linear::{checked_r64_mul, LinearConstraint};

/// Scale a constraint's coefficients and bound by LCM to clear fractions.
/// Uses all-or-nothing approach: if any multiplication overflows, the
/// constraint is left unscaled to prevent inconsistent partial scaling.
fn scale_constraint_by_lcm(c: &mut LinearConstraint, lcm_val: i64) {
    let scale = Rational64::from_integer(lcm_val);
    let mut scaled_coeffs: Vec<(String, Rational64)> = Vec::new();
    let mut overflow = false;
    for (var, coeff) in c.coeffs.iter() {
        match checked_r64_mul(*coeff, scale) {
            Some(v) => scaled_coeffs.push((var.clone(), v)),
            None => {
                overflow = true;
                break;
            }
        }
    }
    let scaled_bound = if !overflow {
        checked_r64_mul(c.bound, scale)
    } else {
        None
    };
    if let (false, Some(sb)) = (overflow, scaled_bound) {
        for (var, val) in scaled_coeffs {
            c.coeffs.insert(var, val);
        }
        c.bound = sb;
    }
}

/// Divide a constraint's coefficients and bound by a common GCD.
/// Uses all-or-nothing checked arithmetic so failed normalization degrades
/// to the original constraint instead of panicking on large denominators.
fn divide_constraint_by_gcd(c: &mut LinearConstraint, gcd: i64) {
    let scale = Rational64::new(1, gcd);
    let mut scaled_coeffs: Vec<(String, Rational64)> = Vec::new();
    let mut overflow = false;
    for (var, coeff) in c.coeffs.iter() {
        match checked_r64_mul(*coeff, scale) {
            Some(v) => scaled_coeffs.push((var.clone(), v)),
            None => {
                overflow = true;
                break;
            }
        }
    }
    let scaled_bound = if !overflow {
        checked_r64_mul(c.bound, scale)
    } else {
        None
    };
    if let (false, Some(sb)) = (overflow, scaled_bound) {
        for (var, val) in scaled_coeffs {
            c.coeffs.insert(var, val);
        }
        c.bound = sb;
    }
}

/// Normalize a linear constraint by dividing all coefficients and
/// the bound by their GCD, producing smaller integer coefficients.
pub(super) fn normalize_constraint(mut c: LinearConstraint) -> LinearConstraint {
    use num_traits::Zero;

    // Collect all denominators for LCM computation
    let mut denoms: Vec<i64> = Vec::new();
    let mut has_nonzero = false;

    for &coeff in c.coeffs.values() {
        if !coeff.is_zero() {
            denoms.push(*coeff.denom());
            has_nonzero = true;
        }
    }
    if !c.bound.is_zero() {
        denoms.push(*c.bound.denom());
        has_nonzero = true;
    }

    if !has_nonzero {
        return c;
    }

    // Find LCM of denominators to clear fractions (using i128 to avoid overflow)
    let mut lcm_128 = 1i128;
    for &d in &denoms {
        let d128 = i128::from(d);
        lcm_128 = lcm_128 / num_integer::gcd(lcm_128, d128) * d128;
    }
    let lcm_val = i64::try_from(lcm_128).unwrap_or(i64::MAX);

    if lcm_val != 1 {
        scale_constraint_by_lcm(&mut c, lcm_val);
    }

    // Find GCD of all integer coefficients
    let mut g = 0i64;
    for &coeff in c.coeffs.values() {
        let n = coeff.numer().saturating_abs();
        g = num_integer::gcd(g, n);
    }
    let bound_abs = c.bound.numer().saturating_abs();
    if bound_abs > 0 {
        g = num_integer::gcd(g, bound_abs);
    }

    if g > 1 {
        divide_constraint_by_gcd(&mut c, g);
    }

    c
}
