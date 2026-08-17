// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Sort;
use ay_nra::exact_rational_sqrt;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

pub(super) fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

pub(super) fn is_arith_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Real | Sort::Int)
}

/// Fit `c0 + c1·λ + c2·λ²` at `λ = 0, 1, −1` and check it at `λ = 2`.
///
/// `None` proves those four samples are not quadratic; `Some` does not prove
/// the underlying restriction is quadratic. For coefficients through degree
/// four, the discrepancy at the fourth sample is `6·a3 + 12·a4`, so every
/// cubic is rejected while quartics with `a3 = -2·a4` pass. Both call sites
/// therefore re-evaluate the resulting point's residual exactly, and the
/// whole-assertion gate remains the acceptance authority.
pub(super) fn quadratic_fit(
    at0: &BigRational,
    at1: &BigRational,
    at_m1: &BigRational,
    at2: &BigRational,
) -> Option<(BigRational, BigRational, BigRational)> {
    let two = rat(2);
    let c0 = at0.clone();
    let c1 = (at1 - at_m1) / &two;
    let c2 = (at1 + at_m1 - &c0 - &c0) / &two;
    if *at2 != &c2 * rat(4) + &c1 * &two + &c0 {
        return None;
    }
    Some((c0, c1, c2))
}

/// Exact rational roots of `c2·x² + c1·x + c0`: both roots when the
/// discriminant is the square of a rational, the single root of the linear
/// case, empty when no rational root exists.
pub(super) fn rational_roots(
    c0: &BigRational,
    c1: &BigRational,
    c2: &BigRational,
) -> Vec<BigRational> {
    if c2.is_zero() {
        if c1.is_zero() {
            return Vec::new();
        }
        return vec![-c0 / c1];
    }
    let disc = c1 * c1 - rat(4) * c2 * c0;
    if disc.is_negative() {
        return Vec::new();
    }
    let Some(root) = exact_rational_sqrt(&disc) else {
        return Vec::new();
    };
    let denom = rat(2) * c2;
    let mut out = vec![(-c1 + &root) / &denom];
    if !root.is_zero() {
        out.push((-c1 - &root) / &denom);
    }
    out
}

/// Simple rationals tried as the fixed coordinate when seeding the chord, plus
/// the model's own values: the pins in this family are built out of them
/// (`s² = (1+a²)(1+b²)` has the rational point `(b, s) = (a, 1+a²)`).
pub(super) fn seed_values(model_values: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![
        BigRational::zero(),
        BigRational::one(),
        -BigRational::one(),
        rat(2),
        rat(-2),
        BigRational::new(BigInt::one(), BigInt::from(2)),
        BigRational::new(-BigInt::one(), BigInt::from(2)),
    ];
    for value in model_values {
        for candidate in [value.clone(), -value.clone()] {
            if !out.contains(&candidate) {
                out.push(candidate);
            }
        }
    }
    out
}
