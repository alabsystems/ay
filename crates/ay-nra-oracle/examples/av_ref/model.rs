// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_nra::oracle_api::OBq;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Recover the dyadic exponent by dividing out twos and counting.
pub(super) fn ref_exponent(r: &BigRational) -> Option<u32> {
    let mut denominator = r.denom().clone();
    let two = BigInt::from(2);
    let mut exponent = 0u32;
    while !denominator.is_zero() && (&denominator % &two).is_zero() {
        denominator /= &two;
        exponent = exponent.checked_add(1)?;
    }
    denominator.is_one().then_some(exponent)
}

pub(super) fn r_of(numerator: i64, exponent: u32) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::one() << exponent)
}

pub(super) fn to_r(value: &OBq) -> BigRational {
    BigRational::new(value.numerator(), BigInt::one() << value.k())
}

pub(super) fn rfloor(value: &BigRational) -> BigInt {
    value.floor().to_integer()
}

pub(super) fn rceil(value: &BigRational) -> BigInt {
    value.ceil().to_integer()
}

/// Reference `floor(r * 2^t)`.
pub(super) fn ref_floor_at(value: &BigRational, exponent: u32) -> BigInt {
    rfloor(&(value * BigRational::from_integer(BigInt::one() << exponent)))
}

pub(super) fn ref_ceil_at(value: &BigRational, exponent: u32) -> BigInt {
    rceil(&(value * BigRational::from_integer(BigInt::one() << exponent)))
}

/// Find the smallest `n` with `width / 2^n <= target` by explicit refinement.
pub(super) fn ref_step_bound(width: &BigRational, target: &BigRational, cap: u32) -> Option<u32> {
    if !width.is_positive() || !target.is_positive() {
        return None;
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut width = width.clone();
    let mut steps = 0;
    while width > *target {
        width /= &two;
        steps += 1;
        if steps > cap {
            return None;
        }
    }
    Some(steps)
}

pub(super) fn ref_poly_sign(polynomial: &[BigInt], x: &BigRational) -> i32 {
    match ref_poly_eval(polynomial, x).numer().sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    }
}

pub(super) fn ref_poly_eval(polynomial: &[BigInt], x: &BigRational) -> BigRational {
    polynomial
        .iter()
        .rev()
        .fold(BigRational::zero(), |acc, coefficient| {
            acc * x + BigRational::from_integer(coefficient.clone())
        })
}

/// Return the interior integer at scale `k` that is closest to zero.
pub(super) fn ref_candidate_at(
    lo: &BigRational,
    hi: &BigRational,
    exponent: u32,
) -> Option<BigInt> {
    let first: BigInt = ref_floor_at(lo, exponent) + 1;
    let last = ref_ceil_at(hi, exponent) - 1;
    if first > last {
        return None;
    }
    Some(if first.is_positive() {
        first
    } else if last.is_negative() {
        last
    } else {
        BigInt::zero()
    })
}

/// Reference minimal-exponent selection by brute-force scan.
pub(super) fn ref_select_small(
    lo: &BigRational,
    hi: &BigRational,
    ceiling: u32,
) -> Option<(u32, BigInt)> {
    (0..=ceiling).find_map(|exponent| {
        ref_candidate_at(lo, hi, exponent).map(|numerator| (exponent, numerator))
    })
}
