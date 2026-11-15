// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-arithmetic differential checks for the affine elimination identities.

use super::*;

fn admitted(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_AFFINE_COEFF_BITS && value.denom().bits() <= MAX_AFFINE_COEFF_BITS
}

/// Evaluate the mathematical expression directly, including the existing
/// admission policy on the intermediate product before cancellation.
fn reference_scaled(
    value: &BigRational,
    factor: &BigRational,
    pivot: &BigRational,
) -> (Option<BigRational>, Option<BigRational>) {
    if ![value, factor, pivot].into_iter().all(admitted) {
        return (None, None);
    }
    let product = factor * pivot;
    if !admitted(&product) {
        return (None, None);
    }
    let sum = value + &product;
    let difference = value - &product;
    (
        admitted(&sum).then_some(sum),
        admitted(&difference).then_some(difference),
    )
}

fn check_arithmetic(values: &[BigRational]) {
    for value in values {
        for factor in values {
            let quotient = if factor.is_zero() || !admitted(value) || !admitted(factor) {
                None
            } else {
                let result = value / factor;
                admitted(&result).then_some(result)
            };
            assert_eq!(LiaSolver::bounded_rational_div(value, factor), quotient);
            for pivot in values {
                let (sum, difference) = reference_scaled(value, factor, pivot);
                assert_eq!(
                    LiaSolver::bounded_rational_scaled_add(value, factor, pivot),
                    sum,
                    "{value} + {factor} * {pivot}"
                );
                assert_eq!(
                    LiaSolver::bounded_rational_scaled_sub(value, factor, pivot),
                    difference,
                    "{value} - {factor} * {pivot}"
                );
            }
        }
    }
}

#[test]
fn affine_arithmetic_matches_exact_small_rationals() {
    let values: Vec<_> = (-3..=3)
        .flat_map(|numerator| {
            (1..=3).map(move |denominator| {
                BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
            })
        })
        .collect();
    check_arithmetic(&values);
}

#[test]
fn affine_arithmetic_preserves_coefficient_boundaries() {
    let largest = (BigInt::one() << MAX_AFFINE_COEFF_BITS) - BigInt::one();
    let oversized = BigInt::one() << MAX_AFFINE_COEFF_BITS;
    let values = vec![
        BigRational::zero(),
        BigRational::one(),
        -BigRational::one(),
        BigRational::from_integer(largest.clone()),
        BigRational::from_integer(-largest.clone()),
        BigRational::new(BigInt::one(), largest),
        BigRational::from_integer(oversized.clone()),
        BigRational::new(BigInt::one(), oversized),
    ];
    check_arithmetic(&values);
}

#[test]
fn affine_arithmetic_refuses_oversized_product_before_cancellation() {
    let value = BigRational::from_integer(BigInt::one() << (MAX_AFFINE_COEFF_BITS - 1));
    let two = BigRational::from_integer(BigInt::from(2));
    // The difference would fit, but the product is outside the admission bound.
    assert!(admitted(&(&value - &value * &two)));
    assert_eq!(
        LiaSolver::bounded_rational_scaled_sub(&value, &value, &two),
        None
    );
    assert_eq!(
        LiaSolver::bounded_rational_scaled_add(&(-&value), &value, &two),
        None
    );
}

#[test]
fn affine_arithmetic_identities_still_spend_elimination_fuel() {
    let rows = vec![
        vec![BigRational::one(), BigRational::zero()],
        vec![BigRational::zero(), BigRational::one()],
    ];
    let mut never = || false;
    let mut insufficient = 2;
    assert!(LiaSolver::rational_rref(rows.clone(), &mut insufficient, &mut never).is_none());
    let mut exact = 3;
    assert_eq!(
        LiaSolver::rational_rref(rows.clone(), &mut exact, &mut never),
        Some(vec![(0, rows[0].clone()), (1, rows[1].clone())])
    );
    assert_eq!(exact, 0);
    let mut cancelled = || true;
    let mut untouched = 3;
    assert!(LiaSolver::rational_rref(rows, &mut untouched, &mut cancelled).is_none());
    assert_eq!(untouched, 3);
}
