// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// ceil_rational / floor_rational edge case tests (#1854)
// ========================================================================

/// Test ceil_rational for zero.
#[test]
fn test_ceil_rational_zero() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let zero = BigRational::from_integer(BigInt::from(0));
    assert_eq!(LiaSolver::ceil_rational(&zero), BigInt::from(0));
}

/// Test ceil_rational for positive values.
#[test]
fn test_ceil_rational_positive() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // 3/2 = 1.5 -> ceil = 2
    let three_halves = BigRational::new(BigInt::from(3), BigInt::from(2));
    assert_eq!(LiaSolver::ceil_rational(&three_halves), BigInt::from(2));

    // 7/4 = 1.75 -> ceil = 2
    let seven_fourths = BigRational::new(BigInt::from(7), BigInt::from(4));
    assert_eq!(LiaSolver::ceil_rational(&seven_fourths), BigInt::from(2));

    // 5/1 = 5 (exact integer) -> ceil = 5
    let five = BigRational::from_integer(BigInt::from(5));
    assert_eq!(LiaSolver::ceil_rational(&five), BigInt::from(5));

    // 999999999/1000000000 = 0.999... -> ceil = 1
    let almost_one = BigRational::new(BigInt::from(999999999i64), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::ceil_rational(&almost_one), BigInt::from(1));

    // 1/1000000000 = tiny positive -> ceil = 1
    let tiny = BigRational::new(BigInt::from(1), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::ceil_rational(&tiny), BigInt::from(1));
}

/// Test ceil_rational for negative values.
#[test]
fn test_ceil_rational_negative() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // -3/2 = -1.5 -> ceil = -1
    let neg_three_halves = BigRational::new(BigInt::from(-3), BigInt::from(2));
    assert_eq!(
        LiaSolver::ceil_rational(&neg_three_halves),
        BigInt::from(-1)
    );

    // -7/4 = -1.75 -> ceil = -1
    let neg_seven_fourths = BigRational::new(BigInt::from(-7), BigInt::from(4));
    assert_eq!(
        LiaSolver::ceil_rational(&neg_seven_fourths),
        BigInt::from(-1)
    );

    // -5/1 = -5 (exact integer) -> ceil = -5
    let neg_five = BigRational::from_integer(BigInt::from(-5));
    assert_eq!(LiaSolver::ceil_rational(&neg_five), BigInt::from(-5));

    // -1/1000000000 = tiny negative -> ceil = 0
    let tiny_neg = BigRational::new(BigInt::from(-1), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::ceil_rational(&tiny_neg), BigInt::from(0));
}

/// Test ceil_rational for exact integers (should return unchanged).
#[test]
fn test_ceil_rational_exact_integers() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // 6/2 = 3 (should simplify and return 3)
    let six_halves = BigRational::new(BigInt::from(6), BigInt::from(2));
    assert_eq!(LiaSolver::ceil_rational(&six_halves), BigInt::from(3));

    // -6/2 = -3 (should simplify and return -3)
    let neg_six_halves = BigRational::new(BigInt::from(-6), BigInt::from(2));
    assert_eq!(LiaSolver::ceil_rational(&neg_six_halves), BigInt::from(-3));

    // 100/25 = 4
    let hundred_over_25 = BigRational::new(BigInt::from(100), BigInt::from(25));
    assert_eq!(LiaSolver::ceil_rational(&hundred_over_25), BigInt::from(4));
}

/// Test floor_rational for zero.
#[test]
fn test_floor_rational_zero() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let zero = BigRational::from_integer(BigInt::from(0));
    assert_eq!(LiaSolver::floor_rational(&zero), BigInt::from(0));
}

/// Test floor_rational for positive values.
#[test]
fn test_floor_rational_positive() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // 3/2 = 1.5 -> floor = 1
    let three_halves = BigRational::new(BigInt::from(3), BigInt::from(2));
    assert_eq!(LiaSolver::floor_rational(&three_halves), BigInt::from(1));

    // 7/4 = 1.75 -> floor = 1
    let seven_fourths = BigRational::new(BigInt::from(7), BigInt::from(4));
    assert_eq!(LiaSolver::floor_rational(&seven_fourths), BigInt::from(1));

    // 5/1 = 5 (exact integer) -> floor = 5
    let five = BigRational::from_integer(BigInt::from(5));
    assert_eq!(LiaSolver::floor_rational(&five), BigInt::from(5));

    // 999999999/1000000000 = 0.999... -> floor = 0
    let almost_one = BigRational::new(BigInt::from(999999999i64), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::floor_rational(&almost_one), BigInt::from(0));

    // 1/1000000000 = tiny positive -> floor = 0
    let tiny = BigRational::new(BigInt::from(1), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::floor_rational(&tiny), BigInt::from(0));
}

/// Test floor_rational for negative values.
#[test]
fn test_floor_rational_negative() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // -3/2 = -1.5 -> floor = -2
    let neg_three_halves = BigRational::new(BigInt::from(-3), BigInt::from(2));
    assert_eq!(
        LiaSolver::floor_rational(&neg_three_halves),
        BigInt::from(-2)
    );

    // -7/4 = -1.75 -> floor = -2
    let neg_seven_fourths = BigRational::new(BigInt::from(-7), BigInt::from(4));
    assert_eq!(
        LiaSolver::floor_rational(&neg_seven_fourths),
        BigInt::from(-2)
    );

    // -5/1 = -5 (exact integer) -> floor = -5
    let neg_five = BigRational::from_integer(BigInt::from(-5));
    assert_eq!(LiaSolver::floor_rational(&neg_five), BigInt::from(-5));

    // -1/1000000000 = tiny negative -> floor = -1
    let tiny_neg = BigRational::new(BigInt::from(-1), BigInt::from(1000000000i64));
    assert_eq!(LiaSolver::floor_rational(&tiny_neg), BigInt::from(-1));
}

/// Test floor_rational for exact integers (should return unchanged).
#[test]
fn test_floor_rational_exact_integers() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // 6/2 = 3 (should simplify and return 3)
    let six_halves = BigRational::new(BigInt::from(6), BigInt::from(2));
    assert_eq!(LiaSolver::floor_rational(&six_halves), BigInt::from(3));

    // -6/2 = -3 (should simplify and return -3)
    let neg_six_halves = BigRational::new(BigInt::from(-6), BigInt::from(2));
    assert_eq!(LiaSolver::floor_rational(&neg_six_halves), BigInt::from(-3));

    // 100/25 = 4
    let hundred_over_25 = BigRational::new(BigInt::from(100), BigInt::from(25));
    assert_eq!(LiaSolver::floor_rational(&hundred_over_25), BigInt::from(4));
}

/// Test that ceil and floor maintain the property: floor(x) <= x <= ceil(x).
#[test]
fn test_ceil_floor_property() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    let test_values = vec![
        BigRational::from_integer(BigInt::from(0)),
        BigRational::from_integer(BigInt::from(5)),
        BigRational::from_integer(BigInt::from(-5)),
        BigRational::new(BigInt::from(3), BigInt::from(2)),
        BigRational::new(BigInt::from(-3), BigInt::from(2)),
        BigRational::new(BigInt::from(7), BigInt::from(4)),
        BigRational::new(BigInt::from(-7), BigInt::from(4)),
        BigRational::new(BigInt::from(1), BigInt::from(1000)),
        BigRational::new(BigInt::from(-1), BigInt::from(1000)),
    ];

    for val in test_values {
        let floor_val = LiaSolver::floor_rational(&val);
        let ceil_val = LiaSolver::ceil_rational(&val);

        // floor(x) <= x
        assert!(
            BigRational::from_integer(floor_val.clone()) <= val,
            "floor({val}) = {floor_val} should be <= {val}"
        );

        // x <= ceil(x)
        assert!(
            val <= BigRational::from_integer(ceil_val.clone()),
            "{val} should be <= ceil({val}) = {ceil_val}"
        );

        // floor(x) <= ceil(x)
        assert!(
            floor_val <= ceil_val,
            "floor({val}) = {floor_val} should be <= ceil({val}) = {ceil_val}"
        );

        // For integers: floor(x) == ceil(x) == x
        if val.is_integer() {
            assert_eq!(
                floor_val, ceil_val,
                "For integer {val}, floor and ceil should be equal"
            );
            assert_eq!(
                floor_val,
                val.to_integer(),
                "For integer {val}, floor should equal the value"
            );
        } else {
            // For non-integers: floor(x) < ceil(x) (differ by exactly 1)
            assert_eq!(
                ceil_val.clone() - floor_val.clone(),
                BigInt::from(1),
                "For non-integer {val}, ceil - floor should be 1"
            );
        }
    }
}
