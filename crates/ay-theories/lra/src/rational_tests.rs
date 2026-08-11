// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::rational::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

#[test]
fn test_zero_one() {
    assert!(Rational::zero().is_zero());
    assert!(!Rational::one().is_zero());
    assert!(Rational::one().is_one());
    assert!(!Rational::zero().is_one());
}

#[test]
fn test_small_arithmetic() {
    let a = Rational::new(1, 3);
    let b = Rational::new(1, 6);
    let sum = &a + &b;
    assert_eq!(sum, Rational::new(1, 2));
    assert!(sum.is_small());

    let prod = &a * &b;
    assert_eq!(prod, Rational::new(1, 18));
    assert!(prod.is_small());

    let diff = &a - &b;
    assert_eq!(diff, Rational::new(1, 6));
    assert!(diff.is_small());
}

#[test]
fn test_comparison() {
    let a = Rational::new(1, 3);
    let b = Rational::new(1, 2);
    assert!(a < b);
    assert!(b > a);
    assert_eq!(a, Rational::new(2, 6));
}

#[test]
fn test_negation() {
    let a = Rational::new(3, 4);
    let neg = -a.clone();
    assert_eq!(neg, Rational::new(-3, 4));
    assert_eq!(a + neg, Rational::zero());
}

#[test]
fn test_division() {
    let a = Rational::new(2, 3);
    let b = Rational::new(4, 5);
    let quot = a / b;
    assert_eq!(quot, Rational::new(5, 6));
}

#[test]
fn test_from_bigint() {
    let n = BigInt::from(42);
    let r = Rational::from(n);
    assert_eq!(r, Rational::Small(42, 1));
    assert!(r.is_small());
}

#[test]
fn test_from_bigrational() {
    let br = BigRational::new(BigInt::from(7), BigInt::from(3));
    let borrowed = Rational::from(&br);
    assert_eq!(borrowed, Rational::new(7, 3));
    assert!(borrowed.is_small());

    let r = Rational::from(br);
    assert_eq!(r, Rational::new(7, 3));
    assert!(r.is_small());

    let large = BigRational::from_integer(BigInt::from(i64::MAX) + BigInt::one());
    let borrowed_large = Rational::from(&large);
    assert!(!borrowed_large.is_small());
    assert_eq!(borrowed_large.to_big(), large);
}

#[test]
fn test_overflow_to_big() {
    let big = Rational::Small(i64::MAX, 1);
    let two = Rational::Small(2, 1);
    let result = big * two;
    assert!(matches!(result, Rational::Big(_)));
    let expected = BigRational::from(BigInt::from(i64::MAX)) * BigRational::from(BigInt::from(2));
    assert_eq!(result.to_big(), expected);
}

#[test]
fn test_is_integer() {
    assert!(Rational::new(5, 1).is_integer());
    assert!(!Rational::new(5, 3).is_integer());
    assert!(Rational::new(0, 1).is_integer());
}

#[test]
fn test_floor_ceil() {
    let r = Rational::new(7, 3); // 2.333...
    assert_eq!(r.floor(), BigInt::from(2));
    assert_eq!(r.ceil(), BigInt::from(3));

    let r = Rational::new(-7, 3); // -2.333...
    assert_eq!(r.floor(), BigInt::from(-3));
    assert_eq!(r.ceil(), BigInt::from(-2));

    let r = Rational::new(6, 3); // exactly 2
    assert_eq!(r.floor(), BigInt::from(2));
    assert_eq!(r.ceil(), BigInt::from(2));
}

#[test]
fn test_signed_traits() {
    let pos = Rational::new(3, 4);
    let neg = Rational::new(-3, 4);
    assert!(pos.is_positive());
    assert!(!pos.is_negative());
    assert!(neg.is_negative());
    assert!(!neg.is_positive());
    assert_eq!(pos.abs(), Rational::new(3, 4));
    assert_eq!(neg.abs(), Rational::new(3, 4));
}

#[test]
fn test_negative_denominator_normalization() {
    let r = Rational::new(3, -4);
    assert_eq!(r, Rational::new(-3, 4));
    match r {
        Rational::Small(n, d) => {
            assert_eq!(n, -3);
            assert_eq!(d, 4);
        }
        _ => panic!("expected Small"),
    }
}

#[test]
fn test_gcd_reduction() {
    let r = Rational::new(6, 4);
    assert_eq!(r, Rational::new(3, 2));
    match r {
        Rational::Small(n, d) => {
            assert_eq!(n, 3);
            assert_eq!(d, 2);
        }
        _ => panic!("expected Small"),
    }
}

#[test]
fn test_recip() {
    let r = Rational::new(3, 4);
    assert_eq!(r.recip(), Rational::new(4, 3));
    let neg = Rational::new(-3, 4);
    assert_eq!(neg.recip(), Rational::new(-4, 3));
}

#[test]
fn test_cmp_big_small_vs_bigrational() {
    use std::cmp::Ordering;
    // 1/3 < 1/2
    let small = Rational::new(1, 3);
    let big = BigRational::new(BigInt::from(1), BigInt::from(2));
    assert_eq!(small.cmp_big(&big), Ordering::Less);

    // 1/2 == 1/2
    let half = Rational::new(1, 2);
    assert_eq!(half.cmp_big(&big), Ordering::Equal);

    // 2/3 > 1/2
    let two_thirds = Rational::new(2, 3);
    assert_eq!(two_thirds.cmp_big(&big), Ordering::Greater);

    // Negative: -1/3 > -1/2
    let neg_third = Rational::new(-1, 3);
    let neg_half = BigRational::new(BigInt::from(-1), BigInt::from(2));
    assert_eq!(neg_third.cmp_big(&neg_half), Ordering::Greater);

    // Zero vs positive
    assert_eq!(Rational::zero().cmp_big(&big), Ordering::Less);

    // Big Rational variant
    let large = Rational::from_big(BigRational::new(BigInt::from(i64::MAX), BigInt::from(1)));
    let large_big = BigRational::new(BigInt::from(i64::MAX), BigInt::from(1));
    assert_eq!(large.cmp_big(&large_big), Ordering::Equal);
}

#[test]
fn test_try_as_i64_small() {
    let r = Rational::new(7, 3);
    assert_eq!(r.try_as_i64(), Some((7, 3)));
}

#[test]
fn test_try_as_i64_zero() {
    assert_eq!(Rational::zero().try_as_i64(), Some((0, 1)));
}

#[test]
fn test_try_as_i64_negative() {
    let r = Rational::new(-5, 2);
    assert_eq!(r.try_as_i64(), Some((-5, 2)));
}

#[test]
fn test_try_as_i64_big_returns_none() {
    let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
    assert!(matches!(big, Rational::Big(_)));
    assert_eq!(big.try_as_i64(), None);
}

#[test]
fn test_try_as_i128_small() {
    let r = Rational::new(42, 13);
    assert_eq!(r.try_as_i128(), Some((42, 13)));
}

#[test]
fn test_try_as_i128_widens_small() {
    let r = Rational::new(i64::MAX, 1);
    let (n, d) = r.try_as_i128().expect("should widen to i128");
    assert_eq!(n, i128::from(i64::MAX));
    assert_eq!(d, 1);
}

#[test]
fn test_try_as_i128_big_fits() {
    // 2 * i64::MAX fits in i128 but not i64
    let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
    assert!(matches!(big, Rational::Big(_)));
    let result = big.try_as_i128();
    assert!(result.is_some(), "2*i64::MAX should fit in i128");
    let (n, d) = result.expect("fits");
    assert_eq!(n, 2 * i128::from(i64::MAX));
    assert_eq!(d, 1);
}

#[test]
fn test_is_integer_i64() {
    assert!(Rational::from(5i64).is_integer_i64());
    assert!(!Rational::new(1, 3).is_integer_i64());
    let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
    assert!(!big.is_integer_i64());
}

#[test]
fn test_from_i128() {
    assert_eq!(Rational::from_i128(42), Rational::Small(42, 1));
    let v = i128::from(i64::MAX) * 3;
    let r = Rational::from_i128(v);
    assert!(matches!(r, Rational::Big(_)));
    assert_eq!(r.try_as_i128().expect("fits"), (v, 1));
}

#[test]
fn test_floor_int_ceil_int_match_big_paths() {
    // (#C4) i64 fast-path floor/ceil must agree with the BigInt versions
    // on every Small value class: integers, positive/negative proper
    // fractions, and values straddling zero.
    let cases: [(i64, i64); 12] = [
        (5, 1),
        (-5, 1),
        (0, 1),
        (11, 2),
        (-11, 2),
        (1, 3),
        (-1, 3),
        (7, 7),
        (-7, 7),
        (i64::MAX, 2),
        (i64::MIN + 1, 2),
        (i64::MIN, 1),
    ];
    for (n, d) in cases {
        let r = Rational::new(n, d);
        let fi = r.floor_int().expect("Small floor_int");
        let ci = r.ceil_int().expect("Small ceil_int");
        assert_eq!(BigInt::from(fi), r.floor(), "floor mismatch for {n}/{d}");
        assert_eq!(BigInt::from(ci), r.ceil(), "ceil mismatch for {n}/{d}");
    }
}

#[test]
fn test_floor_int_ceil_int_big_returns_none() {
    let big = Rational::Small(i64::MAX, 1) * Rational::Small(2, 1);
    assert!(matches!(big, Rational::Big(_)));
    assert_eq!(big.floor_int(), None);
    assert_eq!(big.ceil_int(), None);
    // The Big fallbacks still produce the exact values.
    assert_eq!(big.floor(), BigInt::from(i64::MAX) * BigInt::from(2));
    assert_eq!(big.ceil(), BigInt::from(i64::MAX) * BigInt::from(2));
}
