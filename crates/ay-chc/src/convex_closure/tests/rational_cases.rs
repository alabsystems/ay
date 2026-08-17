// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_rational_basic() {
    let a = Rational::new(1, 2);
    let b = Rational::new(1, 3);

    // 1/2 + 1/3 = 5/6
    let sum = a + b;
    assert_eq!(sum.num, 5);
    assert_eq!(sum.den, 6);

    // 1/2 * 1/3 = 1/6
    let prod = a * b;
    assert_eq!(prod.num, 1);
    assert_eq!(prod.den, 6);
}

/// Test that division by zero returns zero instead of panicking (#1715)
#[test]
fn test_rational_div_by_zero_no_panic() {
    let a = Rational::new(1, 2);
    let zero = Rational::zero();

    // Division by zero should return zero, not panic
    let result = a / zero;
    assert!(result.is_zero(), "Division by zero should return zero");
}

/// Test that try_normalize handles zero denominator gracefully (#1715)
#[test]
fn test_rational_normalize_zero_den_no_panic() {
    // Calling try_normalize with zero denominator should return None
    let result = Rational::try_normalize(5, 0);
    assert!(result.is_none(), "try_normalize(5, 0) should return None");

    // normalize() should return (0, 1) as fallback
    let (num, den) = Rational::normalize(5, 0);
    assert_eq!((num, den), (0, 1), "normalize fallback should be (0, 1)");
}

/// Test that i128::MIN edge cases do not panic (#1713)
#[test]
fn test_rational_i128_min_no_panic() {
    let min = Rational {
        num: i128::MIN,
        den: 1,
    };

    // abs(i128::MIN) overflows; should degrade gracefully.
    assert_eq!(min.abs(), Rational::zero());

    // -(i128::MIN) overflows; should degrade gracefully.
    assert_eq!(min.negate(), Rational::zero());

    // addition overflow should not panic.
    let sum = Rational {
        num: i128::MAX,
        den: 1,
    } + Rational { num: 1, den: 1 };
    assert_eq!(sum, Rational::zero());

    // multiplication overflow should not panic.
    let prod = Rational {
        num: i128::MAX,
        den: 1,
    } * Rational { num: 2, den: 1 };
    assert_eq!(prod, Rational::zero());

    // comparison should fall back to BigInt if i128 multiply overflows.
    let half = Rational { num: 1, den: 2 };
    assert!(
        Rational {
            num: i128::MAX,
            den: 1
        } > half
    );
}

/// Test that LCM overflow in add() degrades gracefully (#1713)
#[test]
fn test_rational_add_lcm_overflow_no_panic() {
    let a = Rational {
        num: 1,
        den: i128::MAX,
    };
    let b = Rational {
        num: 1,
        den: i128::MAX - 1,
    };
    let sum = a + b;
    assert_eq!(sum, Rational::zero());
}
