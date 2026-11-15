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

// --- Gate-profile regressions (2026-09-09, seal trust-28aee49d) -------------
//
// The ny_propagate verification gate's busy thread was `BigUint::gcd` under
// `Ratio<BigInt>::reduce`, reached through `Rational::to_big()` on `Small`
// values (a gcd on a pair already coprime by invariant) and through mixed
// `Small`/`Big` comparisons that materialised both sides. These tests pin the
// VALUE-preserving fixes: same numbers, no gcd, no allocation.

fn big_pow2(exp: u32) -> BigInt {
    BigInt::from(1u8) << exp
}

#[test]
fn to_big_of_small_is_the_reduced_ratio_without_normalizing() {
    // Every Small pair is coprime with a positive denominator; `new_raw` must
    // therefore give the byte-identical Ratio that `new` gave.
    let cases = [
        (0i64, 1i64),
        (1, 1),
        (-1, 1),
        (3, 7),
        (-3, 7),
        (i64::MAX, 1),
        (i64::MIN, 1),
        (i64::MIN, i64::MAX),
        (7, i64::MAX),
        (1, 2),
    ];
    for (n, d) in cases {
        let r = Rational::new(n, d);
        let via_new_raw = r.to_big();
        let via_new = BigRational::new(BigInt::from(n), BigInt::from(d));
        assert_eq!(via_new_raw, via_new, "value for {n}/{d}");
        assert_eq!(via_new_raw.numer(), via_new.numer(), "numer for {n}/{d}");
        assert_eq!(via_new_raw.denom(), via_new.denom(), "denom for {n}/{d}");
        assert_eq!(r.to_rug(), via_new, "to_rug for {n}/{d}");
        assert_eq!(
            r.abs_bigrational(),
            num_traits::Signed::abs(&via_new),
            "abs for {n}/{d}"
        );
    }
    // `Small(0, d)` with d != 1 is tolerated by `is_zero`; it must map to the
    // canonical zero, not to a non-reduced `0/d`.
    let odd_zero = Rational::Small(0, 5);
    assert_eq!(odd_zero.to_big(), BigRational::zero());
    assert!(odd_zero.to_big().denom().is_one());
    assert_eq!(odd_zero.abs_bigrational(), BigRational::zero());
}

#[test]
fn mixed_small_big_eq_and_ord_match_bigrational_semantics() {
    let big_pos = Rational::from(big_pow2(70)); // Big
    let big_neg = Rational::from(-big_pow2(70)); // Big
    let big_frac = Rational::new_big(big_pow2(70) + BigInt::from(1), big_pow2(70)); // Big, > 1
    assert!(!big_pos.is_small() && !big_neg.is_small() && !big_frac.is_small());
    let smalls = [
        Rational::zero(),
        Rational::one(),
        Rational::new(-1, 1),
        Rational::new(1, 3),
        Rational::from(i64::MAX),
        Rational::from(i64::MIN),
        Rational::new(i64::MIN, i64::MAX),
    ];
    for s in &smalls {
        for b in [&big_pos, &big_neg, &big_frac] {
            let expect = s.to_big().cmp(&b.to_big());
            assert_eq!(s.cmp(b), expect, "Small {s:?} vs Big {b:?}");
            assert_eq!(b.cmp(s), expect.reverse(), "Big {b:?} vs Small {s:?}");
            assert_eq!(s == b, expect.is_eq(), "eq {s:?} == {b:?}");
            assert_eq!(b == s, expect.is_eq(), "eq {b:?} == {s:?}");
            assert_eq!(s.partial_cmp(b), Some(expect));
        }
    }
    // Big vs Big: -2^70 < (2^70+1)/2^70 (just above 1) < 2^70.
    assert!(big_neg < big_pos);
    assert!(big_frac < big_pos);
    assert!(big_neg < big_frac);
    assert!(Rational::one() < big_frac);
    assert_eq!(big_pos, Rational::from(big_pow2(70)));
    assert_ne!(big_pos, big_frac);
    assert_eq!(big_pos.cmp(&big_frac), std::cmp::Ordering::Greater);
    assert_eq!(big_frac.cmp(&big_pos), std::cmp::Ordering::Less);
    assert_eq!(big_pos.cmp(&big_pos.clone()), std::cmp::Ordering::Equal);
}

#[test]
fn big_backing_holding_an_i64_value_compares_equal_to_small() {
    // Direct `Big` construction of an inline-representable value (the shape a
    // stuck accumulator has). Eq/Ord/Hash must all agree with the Small form.
    use std::hash::{Hash, Hasher};
    let stuck = Rational::Big(Box::new(BigRational::from_integer(BigInt::from(5))));
    let small = Rational::from(5i64);
    assert!(!stuck.is_small());
    assert_eq!(stuck, small);
    assert_eq!(small, stuck);
    assert_eq!(stuck.cmp(&small), std::cmp::Ordering::Equal);
    assert_eq!(small.cmp(&stuck), std::cmp::Ordering::Equal);
    assert!(stuck < Rational::from(6i64));
    assert!(Rational::from(4i64) < stuck);
    let hash = |r: &Rational| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        r.hash(&mut h);
        h.finish()
    };
    assert_eq!(hash(&stuck), hash(&small), "Eq/Hash agreement");
}

#[test]
fn add_product_and_mul_add_assign_demote_a_big_accumulator_that_fits_again() {
    // acc = 2^70 (Big); acc += (5 - 2^70) * 1  ==>  5, which fits i64.
    let start = Rational::from(big_pow2(70));
    let delta = Rational::from(BigInt::from(5) - big_pow2(70));
    assert!(!start.is_small() && !delta.is_small());

    let mut acc = start.clone();
    let product = acc.add_product(&delta, &Rational::one());
    assert_eq!(acc, Rational::from(5i64));
    assert!(
        acc.is_small(),
        "add_product must shrink a Big accumulator: {acc:?}"
    );
    assert_eq!(product, delta);

    let mut acc2 = start.clone();
    acc2.mul_add_assign(&delta, &Rational::one());
    assert_eq!(acc2, Rational::from(5i64));
    assert!(
        acc2.is_small(),
        "mul_add_assign must shrink a Big accumulator: {acc2:?}"
    );

    // Reference: the shrinking `+=` path gives the same value and shape.
    let mut reference = start;
    reference += &(&delta * &Rational::one());
    assert_eq!(reference, acc2);
    assert_eq!(reference.is_small(), acc2.is_small());

    // Anti-vacuity: a Big result that does NOT fit stays Big and exact.
    let mut still_big = Rational::from(big_pow2(70));
    still_big.mul_add_assign(&Rational::from(big_pow2(70)), &Rational::one());
    assert!(!still_big.is_small());
    assert_eq!(still_big, Rational::from(big_pow2(71)));
}

#[test]
fn owned_sub_matches_by_ref_sub_for_big_and_mixed_operands() {
    let a = Rational::from(big_pow2(70));
    let b = Rational::new_big(BigInt::from(1), big_pow2(70));
    let pairs = [
        (a.clone(), b.clone()),
        (b.clone(), a.clone()),
        (a.clone(), Rational::from(3i64)),
        (Rational::from(3i64), a.clone()),
        (a.clone(), a.clone()),
        (Rational::from(i64::MIN), Rational::from(1i64)),
    ];
    for (x, y) in pairs {
        let by_ref = &x - &y;
        let owned = x.clone() - y.clone();
        assert_eq!(owned, by_ref, "{x:?} - {y:?}");
        assert_eq!(
            owned.is_small(),
            by_ref.is_small(),
            "shape for {x:?} - {y:?}"
        );
        assert_eq!(
            owned.to_big(),
            x.to_big() - y.to_big(),
            "value for {x:?} - {y:?}"
        );
    }
    // A Big - Big that lands back inline must come back Small.
    let diff = a.clone() - Rational::from(big_pow2(70) - BigInt::from(9));
    assert_eq!(diff, Rational::from(9i64));
    assert!(diff.is_small());
}
