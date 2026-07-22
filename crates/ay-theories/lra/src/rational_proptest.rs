// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property tests: the fast `Rational` (inline i64/i128 path + pure-Rust
//! `BigRational` overflow fallback) must produce arithmetic results IDENTICAL
//! to computing directly in `num_rational::BigRational`, which is exact by
//! construction. `to_big()` is an exact injection, so
//! `op(a, b).to_big() == op(a.to_big(), b.to_big())` is a full exactness proof
//! for every operation across the small / i128-overflow / Big regimes.
//!
//! These guard the pure-Rust arithmetic that replaces the removed gmp backend
//! (#chc25-pure-rust-lra) and the allocation-free bound-comparison fast paths.

use crate::infrational::InfRational;
use crate::rational::Rational;
use crate::types::BoundType;
use num_traits::Zero;
use proptest::prelude::*;
use std::cmp::Ordering;

/// A `Rational` spanning three regimes:
///  * small: fits comfortably in i64,
///  * i64-boundary: near `i64::MAX`,
///  * Big: a product of two large i64 that exceeds i64 (and can exceed i128).
fn any_rat() -> impl Strategy<Value = Rational> {
    prop_oneof![
        // Small, arbitrary sign, modest denominator.
        (-100_000i64..100_000, 1i64..100_000).prop_map(|(n, d)| Rational::new(n, d)),
        // Full i64 range numerator, positive denominator.
        (
            any::<i64>().prop_filter("no MIN", |n| *n != i64::MIN),
            1i64..=i64::MAX
        )
            .prop_map(|(n, d)| Rational::new(n, d)),
        // Big-forcing: product of two large values overflows i64 (-> i128 or Big).
        (1_000_000_000i64..=i64::MAX, 1_000_000_000i64..=i64::MAX)
            .prop_map(|(a, b)| Rational::from(a) * Rational::from(b)),
        // Big fraction: large numerator over large denominator.
        (
            1_000_000_000i64..=i64::MAX,
            1_000_000_000i64..=i64::MAX,
            1_000_000_007i64..=i64::MAX
        )
            .prop_map(|(a, b, d)| (Rational::from(a) * Rational::from(b)) / Rational::from(d)),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// Addition is exact vs the BigRational oracle.
    #[test]
    fn prop_add_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assert_eq!((&a + &b).to_big(), a.to_big() + b.to_big());
    }

    /// Subtraction is exact.
    #[test]
    fn prop_sub_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assert_eq!((&a - &b).to_big(), a.to_big() - b.to_big());
    }

    /// Multiplication is exact.
    #[test]
    fn prop_mul_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assert_eq!((&a * &b).to_big(), a.to_big() * b.to_big());
    }

    /// Division is exact (nonzero divisor).
    #[test]
    fn prop_div_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assume!(!b.is_zero());
        prop_assert_eq!((&a / &b).to_big(), a.to_big() / b.to_big());
    }

    /// Negation is exact.
    #[test]
    fn prop_neg_matches_bigrational(a in any_rat()) {
        prop_assert_eq!((-&a).to_big(), -a.to_big());
    }

    /// Ordering agrees with the BigRational oracle in all regimes.
    #[test]
    fn prop_cmp_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assert_eq!(a.cmp(&b), a.to_big().cmp(&b.to_big()));
    }

    /// Equality agrees with the BigRational oracle.
    #[test]
    fn prop_eq_matches_bigrational(a in any_rat(), b in any_rat()) {
        prop_assert_eq!(a == b, a.to_big() == b.to_big());
    }

    /// `to_big()` round-trips exactly through `Rational::from`.
    #[test]
    fn prop_to_from_big_roundtrip(a in any_rat()) {
        let back = Rational::from(a.to_big());
        prop_assert_eq!(a.cmp(&back), Ordering::Equal);
        prop_assert!(a == back);
    }

    /// Fused `add_product` (`acc += a*b`) matches the separate-op sequence.
    #[test]
    fn prop_add_product_matches_separate(acc in any_rat(), a in any_rat(), b in any_rat()) {
        let mut acc_fused = acc.clone();
        let product = acc_fused.add_product(&a, &b);
        let product_sep = &a * &b;
        let mut acc_sep = acc.clone();
        acc_sep += &product_sep;
        prop_assert_eq!(acc_fused.to_big(), acc_sep.to_big());
        prop_assert_eq!(product.to_big(), product_sep.to_big());
    }

    /// Fused `mul_add_assign` matches the separate-op sequence.
    #[test]
    fn prop_mul_add_assign_matches_separate(acc in any_rat(), a in any_rat(), b in any_rat()) {
        let mut acc_fused = acc.clone();
        acc_fused.mul_add_assign(&a, &b);
        let mut acc_sep = acc.clone();
        acc_sep += &(&a * &b);
        prop_assert_eq!(acc_fused.to_big(), acc_sep.to_big());
    }

    /// `scale_small_i64` (when it succeeds) matches generic multiplication.
    #[test]
    fn prop_scale_small_i64_matches_mul(
        a in any_rat(),
        sn in (any::<i32>()).prop_map(i64::from),
        sd in (1i32..1_000_000).prop_map(i64::from),
    ) {
        if let Some(fast) = a.scale_small_i64(sn, sd) {
            let generic = &a * &Rational::new(sn, sd);
            prop_assert_eq!(fast.to_big(), generic.to_big());
        }
    }
}

/// InfRational bound value with an optional epsilon component.
fn any_inf() -> impl Strategy<Value = InfRational> {
    (
        any_rat(),
        prop_oneof![Just(0i64), Just(1i64), Just(-1i64), Just(3i64)],
    )
        .prop_map(|(x, e)| InfRational::new_rat(x, Rational::new(e, 1)))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// The allocation-free `lt_bound(Lower)` used by
    /// `first_current_assignment_bound_violation` (#chc25-pure-rust-lra) must
    /// equal the old `value < InfRational::new(bound, +1ε if strict else 0)`.
    #[test]
    fn prop_lt_bound_lower_matches_infrational(value in any_inf(), bound in any_rat(), strict in any::<bool>()) {
        let eps = if strict { Rational::new(1, 1) } else { Rational::zero() };
        let bound_inf = InfRational::new_rat(bound.clone(), eps);
        let fast = value.lt_bound(&bound, strict, BoundType::Lower);
        let reference = value < bound_inf;
        prop_assert_eq!(fast, reference);
    }

    /// The allocation-free `gt_bound(Upper)` must equal the old
    /// `value > InfRational::new(bound, -1ε if strict else 0)`.
    #[test]
    fn prop_gt_bound_upper_matches_infrational(value in any_inf(), bound in any_rat(), strict in any::<bool>()) {
        let eps = if strict { Rational::new(-1, 1) } else { Rational::zero() };
        let bound_inf = InfRational::new_rat(bound.clone(), eps);
        let fast = value.gt_bound(&bound, strict, BoundType::Upper);
        let reference = value > bound_inf;
        prop_assert_eq!(fast, reference);
    }
}
