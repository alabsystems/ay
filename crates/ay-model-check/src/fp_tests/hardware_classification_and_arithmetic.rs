// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp::tests` to preserve test FQNs.

#[test]
fn classification_matches_hardware_on_every_binade() {
    for (bits, class) in [
        (POS_ZERO, FpClass::Zero),
        (NEG_ZERO, FpClass::Zero),
        (ONE, FpClass::Normal),
        (NEG_ONE, FpClass::Normal),
        (POS_INF, FpClass::Infinite),
        (NEG_INF, FpClass::Infinite),
        (NAN, FpClass::NaN),
        (NEG_NAN, FpClass::NaN),
        (SMALLEST_SUBNORMAL, FpClass::Subnormal),
        (LARGEST_SUBNORMAL, FpClass::Subnormal),
        (SMALLEST_NORMAL, FpClass::Normal),
        (MAX_FINITE, FpClass::Normal),
    ] {
        let value = f32_bits(bits);
        assert_eq!(class_of(&value), class, "bits {bits:#010x}");
        let hardware = f32::from_bits(bits);
        assert_eq!(
            class == FpClass::NaN,
            hardware.is_nan(),
            "isNaN for {bits:#010x}"
        );
        assert_eq!(
            class == FpClass::Infinite,
            hardware.is_infinite(),
            "isInfinite for {bits:#010x}"
        );
        assert_eq!(
            class == FpClass::Subnormal,
            hardware.is_subnormal(),
            "isSubnormal for {bits:#010x}"
        );
        assert_eq!(
            class == FpClass::Normal,
            hardware.is_normal(),
            "isNormal for {bits:#010x}"
        );
    }
}

#[test]
fn predicates_follow_the_class() {
    assert!(predicate("fp.isNaN", &f32_bits(NAN)).unwrap());
    assert!(!predicate("fp.isNaN", &f32_bits(ONE)).unwrap());
    assert!(predicate("fp.isZero", &f32_bits(NEG_ZERO)).unwrap());
    assert!(predicate("fp.isInfinite", &f32_bits(NEG_INF)).unwrap());
    assert!(!predicate("fp.isNormal", &f32_bits(POS_ZERO)).unwrap());
    assert!(!predicate("fp.isNormal", &f32_bits(SMALLEST_SUBNORMAL)).unwrap());
    assert!(predicate("fp.isSubnormal", &f32_bits(SMALLEST_SUBNORMAL)).unwrap());
}

/// A NaN is neither negative nor positive, but `-0` IS negative — the two rules
/// that a naive "check the sign bit" or "not positive" implementation gets
/// wrong in opposite directions.
#[test]
fn sign_predicates_treat_nan_and_negative_zero_correctly() {
    assert!(!predicate("fp.isNegative", &f32_bits(NAN)).unwrap());
    assert!(!predicate("fp.isPositive", &f32_bits(NAN)).unwrap());
    assert!(!predicate("fp.isNegative", &f32_bits(NEG_NAN)).unwrap());
    assert!(!predicate("fp.isPositive", &f32_bits(NEG_NAN)).unwrap());

    assert!(predicate("fp.isNegative", &f32_bits(NEG_ZERO)).unwrap());
    assert!(!predicate("fp.isPositive", &f32_bits(NEG_ZERO)).unwrap());
    assert!(predicate("fp.isPositive", &f32_bits(POS_ZERO)).unwrap());
    assert!(!predicate("fp.isNegative", &f32_bits(POS_ZERO)).unwrap());
}

// -- comparisons ----------------------------------------------------------

/// Comparisons agree with hardware on every pair of a representative set,
/// across all five operators. Hardware is the independent oracle here.
#[test]
// Exact `f32` equality is deliberate: it IS the oracle for `fp.eq`.
#[allow(clippy::float_cmp)]
fn comparisons_agree_with_hardware_on_every_pair() {
    let patterns = [
        POS_ZERO,
        NEG_ZERO,
        ONE,
        NEG_ONE,
        TWO,
        POS_INF,
        NEG_INF,
        NAN,
        SMALLEST_SUBNORMAL,
        NEG_SMALLEST_SUBNORMAL,
        MAX_FINITE,
        NEG_MAX_FINITE,
    ];
    for a in patterns {
        for b in patterns {
            let (x, y) = (f32::from_bits(a), f32::from_bits(b));
            let pair = [f32_bits(a), f32_bits(b)];
            for (name, expected) in [
                ("fp.eq", x == y),
                ("fp.lt", x < y),
                ("fp.leq", x <= y),
                ("fp.gt", x > y),
                ("fp.geq", x >= y),
            ] {
                assert_eq!(
                    comparison(name, &pair).unwrap(),
                    expected,
                    "{name} of {a:#010x} and {b:#010x}"
                );
            }
        }
    }
}

/// `fp.geq` is NOT the negation of `fp.lt`: NaN makes both false. A single
/// pair pins the rule that an implementation written as one negated comparison
/// would break.
#[test]
fn every_comparison_with_nan_is_false() {
    for other in [POS_ZERO, ONE, NEG_ONE, POS_INF, NEG_INF, NAN] {
        for (a, b) in [(NAN, other), (other, NAN)] {
            let pair = [f32_bits(a), f32_bits(b)];
            for name in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"] {
                assert!(
                    !comparison(name, &pair).unwrap(),
                    "{name} of {a:#010x} and {b:#010x} must be false"
                );
            }
        }
    }
    // NaN is UNORDERED, not merely unequal: the internal ordering has no answer
    // at all, which is what keeps `fp.geq` from being `not fp.lt`.
    let nan = Fp::from_value(&f32_bits(NAN)).unwrap().ext().unwrap();
    let one = Fp::from_value(&f32_bits(ONE)).unwrap().ext().unwrap();
    assert_eq!(nan, Ext::Nan);
    assert_eq!(ext_cmp(&nan, &one), None);
    assert_eq!(ext_cmp(&nan, &nan), None);
}

/// The zeros are equal under comparison and distinct under the encoding — the
/// two facts a sign-blind or a purely structural implementation confuses.
#[test]
fn the_two_zeros_compare_equal_but_stay_distinct() {
    let pair = [f32_bits(POS_ZERO), f32_bits(NEG_ZERO)];
    assert!(comparison("fp.eq", &pair).unwrap());
    assert!(comparison("fp.leq", &pair).unwrap());
    assert!(comparison("fp.geq", &pair).unwrap());
    assert!(!comparison("fp.lt", &pair).unwrap());
    assert!(!comparison("fp.gt", &pair).unwrap());
    // ... but they are different VALUES, which `fp.isNegative` and SMT-LIB's
    // structural `=` both see.
    assert!(predicate("fp.isNegative", &f32_bits(NEG_ZERO)).unwrap());
    assert!(!predicate("fp.isNegative", &f32_bits(POS_ZERO)).unwrap());
    assert!(!same_element(&f32_bits(POS_ZERO), &f32_bits(NEG_ZERO)));
}

/// SMT-LIB comparisons are n-ary over ADJACENT pairs.
#[test]
fn comparisons_are_chained_over_adjacent_pairs() {
    let rising = [
        f32_bits(NEG_ONE),
        f32_bits(POS_ZERO),
        f32_bits(ONE),
        f32_bits(TWO),
    ];
    assert!(comparison("fp.lt", &rising).unwrap());
    assert!(comparison("fp.leq", &rising).unwrap());
    assert!(!comparison("fp.gt", &rising).unwrap());

    let not_sorted = [f32_bits(NEG_ONE), f32_bits(TWO), f32_bits(ONE)];
    assert!(!comparison("fp.lt", &not_sorted).unwrap());

    // One NaN anywhere in the chain falsifies it.
    let with_nan = [f32_bits(NEG_ONE), f32_bits(NAN), f32_bits(TWO)];
    assert!(!comparison("fp.lt", &with_nan).unwrap());

    assert!(
        comparison("fp.eq", &[f32_bits(ONE)]).is_err(),
        "needs two operands"
    );
}

// -- sign operations ------------------------------------------------------

#[test]
fn abs_and_neg_do_not_round_and_apply_to_nan() {
    let bits = |name: &str, v: u32| bits_of(&sign_op(name, &f32_bits(v)).unwrap());
    assert_eq!(bits("fp.abs", NEG_ONE), ONE);
    assert_eq!(bits("fp.abs", ONE), ONE);
    assert_eq!(bits("fp.neg", ONE), NEG_ONE);
    assert_eq!(bits("fp.neg", POS_ZERO), NEG_ZERO);
    assert_eq!(bits("fp.abs", NEG_ZERO), POS_ZERO);
    assert_eq!(bits("fp.neg", POS_INF), NEG_INF);
    // NaN keeps its payload; only the sign bit moves.
    assert_eq!(bits("fp.neg", NAN), NEG_NAN);
    assert_eq!(bits("fp.abs", NEG_NAN), NAN);
}

// -- exact values and malformed input -------------------------------------

/// The exact value of a finite float, cross-checked against a reconstruction
/// from the raw IEEE fields that does not go through this module at all.
#[test]
fn exact_values_match_an_independent_field_reconstruction() {
    for bits in [
        POS_ZERO,
        NEG_ZERO,
        ONE,
        NEG_ONE,
        TWO,
        SMALLEST_SUBNORMAL,
        NEG_SMALLEST_SUBNORMAL,
        LARGEST_SUBNORMAL,
        SMALLEST_NORMAL,
        0x4048_0000, // 3.125
        MAX_FINITE,
    ] {
        let exact = exact_value(&f32_bits(bits)).expect("finite");
        let biased = (bits >> 23) & 0xff;
        let stored = bits & 0x007f_ffff;
        let expected = if biased == 0 && stored == 0 {
            BigRational::from(BigInt::from(0u8))
        } else {
            let mantissa = if biased == 0 {
                BigInt::from(stored)
            } else {
                BigInt::from(stored | 0x0080_0000)
            };
            let exponent = if biased == 0 {
                -149i64
            } else {
                i64::from(biased) - 127 - 23
            };
            let magnitude = if exponent >= 0 {
                BigRational::from(mantissa << u32::try_from(exponent).unwrap())
            } else {
                BigRational::new(
                    mantissa,
                    BigInt::from(1u8) << u32::try_from(-exponent).unwrap(),
                )
            };
            if bits >> 31 == 1 {
                -magnitude
            } else {
                magnitude
            }
        };
        assert_eq!(exact, expected, "bits {bits:#010x}");
    }
    // NaN and the infinities have no real value.
    for bits in [NAN, POS_INF, NEG_INF] {
        assert!(exact_value(&f32_bits(bits)).is_none(), "{bits:#010x}");
    }
}

/// Mixing formats is a malformed term, not something to coerce: SMT-LIB gives
/// each `(_ FloatingPoint eb sb)` its own sort, so an operand pair that does
/// not share one is refused by every binary operator.
#[test]
fn operands_of_different_formats_are_refused() {
    let single = f32_bits(ONE);
    let double = f64_bits(0x3ff0_0000_0000_0000);
    let pair = [single.clone(), double.clone()];
    assert!(arith("fp.add", RNE, &pair).is_err());
    assert!(arith("fp.mul", RNE, &pair).is_err());
    assert!(arith("fp.div", RNE, &pair).is_err());
    assert!(arith("fp.sub", RNE, &pair).is_err());
    assert!(min_max("fp.min", &pair).is_err());
    assert!(min_max("fp.max", &pair).is_err());
    assert!(rem(&pair).is_err());
    assert!(fma(RNE, &[single.clone(), single, double]).is_err());
}

/// `fp.eq` and its four siblings are refused across formats for the same
/// reason the arithmetic is.
///
/// A well-typed SMT-LIB formula cannot produce this, so the case exists only to
/// keep the gate failing CLOSED on a malformed or mis-parsed term: an answer
/// here would be a comparison of two values that have no common sort. The
/// comparison path must therefore reject a format mismatch before ordering the
/// operands, exactly as `arith`/`min_max`/`rem`/`fma` do.
#[test]
fn comparisons_of_different_formats_are_refused() {
    let single = f32_bits(ONE);
    let double = f64_bits(0x3ff0_0000_0000_0000);
    for name in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"] {
        assert!(
            compare(name, &[single.clone(), double.clone()]).is_err(),
            "{name} across formats must be refused, not answered"
        );
    }
}

/// A payload outside the format's field widths is refused rather than masked.
#[test]
fn a_malformed_payload_is_refused() {
    let bad_significand = ModelValue::FloatingPoint {
        sign: false,
        exponent: 127,
        significand: 1 << 23, // needs 24 stored bits; the format has 23
        exponent_bits: 8,
        significand_bits: 24,
    };
    assert!(Fp::from_value(&bad_significand).is_err());
    let bad_exponent = ModelValue::FloatingPoint {
        sign: false,
        exponent: 256,
        significand: 0,
        exponent_bits: 8,
        significand_bits: 24,
    };
    assert!(Fp::from_value(&bad_exponent).is_err());
    // A non-FP operand is refused too, rather than defaulted.
    assert!(predicate("fp.isNaN", &ModelValue::Bool(true)).is_err());
}

// -- arithmetic against hardware ------------------------------------------

/// Hardware `f32` add/sub/mul/div are correctly rounded under RNE, so they are
/// an independent oracle over a wide sweep — including the infinities, the
/// zeros, and the subnormal boundary, where the special-case rules live.
#[test]
fn arithmetic_matches_hardware_under_rne() {
    let patterns = [
        POS_ZERO,
        NEG_ZERO,
        ONE,
        NEG_ONE,
        TWO,
        PI_ISH,
        NEG_PI_ISH,
        POS_INF,
        NEG_INF,
        SMALLEST_SUBNORMAL,
        NEG_SMALLEST_SUBNORMAL,
        LARGEST_SUBNORMAL,
        SMALLEST_NORMAL,
        MAX_FINITE,
        NEG_MAX_FINITE,
        TINY,
    ];
    for a in patterns {
        for b in patterns {
            let (x, y) = (f32::from_bits(a), f32::from_bits(b));
            for (name, expected) in [
                ("fp.add", x + y),
                ("fp.sub", x - y),
                ("fp.mul", x * y),
                ("fp.div", x / y),
            ] {
                let got = op2(name, RNE, a, b);
                if expected.is_nan() {
                    // Which NaN encoding comes back is not determined; that it
                    // is a NaN at all is.
                    assert!(
                        f32::from_bits(got).is_nan(),
                        "{name}({a:#010x}, {b:#010x}) should be NaN, got {got:#010x}"
                    );
                } else {
                    assert_eq!(
                        got,
                        expected.to_bits(),
                        "{name}({a:#010x}, {b:#010x}) = {expected}"
                    );
                }
            }
        }
    }
}
