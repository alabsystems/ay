// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp::tests` to preserve test FQNs.

/// The sign of an exactly zero sum is the rule a rational cannot carry:
/// `x + (-x)` is `+0` in every mode but toward negative infinity.
#[test]
fn the_sign_of_an_exactly_zero_sum_follows_the_mode() {
    for rm in ALL_MODES {
        let cancelled = op2("fp.add", rm, ONE, NEG_ONE);
        let expected = if rm == RoundingMode::Rtn {
            NEG_ZERO
        } else {
            POS_ZERO
        };
        assert_eq!(cancelled, expected, "1 + (-1) under {rm:?}");
        // Two zeros of the same sign keep it, whatever the mode.
        assert_eq!(op2("fp.add", rm, NEG_ZERO, NEG_ZERO), NEG_ZERO, "{rm:?}");
        assert_eq!(op2("fp.add", rm, POS_ZERO, POS_ZERO), POS_ZERO, "{rm:?}");
        // Opposite zeros fall under the cancellation rule.
        assert_eq!(op2("fp.add", rm, POS_ZERO, NEG_ZERO), expected, "{rm:?}");
        // `x - x` is `x + (-x)`, so it follows the same rule.
        assert_eq!(op2("fp.sub", rm, ONE, ONE), expected, "{rm:?}");
        // A product's zero sign is the XOR of the operand signs, in EVERY mode.
        assert_eq!(op2("fp.mul", rm, NEG_ONE, POS_ZERO), NEG_ZERO, "{rm:?}");
        assert_eq!(op2("fp.mul", rm, NEG_ONE, NEG_ZERO), POS_ZERO, "{rm:?}");
        assert_eq!(op2("fp.div", rm, NEG_ZERO, TWO), NEG_ZERO, "{rm:?}");
    }
}

/// The undefined combinations are NaN, not an infinity or a zero.
#[test]
fn invalid_operations_produce_nan() {
    let is_nan = |v: u32| f32::from_bits(v).is_nan();
    assert!(is_nan(op2("fp.add", RNE, POS_INF, NEG_INF)));
    assert!(is_nan(op2("fp.sub", RNE, POS_INF, POS_INF)));
    assert!(is_nan(op2("fp.mul", RNE, POS_INF, POS_ZERO)));
    assert!(is_nan(op2("fp.mul", RNE, NEG_ZERO, NEG_INF)));
    assert!(is_nan(op2("fp.div", RNE, POS_INF, NEG_INF)));
    assert!(is_nan(op2("fp.div", RNE, POS_ZERO, NEG_ZERO)));
    // ... but division BY zero is an infinity with the xor sign, not NaN.
    assert_eq!(op2("fp.div", RNE, ONE, POS_ZERO), POS_INF);
    assert_eq!(op2("fp.div", RNE, ONE, NEG_ZERO), NEG_INF);
    assert_eq!(op2("fp.div", RNE, NEG_ONE, NEG_ZERO), POS_INF);
}

/// The directed modes must bracket the exact result, and the nearest modes must
/// land on one of those two — checked against exact rational arithmetic rather
/// than against another implementation.
#[test]
fn every_mode_rounds_the_exact_result_correctly() {
    let cases = [
        (ONE, 0x4049_0fdb_u32), // 1 + pi
        (0x3f40_0000, 0x3eaa_aaab),
        (TWO, TINY),
    ];
    for (a, b) in cases {
        let exact_sum = exact_value(&f32_bits(a)).unwrap() + exact_value(&f32_bits(b)).unwrap();
        let down = op2("fp.add", RoundingMode::Rtn, a, b);
        let up = op2("fp.add", RoundingMode::Rtp, a, b);
        let down_v = exact_value(&f32_bits(down)).unwrap();
        let up_v = exact_value(&f32_bits(up)).unwrap();
        assert!(
            down_v <= exact_sum,
            "toward -inf must not exceed the exact sum"
        );
        assert!(up_v >= exact_sum, "toward +inf must not fall short");
        for rm in [RoundingMode::Rne, RoundingMode::Rna] {
            let near = op2("fp.add", rm, a, b);
            assert!(
                near == down || near == up,
                "a nearest mode picks a neighbour of the exact sum"
            );
        }
        // Every one of these sums is positive, so toward-zero is toward -inf.
        assert_eq!(op2("fp.add", RoundingMode::Rtz, a, b), down, "positive sum");
    }
}

// -- fused multiply-add ---------------------------------------------------

/// `fp.fma` rounds ONCE. The low bits of the exact product must survive into
/// the sum, which they cannot do if the product is rounded on its own first.
#[test]
fn fma_rounds_only_at_the_end() {
    // a = 1 + 2^-12, so a*a = 1 + 2^-11 + 2^-24 exactly. Rounding that product
    // to f32 lands on a tie at 1 + 2^-11 (ties to even discards the 2^-24), so
    // multiply-then-add gives 2^-11. The fused result keeps the 2^-24 term, and
    // 2^-11 + 2^-24 IS representable, so the two answers differ.
    let a = 0x3f80_0800u32;
    let product_then_add = {
        let p = op2("fp.mul", RNE, a, a);
        op2("fp.add", RNE, p, NEG_ONE)
    };
    let fused = bits_of(
        &rounded_op(
            "fp.fma",
            RNE,
            &[f32_bits(a), f32_bits(a), f32_bits(NEG_ONE)],
        )
        .unwrap(),
    );
    assert_ne!(
        fused, product_then_add,
        "a fused multiply-add must differ from multiply-then-add here"
    );

    let two_pow = |k: u32| BigRational::new(BigInt::one(), BigInt::one() << k);
    assert_eq!(
        exact_value(&f32_bits(fused)).unwrap(),
        two_pow(11) + two_pow(24),
        "the fused result is the exact value, unrounded"
    );
    assert_eq!(
        exact_value(&f32_bits(product_then_add)).unwrap(),
        two_pow(11),
        "multiply-then-add lost the low term"
    );
}

#[test]
fn fma_special_cases() {
    let fma_bits = |x: u32, y: u32, z: u32| {
        bits_of(&rounded_op("fp.fma", RNE, &[f32_bits(x), f32_bits(y), f32_bits(z)]).unwrap())
    };
    assert!(
        f32::from_bits(fma_bits(POS_INF, POS_ZERO, ONE)).is_nan(),
        "inf * 0"
    );
    assert!(
        f32::from_bits(fma_bits(POS_INF, ONE, NEG_INF)).is_nan(),
        "an infinite product plus the opposite infinity"
    );
    assert_eq!(fma_bits(POS_INF, ONE, POS_INF), POS_INF);
    assert_eq!(fma_bits(ONE, ONE, POS_INF), POS_INF);
    assert_eq!(fma_bits(TWO, TWO, ONE), FIVE, "2*2 + 1 = 5");
    // Hardware agrees on ordinary values.
    for (x, y, z) in [(ONE, TWO, ONE), (PI_ISH, TWO, NEG_ONE), (NEG_ONE, TWO, TWO)] {
        let expected = f32::from_bits(x).mul_add(f32::from_bits(y), f32::from_bits(z));
        assert_eq!(
            fma_bits(x, y, z),
            expected.to_bits(),
            "fma({x:#x},{y:#x},{z:#x})"
        );
    }
}

// -- remainder, roundToIntegral, min/max, sqrt ----------------------------

/// `fp.rem` is the IEEE remainder, not `fmod`: it can be negative for positive
/// operands, because `n` is the NEAREST integer quotient.
#[test]
fn remainder_is_the_ieee_remainder_not_fmod() {
    let rem_bits =
        |x: u32, y: u32| bits_of(&unrounded_op("fp.rem", &[f32_bits(x), f32_bits(y)]).unwrap());
    // 5 rem 3: nearest quotient is 2, so 5 - 6 = -1. `fmod` would give 2.
    assert_eq!(rem_bits(FIVE, THREE), NEG_ONE, "5 rem 3 = -1");
    // 5 rem 2: quotient 2 (ties to even from 2.5), so 5 - 4 = 1.
    assert_eq!(rem_bits(FIVE, TWO), ONE, "5 rem 2 = 1");
    assert_eq!(
        rem_bits(NINE, TWO),
        ONE,
        "9 rem 2: nearest quotient 4, so 9 - 8 = 1"
    );
    // Special cases.
    assert!(f32::from_bits(rem_bits(POS_INF, TWO)).is_nan());
    assert!(f32::from_bits(rem_bits(ONE, POS_ZERO)).is_nan());
    assert_eq!(rem_bits(ONE, POS_INF), ONE);
    assert_eq!(
        rem_bits(NEG_ZERO, TWO),
        NEG_ZERO,
        "a zero keeps the dividend's sign"
    );
    // An exactly zero remainder keeps the dividend's sign too.
    assert_eq!(rem_bits(NEG_FOUR, TWO), NEG_ZERO, "-4 rem 2 = -0");
}

#[test]
fn round_to_integral_follows_the_mode_and_keeps_zero_signs() {
    let rti = |rm, v: u32| bits_of(&rounded_op("fp.roundToIntegral", rm, &[f32_bits(v)]).unwrap());

    assert_eq!(rti(RNE, HALF), POS_ZERO, "0.5 ties to even = 0");
    assert_eq!(rti(RoundingMode::Rna, HALF), ONE);
    assert_eq!(rti(RNE, ONE_AND_A_HALF), TWO, "1.5 ties to even = 2");
    assert_eq!(rti(RoundingMode::Rtp, HALF), ONE);
    assert_eq!(rti(RoundingMode::Rtz, ONE_AND_A_HALF), ONE);

    // A value rounding to zero KEEPS its sign — this is the case a
    // `BigRational` round trip erases.
    assert_eq!(rti(RoundingMode::Rtz, NEG_HALF), NEG_ZERO);
    assert_eq!(rti(RNE, NEG_HALF), NEG_ZERO);
    assert_eq!(rti(RoundingMode::Rtp, NEG_HALF), NEG_ZERO);
    assert_eq!(rti(RoundingMode::Rtn, NEG_HALF), NEG_ONE);
    assert_eq!(rti(RNE, NEG_ZERO), NEG_ZERO);
    assert_eq!(rti(RNE, POS_INF), POS_INF);
    assert!(f32::from_bits(rti(RNE, NAN)).is_nan());
    // Large values are already integral.
    assert_eq!(rti(RNE, MAX_FINITE), MAX_FINITE);
}

#[test]
fn min_and_max_prefer_a_number_over_nan_and_refuse_the_unspecified_case() {
    let mm = |name: &str, a: u32, b: u32| {
        unrounded_op(name, &[f32_bits(a), f32_bits(b)]).map(|v| bits_of(&v))
    };
    assert_eq!(mm("fp.min", ONE, TWO).unwrap(), ONE);
    assert_eq!(mm("fp.max", ONE, TWO).unwrap(), TWO);
    assert_eq!(mm("fp.min", NEG_ONE, ONE).unwrap(), NEG_ONE);
    assert_eq!(
        mm("fp.min", NAN, TWO).unwrap(),
        TWO,
        "NaN loses to a number"
    );
    assert_eq!(mm("fp.max", ONE, NAN).unwrap(), ONE);
    assert!(f32::from_bits(mm("fp.min", NAN, NAN).unwrap()).is_nan());
    assert_eq!(mm("fp.min", NEG_INF, POS_INF).unwrap(), NEG_INF);
    assert_eq!(mm("fp.max", NEG_INF, POS_INF).unwrap(), POS_INF);
    // SMT-LIB does not say which zero comes back, so neither does the gate.
    assert!(mm("fp.min", POS_ZERO, NEG_ZERO).is_err());
    assert!(mm("fp.max", NEG_ZERO, POS_ZERO).is_err());
    // Same-sign zeros are fine.
    assert_eq!(mm("fp.min", POS_ZERO, POS_ZERO).unwrap(), POS_ZERO);
}

/// `fp.sqrt` against hardware, which IEEE-754 also requires to be correctly
/// rounded — including the subnormal input, where the exponent handling in a
/// hand-written integer square root is easiest to get wrong.
#[test]
fn sqrt_special_cases_and_values() {
    let sqrt_bits = |v: u32| bits_of(&rounded_op("fp.sqrt", RNE, &[f32_bits(v)]).unwrap());
    assert_eq!(sqrt_bits(FOUR), TWO, "sqrt(4) = 2");
    assert_eq!(sqrt_bits(ONE), ONE);
    assert_eq!(sqrt_bits(POS_ZERO), POS_ZERO);
    assert_eq!(sqrt_bits(NEG_ZERO), NEG_ZERO, "sqrt(-0) is -0, not NaN");
    assert_eq!(sqrt_bits(POS_INF), POS_INF);
    assert!(
        f32::from_bits(sqrt_bits(NEG_ONE)).is_nan(),
        "sqrt of a negative"
    );
    assert!(f32::from_bits(sqrt_bits(NEG_INF)).is_nan());
    assert!(f32::from_bits(sqrt_bits(NAN)).is_nan());
    for v in [TWO, THREE, PI_ISH, SMALLEST_SUBNORMAL, MAX_FINITE] {
        assert_eq!(
            sqrt_bits(v),
            f32::from_bits(v).sqrt().to_bits(),
            "sqrt({v:#010x})"
        );
    }
}

/// `fp.sqrt` checked against its DEFINITION rather than against another
/// implementation: the result must be the unique format neighbour whose square
/// brackets the operand, and squaring is exact in `BigRational`.
#[test]
fn sqrt_is_the_correctly_rounded_root_by_definition() {
    for v in [
        TWO,
        THREE,
        PI_ISH,
        FIVE,
        TINY,
        SMALLEST_SUBNORMAL,
        MAX_FINITE,
    ] {
        let operand = exact_value(&f32_bits(v)).unwrap();
        let down = bits_of(&rounded_op("fp.sqrt", RoundingMode::Rtn, &[f32_bits(v)]).unwrap());
        let up = bits_of(&rounded_op("fp.sqrt", RoundingMode::Rtp, &[f32_bits(v)]).unwrap());
        let down_v = exact_value(&f32_bits(down)).unwrap();
        let up_v = exact_value(&f32_bits(up)).unwrap();
        assert!(
            &down_v * &down_v <= operand,
            "toward -inf must not overshoot the root of {v:#010x}"
        );
        assert!(
            &up_v * &up_v >= operand,
            "toward +inf must not undershoot the root of {v:#010x}"
        );
        // The two directed results are the same encoding (an exact root) or
        // adjacent ones — nothing may sit strictly between them.
        assert!(
            up == down || up == down + 1,
            "the directed roots of {v:#010x} must be adjacent, got {down:#010x}/{up:#010x}"
        );
        for rm in [RoundingMode::Rne, RoundingMode::Rna, RoundingMode::Rtz] {
            let near = bits_of(&rounded_op("fp.sqrt", rm, &[f32_bits(v)]).unwrap());
            assert!(near == down || near == up, "{rm:?} root of {v:#010x}");
        }
    }
}

// -- bitvector conversions ------------------------------------------------

#[test]
fn to_ieee_bv_packs_the_fields_and_refuses_nan() {
    for bits in [
        POS_ZERO, NEG_ZERO, ONE, NEG_ONE, POS_INF, NEG_INF, MAX_FINITE,
    ] {
        assert_eq!(
            bv_parts(&to_ieee_bv(&f32_bits(bits)).unwrap()),
            (BigInt::from(bits), 32),
            "bits {bits:#010x}"
        );
    }
    // NaN has many encodings and SMT-LIB does not say which one comes back.
    assert!(to_ieee_bv(&f32_bits(NAN)).is_err());
}

#[test]
fn to_bv_rounds_and_refuses_what_does_not_fit() {
    let ubv = |rm, v: u32, w| to_bv_named("fp.to_ubv", rm, w, &f32_bits(v));
    let sbv = |rm, v: u32, w| to_bv_named("fp.to_sbv", rm, w, &f32_bits(v));
    let as_int = |r: Result<ModelValue, String>| bv_parts(&r.unwrap()).0;
    assert_eq!(as_int(ubv(RNE, PI_ISH, 8)), BigInt::from(3), "3.14 -> 3");
    assert_eq!(
        as_int(ubv(RoundingMode::Rtp, PI_ISH, 8)),
        BigInt::from(4),
        "3.14 toward +inf -> 4"
    );
    assert_eq!(
        as_int(sbv(RNE, NEG_ONE, 8)),
        BigInt::from(255),
        "-1 as 8-bit two's complement"
    );
    assert_eq!(
        as_int(sbv(RoundingMode::Rtz, NEG_PI_ISH, 8)),
        BigInt::from(253),
        "-3"
    );
    // Unspecified cases are refused.
    assert!(ubv(RNE, NEG_ONE, 8).is_err(), "negative into unsigned");
    assert!(ubv(RNE, NAN, 8).is_err());
    assert!(ubv(RNE, POS_INF, 8).is_err());
    assert!(ubv(RNE, 0x4400_0000, 4).is_err(), "512 does not fit 4 bits");
    assert!(
        sbv(RNE, 0x437f_0000, 8).is_err(),
        "255 does not fit a signed byte"
    );
    assert_eq!(
        as_int(sbv(RNE, 0x42fe_0000, 8)),
        BigInt::from(127),
        "127 does"
    );
}

/// `fp.to_ieee_bv` of NaN is unspecified among NaN ENCODINGS — not among all
/// bit patterns. The gate adopts the model's choice there, so the check on what
/// it adopted is the only thing standing between it and a `+zero` pattern.
#[test]
fn a_nan_encoding_is_recognised_and_a_non_nan_one_is_not() {
    let nan = f32_bits(NAN);
    assert!(to_ieee_bv_unspecified(&nan));
    for bits in [POS_ZERO, ONE, POS_INF, NEG_INF, MAX_FINITE] {
        assert!(
            !to_ieee_bv_unspecified(&f32_bits(bits)),
            "{bits:#010x} is not NaN"
        );
    }

    let bv = |v: u32| ModelValue::bitvec(BigInt::from(v), 32);
    // Any all-ones exponent with a NONZERO fraction, either sign.
    for pattern in [NAN, NEG_NAN, 0x7f80_0001, 0xffff_ffff] {
        assert!(is_nan_encoding(&bv(pattern), &nan), "{pattern:#010x}");
    }
    // An infinity has a ZERO fraction, so it is not a NaN encoding.
    assert!(!is_nan_encoding(&bv(POS_INF), &nan));
    assert!(!is_nan_encoding(&bv(NEG_INF), &nan));
    assert!(
        !is_nan_encoding(&bv(POS_ZERO), &nan),
        "the case the adoption path exists to reject"
    );
    assert!(!is_nan_encoding(&bv(ONE), &nan));
    // Wrong width, or not a bitvector at all.
    assert!(!is_nan_encoding(
        &ModelValue::bitvec(BigInt::from(NEG_NAN), 16),
        &nan
    ));
    assert!(!is_nan_encoding(&f32_bits(NAN), &nan));
}
