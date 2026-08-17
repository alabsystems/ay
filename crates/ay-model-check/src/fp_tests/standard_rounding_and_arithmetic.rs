// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp::tests` to preserve test FQNs.

#[test]
fn exact_powers_of_two_round_to_their_known_encodings() {
    assert_eq!(to_f32(&real(1, 1), RoundingMode::Rne), 0x3f80_0000);
    assert_eq!(to_f32(&real(2, 1), RoundingMode::Rne), 0x4000_0000);
    assert_eq!(to_f32(&real(-1, 2), RoundingMode::Rne), 0xbf00_0000);
    assert_eq!(to_f32(&real(0, 1), RoundingMode::Rne), 0x0000_0000);
}

/// 0.1 is the canonical inexact case: its Float32 RNE encoding is 0x3dcccccd,
/// one ulp ABOVE the truncation 0x3dcccccc.
#[test]
fn one_tenth_rounds_to_nearest_even_not_toward_zero() {
    assert_eq!(to_f32(&real(1, 10), RoundingMode::Rne), 0x3dcc_cccd);
    assert_eq!(to_f32(&real(1, 10), RoundingMode::Rtz), 0x3dcc_cccc);
    assert_eq!(to_f32(&real(1, 10), RoundingMode::Rtn), 0x3dcc_cccc);
    assert_eq!(to_f32(&real(1, 10), RoundingMode::Rtp), 0x3dcc_cccd);
}

/// The directed modes must be asymmetric about zero: toward `+oo` truncates a
/// negative magnitude, toward `-oo` extends it.
#[test]
fn directed_rounding_is_asymmetric_about_zero() {
    assert_eq!(to_f32(&real(-1, 10), RoundingMode::Rtz), 0xbdcc_cccc);
    assert_eq!(to_f32(&real(-1, 10), RoundingMode::Rtp), 0xbdcc_cccc);
    assert_eq!(to_f32(&real(-1, 10), RoundingMode::Rtn), 0xbdcc_cccd);
}

/// A tie must go to the EVEN significand under RNE and away from zero under
/// RNA. `2^24 + 1` is exactly half an ulp above `2^24` in Float32.
#[test]
fn ties_break_to_even_under_rne_and_away_under_rna() {
    let tie_down = BigRational::from_integer(BigInt::from(16_777_217i64)); // 2^24 + 1
    assert_eq!(to_f32(&tie_down, RoundingMode::Rne), 0x4b80_0000); // 2^24, even
    assert_eq!(to_f32(&tie_down, RoundingMode::Rna), 0x4b80_0001);

    let tie_up = BigRational::from_integer(BigInt::from(16_777_219i64)); // 2^24 + 3
    assert_eq!(to_f32(&tie_up, RoundingMode::Rne), 0x4b80_0002); // even neighbour
    assert_eq!(to_f32(&tie_up, RoundingMode::Rna), 0x4b80_0002);
}

/// Overflow follows IEEE-754 §7.4: nearest goes to infinity, toward-zero stops
/// at the largest finite, and the two directed modes split by sign.
#[test]
fn overflow_depends_on_the_rounding_mode_and_sign() {
    let huge = BigRational::from_integer(BigInt::one() << 200u32);
    assert_eq!(to_f32(&huge, RoundingMode::Rne), 0x7f80_0000); // +oo
    assert_eq!(to_f32(&huge, RoundingMode::Rtz), 0x7f7f_ffff); // max finite
    assert_eq!(to_f32(&huge, RoundingMode::Rtp), 0x7f80_0000);
    assert_eq!(to_f32(&huge, RoundingMode::Rtn), 0x7f7f_ffff);
    assert_eq!(to_f32(&(-huge.clone()), RoundingMode::Rtp), 0xff7f_ffff);
    assert_eq!(to_f32(&(-huge), RoundingMode::Rtn), 0xff80_0000); // -oo
}

/// Float16 overflow, the shape `fp_to_fp_real_overflow_to_infinity` exercises:
/// 100000 exceeds Float16's max finite 65504, so RNE gives `+oo`.
#[test]
fn float16_overflow_reaches_infinity() {
    let value = BigRational::from_integer(BigInt::from(100_000i64));
    let fp = round_to_format(&value, 5, 11, RoundingMode::Rne, false).expect("in-envelope");
    assert!(matches!(
        fp.to_value(),
        ModelValue::FloatingPoint {
            exponent: 31,
            significand: 0,
            sign: false,
            ..
        }
    ));
}

/// Subnormals: `2^-149` is the smallest positive Float32 (encoding 1), and
/// half of it is an exact tie that RNE must send to zero (0 is even).
#[test]
fn subnormals_and_underflow_are_exact() {
    let min_sub = BigRational::new(BigInt::one(), BigInt::one() << 149u32);
    assert_eq!(to_f32(&min_sub, RoundingMode::Rne), 0x0000_0001);
    assert_eq!(to_f32(&(&min_sub * real(1, 2)), RoundingMode::Rne), 0);
    assert_eq!(to_f32(&(&min_sub * real(3, 4)), RoundingMode::Rne), 1);
    // The largest subnormal and the smallest normal are adjacent encodings.
    let max_sub = BigRational::new(BigInt::from((1i64 << 23) - 1), BigInt::one() << 149u32);
    assert_eq!(to_f32(&max_sub, RoundingMode::Rne), 0x007f_ffff);
    let min_normal = BigRational::new(BigInt::one(), BigInt::one() << 126u32);
    assert_eq!(to_f32(&min_normal, RoundingMode::Rne), 0x0080_0000);
}

/// Rounding up out of the top of the significand must carry into the exponent
/// rather than wrap: just below 2.0 rounds to exactly 2.0.
#[test]
fn rounding_carries_into_the_exponent() {
    let just_under_two = BigRational::new((BigInt::one() << 25u32) - 1, BigInt::one() << 24u32);
    assert_eq!(to_f32(&just_under_two, RoundingMode::Rne), 0x4000_0000);
}

// -- conversions ----------------------------------------------------------

#[test]
fn signed_and_unsigned_bitvectors_convert_differently() {
    let all_ones = ModelValue::bitvec(BigInt::from(255u8), 8);
    // Two's complement reading: -1.0.
    let signed = to_fp_rounded(false, 8, 24, RoundingMode::Rne, &all_ones).expect("converts");
    assert_eq!(bits_of(&signed), 0xbf80_0000);
    // Unsigned reading: 255.0.
    let unsigned = to_fp_rounded(true, 8, 24, RoundingMode::Rne, &all_ones).expect("converts");
    assert_eq!(bits_of(&unsigned), 0x437f_0000);
}

/// `to_fp` from one FP format to another rounds the SOURCE's exact value once.
///
/// The narrowing case is the one a two-step implementation gets wrong: the
/// Float64 nearest to `0.1` is slightly ABOVE `0.1`, and narrowing it to
/// Float32 still lands on 0x3dcccccd — the same encoding `(float)0.1` prints.
/// The special values pass through by class, not by re-encoding raw fields.
#[test]
fn to_fp_between_formats_rounds_the_source_value_once() {
    // Float32 1.0 widens to the Float64 1.0 encoding.
    let widened =
        to_fp_rounded(false, 11, 53, RoundingMode::Rne, &f32_bits(0x3f80_0000)).expect("converts");
    assert_eq!(
        bv_parts(&to_ieee_bv(&widened).expect("determined")),
        (BigInt::from(0x3ff0_0000_0000_0000u64), 64)
    );
    // Float64 0.1 narrows to Float32 0x3dcccccd.
    let narrowed = to_fp_rounded(
        false,
        8,
        24,
        RoundingMode::Rne,
        &f64_bits(0x3fb9_9999_9999_999a),
    )
    .expect("converts");
    assert_eq!(bits_of(&narrowed), 0x3dcc_cccd);
    // A zero keeps its sign, and an infinity its direction.
    let neg_zero =
        to_fp_rounded(false, 11, 53, RoundingMode::Rne, &f32_bits(0x8000_0000)).expect("converts");
    assert_eq!(
        bv_parts(&to_ieee_bv(&neg_zero).expect("determined")),
        (BigInt::from(0x8000_0000_0000_0000u64), 64)
    );
    let neg_inf = to_fp_rounded(
        false,
        8,
        24,
        RoundingMode::Rne,
        &f64_bits(0xfff0_0000_0000_0000),
    )
    .expect("converts");
    assert_eq!(bits_of(&neg_inf), 0xff80_0000);
    // NaN converts to NaN, whichever way the format goes.
    let nan = to_fp_rounded(
        false,
        8,
        24,
        RoundingMode::Rne,
        &f64_bits(0x7ff8_0000_0000_0000),
    )
    .expect("converts");
    assert_eq!(classify("fp.isNaN", &nan).unwrap(), Some(true));
}

#[test]
fn to_sbv_rounds_and_declines_outside_the_range() {
    let two_and_a_half = f32_bits(0x4020_0000);
    let rounded = to_bv(false, 8, RoundingMode::Rne, &two_and_a_half).expect("in range");
    assert!(
        matches!(rounded, ModelValue::BitVec { width: 8, ref value } if *value == BigInt::from(2u8))
    );
    // RTP of 2.5 is 3.
    let up = to_bv(false, 8, RoundingMode::Rtp, &two_and_a_half).expect("in range");
    assert!(
        matches!(up, ModelValue::BitVec { width: 8, ref value } if *value == BigInt::from(3u8))
    );
    // NaN and out-of-range are SMT-LIB-unspecified and must decline.
    assert!(to_bv(false, 8, RoundingMode::Rne, &f32_bits(0x7fc0_0000)).is_err());
    assert!(to_bv(false, 8, RoundingMode::Rne, &f32_bits(0x4380_0000)).is_err()); // 256.0
    assert!(to_bv(true, 8, RoundingMode::Rne, &f32_bits(0xbf80_0000)).is_err());
    // -1.0
}

// -- predicates -----------------------------------------------------------

#[test]
fn classification_matches_the_ieee_field_definitions() {
    let cases: [(&str, u32, bool); 10] = [
        ("fp.isNaN", 0x7fc0_0000, true),
        ("fp.isNaN", 0x7f80_0000, false),
        ("fp.isInfinite", 0x7f80_0000, true),
        ("fp.isZero", 0x8000_0000, true),    // -0
        ("fp.isNormal", 0x0000_0001, false), // subnormal
        ("fp.isSubnormal", 0x0000_0001, true),
        ("fp.isNegative", 0x8000_0000, true),
        // NaN is neither negative nor positive, even with the sign bit set.
        ("fp.isNegative", 0xffc0_0000, false),
        ("fp.isPositive", 0x7fc0_0000, false),
        ("fp.isPositive", 0x3f80_0000, true),
    ];
    for (name, bits, want) in cases {
        assert_eq!(
            classify(name, &f32_bits(bits)).expect("classifies"),
            Some(want),
            "{name} on {bits:#010x}"
        );
    }
}

#[test]
fn comparisons_treat_nan_as_unordered_and_zeros_as_equal() {
    let nan = f32_bits(0x7fc0_0000);
    let zero = f32_bits(0x0000_0000);
    let neg_zero = f32_bits(0x8000_0000);
    let one = f32_bits(0x3f80_0000);

    // NaN is unordered with everything, including itself.
    for op in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"] {
        assert_eq!(
            compare(op, &[nan.clone(), nan.clone()]).unwrap(),
            Some(false)
        );
        assert_eq!(
            compare(op, &[nan.clone(), one.clone()]).unwrap(),
            Some(false)
        );
    }
    // `fp.eq` identifies the two zeros; structural `=` does not.
    assert_eq!(
        compare("fp.eq", &[zero.clone(), neg_zero.clone()]).unwrap(),
        Some(true)
    );
    assert_eq!(
        compare("fp.leq", &[neg_zero, zero.clone()]).unwrap(),
        Some(true)
    );
    assert_eq!(compare("fp.lt", &[zero, one.clone()]).unwrap(), Some(true));
    // Chainable: `(fp.lt 0 1 +oo)`.
    assert_eq!(
        compare("fp.lt", &[f32_bits(0), one, f32_bits(0x7f80_0000)]).unwrap(),
        Some(true)
    );
}

#[test]
fn abs_and_neg_are_sign_bit_rewrites() {
    let neg_one = f32_bits(0xbf80_0000);
    assert_eq!(
        bits_of(&unary_sign("fp.abs", &neg_one).unwrap().unwrap()),
        0x3f80_0000
    );
    assert_eq!(
        bits_of(&unary_sign("fp.neg", &neg_one).unwrap().unwrap()),
        0x3f80_0000
    );
    assert_eq!(
        bits_of(&unary_sign("fp.neg", &f32_bits(0)).unwrap().unwrap()),
        0x8000_0000
    );
}

// -- arithmetic -----------------------------------------------------------

#[test]
fn arithmetic_rounds_the_exact_result_once() {
    let one = f32_bits(0x3f80_0000);
    let three = f32_bits(0x4040_0000);
    // 1/3 in Float32 is 0x3eaaaaab.
    let third = arith("fp.div", RoundingMode::Rne, &[one.clone(), three.clone()])
        .unwrap()
        .unwrap();
    assert_eq!(bits_of(&third), 0x3eaa_aaab);
    // RTZ truncates instead.
    let third_rtz = arith("fp.div", RoundingMode::Rtz, &[one.clone(), three.clone()])
        .unwrap()
        .unwrap();
    assert_eq!(bits_of(&third_rtz), 0x3eaa_aaaa);

    // 2^24 + 1 is not representable: the sum ties to even.
    let big = f32_bits(0x4b80_0000); // 2^24
    let sum = arith("fp.add", RoundingMode::Rne, &[big.clone(), one.clone()])
        .unwrap()
        .unwrap();
    assert_eq!(bits_of(&sum), 0x4b80_0000);

    let product = arith("fp.mul", RoundingMode::Rne, &[three.clone(), three])
        .unwrap()
        .unwrap();
    assert_eq!(bits_of(&product), 0x4110_0000); // 9.0
}

#[test]
fn special_values_follow_the_ieee_rules() {
    let inf = f32_bits(0x7f80_0000);
    let neg_inf = f32_bits(0xff80_0000);
    let zero = f32_bits(0x0000_0000);
    let one = f32_bits(0x3f80_0000);

    let is_nan = |v: &ModelValue| classify("fp.isNaN", v).unwrap() == Some(true);

    // oo + (-oo), 0 * oo, oo / oo and 0 / 0 are all NaN.
    assert!(is_nan(
        &arith("fp.add", RoundingMode::Rne, &[inf.clone(), neg_inf.clone()])
            .unwrap()
            .unwrap()
    ));
    assert!(is_nan(
        &arith("fp.mul", RoundingMode::Rne, &[zero.clone(), inf.clone()])
            .unwrap()
            .unwrap()
    ));
    assert!(is_nan(
        &arith("fp.div", RoundingMode::Rne, &[inf.clone(), inf.clone()])
            .unwrap()
            .unwrap()
    ));
    assert!(is_nan(
        &arith("fp.div", RoundingMode::Rne, &[zero.clone(), zero.clone()])
            .unwrap()
            .unwrap()
    ));
    // Finite / 0 is a signed infinity.
    assert_eq!(
        bits_of(
            &arith("fp.div", RoundingMode::Rne, &[one.clone(), zero.clone()])
                .unwrap()
                .unwrap()
        ),
        0x7f80_0000
    );
    // Finite / oo is a signed zero.
    assert_eq!(
        bits_of(
            &arith("fp.div", RoundingMode::Rne, &[one, neg_inf])
                .unwrap()
                .unwrap()
        ),
        0x8000_0000
    );
}

/// An exactly-zero SUM is `+0` in every mode but `RTN`, where it is `-0`;
/// like-signed zeros keep their own sign. IEEE-754 §6.3.
#[test]
fn zero_sums_take_their_sign_from_the_rounding_mode() {
    let zero = f32_bits(0x0000_0000);
    let neg_zero = f32_bits(0x8000_0000);
    let one = f32_bits(0x3f80_0000);
    let neg_one = f32_bits(0xbf80_0000);

    let sum = |rm, a: &ModelValue, b: &ModelValue| {
        bits_of(
            &arith("fp.add", rm, &[a.clone(), b.clone()])
                .unwrap()
                .unwrap(),
        )
    };
    assert_eq!(sum(RoundingMode::Rne, &one, &neg_one), 0x0000_0000);
    assert_eq!(sum(RoundingMode::Rtn, &one, &neg_one), 0x8000_0000);
    assert_eq!(sum(RoundingMode::Rne, &neg_zero, &neg_zero), 0x8000_0000);
    assert_eq!(sum(RoundingMode::Rne, &zero, &neg_zero), 0x0000_0000);
}

/// SMT-LIB leaves `fp.min(+0, -0)` under-specified, so the gate must DECLINE
/// rather than pick one — guessing could confirm a model the solver refutes.
#[test]
fn min_max_declines_the_underspecified_zero_case() {
    let zero = f32_bits(0x0000_0000);
    let neg_zero = f32_bits(0x8000_0000);
    let one = f32_bits(0x3f80_0000);
    let nan = f32_bits(0x7fc0_0000);

    assert!(min_max("fp.min", &[zero.clone(), neg_zero]).is_err());
    // NaN is ignored when the other operand is a number.
    assert_eq!(
        bits_of(&min_max("fp.max", &[nan, one.clone()]).unwrap().unwrap()),
        0x3f80_0000
    );
    assert_eq!(
        bits_of(&min_max("fp.min", &[zero, one]).unwrap().unwrap()),
        0x0000_0000
    );
}

/// `fp.sqrt` is correctly rounded even where the true root is irrational.
///
/// `sqrt(2)` scaled to Float32's significand is `11863283.19`, so it rounds
/// DOWN: the correctly-rounded result 0x3fb504f3 (what a `float` hex dump of
/// `sqrtf(2)` prints) coincides with the truncation, and only `RTP` differs.
#[test]
fn sqrt_is_correctly_rounded_on_irrational_roots() {
    let two = f32_bits(0x4000_0000);
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rne, &two).unwrap()),
        0x3fb5_04f3
    );
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rtz, &two).unwrap()),
        0x3fb5_04f3
    );
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rtn, &two).unwrap()),
        0x3fb5_04f3
    );
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rtp, &two).unwrap()),
        0x3fb5_04f4
    );
    // sqrt(3) = 0x3fddb3d7 in Float32.
    let three = f32_bits(0x4040_0000);
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rne, &three).unwrap()),
        0x3fdd_b3d7
    );
}

/// Perfect squares must come back EXACTLY, with no rounding drift.
#[test]
fn sqrt_of_perfect_squares_is_exact() {
    for (input, root) in [
        (0x3f80_0000u32, 0x3f80_0000u32), // 1 -> 1
        (0x4110_0000, 0x4040_0000),       // 9 -> 3
        (0x4280_0000, 0x4100_0000),       // 64 -> 8
        (0x3e80_0000, 0x3f00_0000),       // 0.25 -> 0.5
    ] {
        assert_eq!(
            bits_of(&sqrt(RoundingMode::Rne, &f32_bits(input)).unwrap()),
            root,
            "sqrt of {input:#010x}"
        );
    }
}

/// IEEE-754 §6.3: `sqrt(-0)` is `-0` — the sign survives. A negative operand
/// (other than zero) is invalid and gives NaN, and `sqrt(+oo)` is `+oo`.
#[test]
fn sqrt_special_values_follow_ieee() {
    let is_nan = |v: &ModelValue| classify("fp.isNaN", v).unwrap() == Some(true);
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rne, &f32_bits(0x8000_0000)).unwrap()),
        0x8000_0000
    );
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rne, &f32_bits(0x0000_0000)).unwrap()),
        0x0000_0000
    );
    assert!(is_nan(
        &sqrt(RoundingMode::Rne, &f32_bits(0xbf80_0000)).unwrap()
    )); // sqrt(-1)
    assert!(is_nan(
        &sqrt(RoundingMode::Rne, &f32_bits(0xff80_0000)).unwrap()
    )); // sqrt(-oo)
    assert_eq!(
        bits_of(&sqrt(RoundingMode::Rne, &f32_bits(0x7f80_0000)).unwrap()),
        0x7f80_0000
    );
}

/// The IEEE remainder rounds the quotient to NEAREST (ties even), so it can be
/// negative even for positive operands — which is what separates it from
/// `fmod`. `rem(5, 3)` is `-1`, not `2`.
#[test]
fn rem_uses_nearest_quotient_not_truncation() {
    let five = f32_bits(0x40a0_0000);
    let three = f32_bits(0x4040_0000);
    assert_eq!(bits_of(&rem(&[five, three.clone()]).unwrap()), 0xbf80_0000); // -1
    let seven = f32_bits(0x40e0_0000);
    assert_eq!(bits_of(&rem(&[seven, three]).unwrap()), 0x3f80_0000); // +1
                                                                      //
                                                                      // A tie in the quotient goes to the even one: `rem(3, 2)` has `3/2 = 1.5`,
                                                                      // which ties to 2, so the remainder is -1.
    let three_val = f32_bits(0x4040_0000);
    let two = f32_bits(0x4000_0000);
    assert_eq!(bits_of(&rem(&[three_val, two]).unwrap()), 0xbf80_0000);
}

/// A format the value type cannot hold must decline, not truncate.
#[test]
fn out_of_envelope_formats_decline() {
    let float128 = ModelValue::FloatingPoint {
        sign: false,
        exponent: 0,
        significand: 0,
        exponent_bits: 15,
        significand_bits: 113,
    };
    assert!(Fp::from_value(&float128).is_err());
    assert!(round_to_format(&real(1, 1), 15, 113, RoundingMode::Rne, false).is_err());
}
