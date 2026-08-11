// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exactness tests for the gate's floating-point fragment.
//!
//! Two INDEPENDENT suites, kept side by side on purpose because they pin the
//! same module against two different oracles:
//!
//!  * the **standard suite** — every expected value is an independently known
//!    IEEE-754 bit pattern (the ones a `float`/`double` hex dump prints), read
//!    off the standard rather than out of this module or out of the solver;
//!  * the **hardware cross-check suite** — dense sweeps whose oracle is the
//!    host's own `f32` unit, which IEEE-754 requires to be correctly rounded
//!    for `add`/`sub`/`mul`/`div`/`sqrt`, plus checks of the directed rounding
//!    modes against exact rational arithmetic and of `fp.sqrt` against its
//!    DEFINITION.
//!
//! That is the point: the gate confirms models, so its arithmetic has to be
//! pinned against the standard and against an oracle that shares none of its
//! code — never against the code under test. The host float appears ONLY here,
//! as that oracle; no host float participates in `fp.rs` itself.
//!
//! Everything below reaches the module through the thin shim block marked
//! "hardware cross-check suite": that is the single place where the tests bind
//! to `fp.rs`'s call shapes.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::fp::ext_cmp;
use crate::fp::{
    arith, check_ieee_nan_encoding, classify, compare, fma, min_max, rem, round_to_format,
    round_to_integral, same_element, sqrt, to_bv, to_fp_rounded, to_ieee_bv, unary_sign, Ext, Fp,
    RoundingMode, UNDERSPECIFIED,
};
use crate::ModelValue;

// ===========================================================================
// shared helpers
// ===========================================================================

/// Float32 from its 32-bit IEEE encoding.
fn f32_bits(bits: u32) -> ModelValue {
    ModelValue::FloatingPoint {
        sign: bits >> 31 == 1,
        exponent: u64::from((bits >> 23) & 0xff),
        significand: u64::from(bits & 0x007f_ffff),
        exponent_bits: 8,
        significand_bits: 24,
    }
}

/// Float64 from its 64-bit IEEE encoding.
fn f64_bits(bits: u64) -> ModelValue {
    ModelValue::FloatingPoint {
        sign: bits >> 63 == 1,
        exponent: (bits >> 52) & 0x7ff,
        significand: bits & 0x000f_ffff_ffff_ffff,
        exponent_bits: 11,
        significand_bits: 53,
    }
}

/// The 32-bit IEEE encoding of a Float32 gate value.
///
/// `ModelValue` has no `PartialEq` — equality on model values is semantic and
/// fallible — so results are compared through their encodings, which is also
/// the only comparison that distinguishes `+0` from `-0`.
fn bits_of(value: &ModelValue) -> u32 {
    let ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits,
        significand_bits,
    } = value
    else {
        panic!("expected a floating-point value, got {value:?}");
    };
    assert_eq!(
        (*exponent_bits, *significand_bits),
        (8, 24),
        "not a Float32"
    );
    (u32::from(*sign) << 31)
        | ((u32::try_from(*exponent).unwrap()) << 23)
        | u32::try_from(*significand).unwrap()
}

/// The `(value, width)` of a bitvector gate value.
fn bv_parts(value: &ModelValue) -> (BigInt, u32) {
    let ModelValue::BitVec { width, value } = value else {
        panic!("expected a bitvector value, got {value:?}");
    };
    (value.clone(), *width)
}

fn real(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn to_f32(x: &BigRational, rm: RoundingMode) -> u32 {
    bits_of(
        &round_to_format(x, 8, 24, rm, false)
            .expect("in-envelope")
            .to_value(),
    )
}

// ===========================================================================
// standard suite: expectations read off IEEE-754 / SMT-LIB
// ===========================================================================

// -- rounding a Real into Float32 -----------------------------------------

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

/// SMT-LIB `=` on floating-point is element identity: every NaN encoding of a
/// format denotes the ONE NaN element, while the signed zeros and the signed
/// infinities stay distinct. (z3 decides all five of these the same way.)
#[test]
fn equality_identifies_every_nan_encoding_and_nothing_else() {
    let nans = [0x7fc0_0000u32, 0xffc0_0000, 0x7f80_0001, 0xffff_ffff];
    for a in nans {
        for b in nans {
            assert!(
                same_element(&f32_bits(a), &f32_bits(b)),
                "{a:#010x} and {b:#010x} are the same NaN element"
            );
        }
        // A NaN is not any non-NaN, in either direction.
        for other in [0x7f80_0000u32, 0x0000_0000, 0x3f80_0000] {
            assert!(!same_element(&f32_bits(a), &f32_bits(other)));
            assert!(!same_element(&f32_bits(other), &f32_bits(a)));
        }
    }
    // `=` is NOT `fp.eq`: the signed zeros are distinct elements, and so are
    // the signed infinities.
    assert!(!same_element(
        &f32_bits(0x0000_0000),
        &f32_bits(0x8000_0000)
    ));
    assert!(!same_element(
        &f32_bits(0x7f80_0000),
        &f32_bits(0xff80_0000)
    ));
    assert!(same_element(&f32_bits(0x3f80_0000), &f32_bits(0x3f80_0000)));
    // Different formats are different sorts, never equal — a Float16 NaN is
    // not a Float32 NaN.
    let f16_nan = ModelValue::FloatingPoint {
        sign: false,
        exponent: 31,
        significand: 512,
        exponent_bits: 5,
        significand_bits: 11,
    };
    assert!(!same_element(&f16_nan, &f32_bits(0x7fc0_0000)));
}

/// `fp.to_ieee_bv` is the exact inverse of the bit-reinterpreting `to_fp` on
/// every value SMT-LIB determines, sign bit and subnormals included.
#[test]
fn to_ieee_bv_round_trips_every_determined_float32() {
    for bits in [
        0x0000_0000u32, // +zero
        0x8000_0000,    // -zero
        0x3f80_0000,    // 1.0
        0xbf80_0000,    // -1.0
        0x0000_0001,    // smallest subnormal
        0x7f7f_ffff,    // largest finite
        0x7f80_0000,    // +oo
        0xff80_0000,    // -oo
    ] {
        assert_eq!(
            bv_parts(&to_ieee_bv(&f32_bits(bits)).expect("determined")),
            (BigInt::from(bits), 32),
            "fp.to_ieee_bv disagrees on {bits:#010x}"
        );
    }
}

/// A NaN operand is UNDERSPECIFIED — never the operand's own raw bits, which
/// `fp.neg` would change without changing the denoted element.
#[test]
fn to_ieee_bv_of_nan_is_underspecified_not_the_raw_bits() {
    for nan in [0x7fc0_0000u32, 0xffc0_0000, 0x7f80_0001] {
        assert_eq!(
            to_ieee_bv(&f32_bits(nan)).unwrap_err(),
            UNDERSPECIFIED,
            "{nan:#010x} should decline to the adoption path"
        );
    }
}

/// The adoption path is not a blank cheque: the sign bit and the payload are
/// free, being a NaN encoding at all is not. Anything else fails closed, which
/// is what stops an evaluator or solver bug becoming a confirmed `sat`.
#[test]
fn adopted_nan_encodings_must_still_be_nan_encodings() {
    let nan = f32_bits(0x7fc0_0000);
    for admissible in [0x7fc0_0000u32, 0xffc0_0000, 0x7f80_0001, 0xffff_ffff] {
        check_ieee_nan_encoding(&nan, &ModelValue::bitvec(BigInt::from(admissible), 32))
            .unwrap_or_else(|e| panic!("{admissible:#010x} is an admissible NaN encoding: {e}"));
    }
    for rejected in [
        0x0000_0000u32, // +zero: reinterpreting it back gives zero, not NaN
        0x8000_0000,    // -zero
        0x7f80_0000,    // +oo: max exponent but an EMPTY payload
        0xff80_0000,    // -oo
        0x3f80_0000,    // 1.0
    ] {
        assert!(
            check_ieee_nan_encoding(&nan, &ModelValue::bitvec(BigInt::from(rejected), 32)).is_err(),
            "{rejected:#010x} is not a NaN encoding and must be refused"
        );
    }
    // Wrong width, and a non-bitvector value, are refused too.
    assert!(
        check_ieee_nan_encoding(&nan, &ModelValue::bitvec(BigInt::from(0x7fc0_0000u32), 64))
            .is_err()
    );
    assert!(check_ieee_nan_encoding(&nan, &ModelValue::Bool(true)).is_err());
}

/// Float64 and Float16 use the same field split, so the encoding must follow
/// the format rather than a hard-coded 32-bit layout.
#[test]
fn to_ieee_bv_follows_the_operand_format() {
    let one_f64 = ModelValue::FloatingPoint {
        sign: false,
        exponent: 1023,
        significand: 0,
        exponent_bits: 11,
        significand_bits: 53,
    };
    assert_eq!(
        bv_parts(&to_ieee_bv(&one_f64).expect("determined")),
        (BigInt::from(0x3ff0_0000_0000_0000u64), 64)
    );
    let neg_one_f16 = ModelValue::FloatingPoint {
        sign: true,
        exponent: 15,
        significand: 0,
        exponent_bits: 5,
        significand_bits: 11,
    };
    assert_eq!(
        bv_parts(&to_ieee_bv(&neg_one_f16).expect("determined")),
        (BigInt::from(0xbc00u32), 16)
    );
}

// ===========================================================================
// hardware cross-check suite
// ===========================================================================
//
// The oracle here is the host `f32` unit, which IEEE-754 requires to be
// correctly rounded for add/sub/mul/div/sqrt/fma under roundTiesToEven, plus
// exact `BigRational` arithmetic for the directed modes (which the host cannot
// be asked for portably). Between them they cover the cases a plausible-looking
// implementation gets wrong: the zeros' signs, the subnormal boundary, the
// infinities, and the tie-breaking rule.
//
// Everything below binds to `fp.rs` through the shims in this block. If the
// module's call shapes change, this is the ONLY part of the file that moves.

/// The five IEEE classes, reconstructed from the SMT-LIB predicates. Deriving
/// the class this way also pins that the five predicates PARTITION the values:
/// exactly one of them holds for any well-formed datum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FpClass {
    NaN,
    Infinite,
    Zero,
    Subnormal,
    Normal,
}

fn class_of(value: &ModelValue) -> FpClass {
    let mut found: Option<FpClass> = None;
    for (name, class) in [
        ("fp.isNaN", FpClass::NaN),
        ("fp.isInfinite", FpClass::Infinite),
        ("fp.isZero", FpClass::Zero),
        ("fp.isSubnormal", FpClass::Subnormal),
        ("fp.isNormal", FpClass::Normal),
    ] {
        let holds = classify(name, value)
            .expect("classifies")
            .expect("a known predicate");
        if holds {
            assert!(found.is_none(), "{name} overlaps {found:?}");
            found = Some(class);
        }
    }
    found.expect("every well-formed datum has exactly one IEEE class")
}

/// A classification predicate as a plain boolean.
fn predicate(name: &str, value: &ModelValue) -> Result<bool, String> {
    classify(name, value)?.ok_or_else(|| format!("unsupported floating-point predicate {name}"))
}

/// A comparison chain as a plain boolean.
fn comparison(name: &str, values: &[ModelValue]) -> Result<bool, String> {
    compare(name, values)?.ok_or_else(|| format!("unsupported floating-point comparison {name}"))
}

/// `fp.abs` / `fp.neg`.
fn sign_op(name: &str, value: &ModelValue) -> Result<ModelValue, String> {
    unary_sign(name, value)?.ok_or_else(|| format!("unsupported floating-point operator {name}"))
}

/// Any FP operation that takes a rounding mode, dispatched by name.
fn rounded_op(name: &str, rm: RoundingMode, args: &[ModelValue]) -> Result<ModelValue, String> {
    match name {
        "fp.fma" => fma(rm, args),
        "fp.sqrt" => {
            let [x] = args else {
                return Err("fp.sqrt expects one argument".to_string());
            };
            sqrt(rm, x)
        }
        "fp.roundToIntegral" => {
            let [x] = args else {
                return Err("fp.roundToIntegral expects one argument".to_string());
            };
            round_to_integral(rm, x)
        }
        _ => arith(name, rm, args)?
            .ok_or_else(|| format!("unsupported floating-point operator {name}")),
    }
}

/// Any FP operation that takes NO rounding mode, dispatched by name.
fn unrounded_op(name: &str, args: &[ModelValue]) -> Result<ModelValue, String> {
    match name {
        "fp.rem" => rem(args),
        _ => min_max(name, args)?
            .ok_or_else(|| format!("unsupported floating-point operator {name}")),
    }
}

/// `(_ fp.to_ubv m)` / `(_ fp.to_sbv m)`, dispatched by name.
fn to_bv_named(
    name: &str,
    rm: RoundingMode,
    width: u32,
    value: &ModelValue,
) -> Result<ModelValue, String> {
    match name {
        "fp.to_ubv" => to_bv(true, width, rm, value),
        "fp.to_sbv" => to_bv(false, width, rm, value),
        _ => Err(format!("unsupported floating-point operator {name}")),
    }
}

/// The exact rational value of a datum, or `None` for NaN and the infinities.
fn exact_value(value: &ModelValue) -> Option<BigRational> {
    match Fp::from_value(value).ok()?.ext().ok()? {
        Ext::Fin(x) => Some(x),
        Ext::Nan | Ext::Inf(_) => None,
    }
}

/// Whether `fp.to_ieee_bv` of this value is the underspecified case.
fn to_ieee_bv_unspecified(value: &ModelValue) -> bool {
    matches!(to_ieee_bv(value), Err(reason) if reason == UNDERSPECIFIED)
}

/// Whether `bits` is an admissible `fp.to_ieee_bv` answer for the NaN `like`.
fn is_nan_encoding(bits: &ModelValue, like: &ModelValue) -> bool {
    check_ieee_nan_encoding(like, bits).is_ok()
}

const POS_ZERO: u32 = 0x0000_0000;
const NEG_ZERO: u32 = 0x8000_0000;
const ONE: u32 = 0x3f80_0000;
const NEG_ONE: u32 = 0xbf80_0000;
const TWO: u32 = 0x4000_0000;
const THREE: u32 = 0x4040_0000;
const FOUR: u32 = 0x4080_0000;
const NEG_FOUR: u32 = 0xc080_0000;
const FIVE: u32 = 0x40a0_0000;
const NINE: u32 = 0x4110_0000;
const HALF: u32 = 0x3f00_0000;
const NEG_HALF: u32 = 0xbf00_0000;
const ONE_AND_A_HALF: u32 = 0x3fc0_0000;
const POS_INF: u32 = 0x7f80_0000;
const NEG_INF: u32 = 0xff80_0000;
const NAN: u32 = 0x7fc0_0000;
const NEG_NAN: u32 = 0xffc0_0000;
const SMALLEST_SUBNORMAL: u32 = 0x0000_0001;
const NEG_SMALLEST_SUBNORMAL: u32 = 0x8000_0001;
const LARGEST_SUBNORMAL: u32 = 0x007f_ffff;
const SMALLEST_NORMAL: u32 = 0x0080_0000;
const MAX_FINITE: u32 = 0x7f7f_ffff;
const NEG_MAX_FINITE: u32 = 0xff7f_ffff;
/// ~3.14159274, the Float32 nearest pi.
const PI_ISH: u32 = 0x4048_f5c3;
const NEG_PI_ISH: u32 = 0xc048_f5c3;
/// ~1.6e-8: small enough to vanish under a nearest-mode addition to 2.
const TINY: u32 = 0x3333_3333;

const RNE: RoundingMode = RoundingMode::Rne;

const ALL_MODES: [RoundingMode; 5] = [
    RoundingMode::Rne,
    RoundingMode::Rna,
    RoundingMode::Rtp,
    RoundingMode::Rtn,
    RoundingMode::Rtz,
];

fn op2(name: &str, rm: RoundingMode, a: u32, b: u32) -> u32 {
    bits_of(&rounded_op(name, rm, &[f32_bits(a), f32_bits(b)]).unwrap())
}

// -- classification and predicates ----------------------------------------

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
