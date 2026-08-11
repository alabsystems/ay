// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for exact IEEE 754 rounding.
//!
//! Expected bit patterns are the ones `f32`/`f64` hardware produces, obtained
//! independently of this code — the point is that an exact rational routine
//! agrees with IEEE hardware on values where hardware is exact, and stays
//! exact where hardware cannot be.

use num_bigint::BigInt;
use num_rational::BigRational;

use super::{round_rational, FpFields, RoundingMode};

const F32_EB: u32 = 8;
const F32_SB: u32 = 24;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn int(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// The fields hardware produces for an `f32`, for cross-checking.
fn f32_fields(v: f32) -> FpFields {
    let bits = v.to_bits();
    FpFields {
        sign: bits >> 31 == 1,
        exponent: u64::from((bits >> 23) & 0xff),
        significand: u64::from(bits & 0x007f_ffff),
    }
}

fn round32(v: &BigRational, rm: RoundingMode) -> FpFields {
    round_rational(v, F32_EB, F32_SB, rm).expect("a well-formed f32 rounding")
}

const ALL_MODES: [RoundingMode; 5] = [
    RoundingMode::NearestTiesToEven,
    RoundingMode::NearestTiesToAway,
    RoundingMode::TowardPositive,
    RoundingMode::TowardNegative,
    RoundingMode::TowardZero,
];

/// The exact rational value of a finite `f32` bit pattern.
fn exact_f32(bits: u32) -> BigRational {
    let fraction = BigInt::from(bits & 0x007f_ffff);
    let exponent_field = (bits >> 23) & 0xff;
    assert_ne!(exponent_field, 0xff, "finite patterns only");
    let (mantissa, exponent) = if exponent_field == 0 {
        (fraction, -149i64)
    } else {
        (
            fraction + (BigInt::from(1) << 23u32),
            i64::from(exponent_field) - 127 - 23,
        )
    };
    let magnitude = if exponent >= 0 {
        BigRational::from(mantissa << u32::try_from(exponent).unwrap())
    } else {
        BigRational::new(
            mantissa,
            BigInt::from(1) << u32::try_from(-exponent).unwrap(),
        )
    };
    if bits >> 31 == 1 {
        -magnitude
    } else {
        magnitude
    }
}

// ---------------------------------------------------------------------------
// Agreement with IEEE hardware on exactly-representable values
// ---------------------------------------------------------------------------

/// The case the FP cluster is about: `(_ to_fp 8 24) RNE 1` must be 1.0f.
#[test]
fn one_rounds_to_the_ieee_bits_for_one() {
    assert_eq!(
        round32(&int(1), RoundingMode::NearestTiesToEven),
        f32_fields(1.0)
    );
}

#[test]
fn exactly_representable_values_match_hardware() {
    for v in [0i64, 1, -1, 2, -2, 3, 255, -255, 1024, -4096, 8_388_607] {
        assert_eq!(
            round32(&int(v), RoundingMode::NearestTiesToEven),
            f32_fields(v as f32),
            "value {v}"
        );
    }
}

#[test]
fn exactly_representable_fractions_match_hardware() {
    for (n, d) in [(1i64, 2i64), (-1, 2), (1, 4), (3, 4), (-7, 8), (1, 1024)] {
        assert_eq!(
            round32(&rat(n, d), RoundingMode::NearestTiesToEven),
            f32_fields(n as f32 / d as f32),
            "value {n}/{d}"
        );
    }
}

/// Zero keeps its sign: `-0.0` is distinct from `+0.0` in SMT-LIB.
#[test]
fn zero_is_signed() {
    let positive = round32(&int(0), RoundingMode::NearestTiesToEven);
    assert_eq!(positive, f32_fields(0.0));
    assert!(!positive.sign);
}

// ---------------------------------------------------------------------------
// Rounding modes: a value BETWEEN two representables
// ---------------------------------------------------------------------------

/// `1 + 2^-24` sits exactly halfway between `1.0f` and the next float up, so
/// every mode has a distinct, checkable answer. This is the tie case.
#[test]
fn a_tie_resolves_per_mode() {
    let half_ulp = BigRational::new(BigInt::from(1), BigInt::from(1i64 << 24));
    let value = int(1) + half_ulp;

    // Ties to even: 1.0f has an even significand, so it stays.
    assert_eq!(
        round32(&value, RoundingMode::NearestTiesToEven),
        f32_fields(1.0)
    );
    // Ties away: up to the next float.
    assert_eq!(
        round32(&value, RoundingMode::NearestTiesToAway),
        f32_fields(f32::from_bits(
            f32_fields(1.0).significand as u32 | 0x3f80_0001
        ))
    );
    // Directed modes ignore the tie entirely.
    assert_eq!(round32(&value, RoundingMode::TowardZero), f32_fields(1.0));
    assert_eq!(
        round32(&value, RoundingMode::TowardNegative),
        f32_fields(1.0)
    );
}

/// A third — not a tie — pins the nearest modes without the tie rule masking
/// a bug.
#[test]
fn a_non_tie_rounds_to_the_nearer_neighbour() {
    let ulp = BigRational::new(BigInt::from(1), BigInt::from(1i64 << 23));
    let just_above_one = int(1) + ulp.clone() / int(4);
    assert_eq!(
        round32(&just_above_one, RoundingMode::NearestTiesToEven),
        f32_fields(1.0),
        "a quarter of an ulp above 1.0 rounds back down"
    );
    let just_below_next = int(1) + ulp * int(3) / int(4);
    assert_ne!(
        round32(&just_below_next, RoundingMode::NearestTiesToEven),
        f32_fields(1.0),
        "three quarters of an ulp above 1.0 rounds up"
    );
}

/// The directed modes must respect the SIGN of the value: `TowardPositive`
/// increases magnitude for positives and decreases it for negatives.
#[test]
fn directed_modes_follow_the_sign() {
    let third = rat(1, 3);
    let up = round32(&third, RoundingMode::TowardPositive);
    let down = round32(&third, RoundingMode::TowardNegative);
    assert_ne!(up, down, "1/3 is not representable, so the modes differ");
    assert!(up.significand > down.significand, "toward +inf is larger");

    let neg_third = -third;
    let neg_up = round32(&neg_third, RoundingMode::TowardPositive);
    let neg_down = round32(&neg_third, RoundingMode::TowardNegative);
    assert!(
        neg_up.significand < neg_down.significand,
        "for a NEGATIVE value, toward +inf means SMALLER magnitude"
    );
}

/// Toward zero always shrinks the magnitude, whatever the sign.
#[test]
fn toward_zero_shrinks_magnitude_for_both_signs() {
    let third = rat(1, 3);
    assert_eq!(
        round32(&third, RoundingMode::TowardZero),
        round32(&third, RoundingMode::TowardNegative),
        "for a positive value, toward zero IS toward negative"
    );
    assert_eq!(
        round32(&(-third), RoundingMode::TowardZero),
        round32(&(-rat(1, 3)), RoundingMode::TowardPositive),
        "for a negative value, toward zero IS toward positive"
    );
}

// ---------------------------------------------------------------------------
// Carry, subnormals, overflow
// ---------------------------------------------------------------------------

/// A significand that rounds up to `2^sb` must carry into the exponent rather
/// than wrap. `2 - 2^-24` rounds up to exactly 2.0f.
#[test]
fn a_rounded_significand_carries_into_the_exponent() {
    let value = int(2) - BigRational::new(BigInt::from(1), BigInt::from(1i64 << 24));
    assert_eq!(
        round32(&value, RoundingMode::NearestTiesToEven),
        f32_fields(2.0)
    );
}

/// Subnormals have a zero exponent field and no hidden bit.
#[test]
fn subnormals_are_encoded_with_a_zero_exponent_field() {
    let smallest_subnormal = f32::from_bits(1);
    let value = BigRational::new(BigInt::from(1), BigInt::from(1) << 149u32);
    let fields = round32(&value, RoundingMode::NearestTiesToEven);
    assert_eq!(fields, f32_fields(smallest_subnormal));
    assert_eq!(fields.exponent, 0, "subnormal exponent field is zero");
    assert_eq!(fields.significand, 1);
}

/// The TOP subnormal binade, `[2^-127, 2^-126)`, is the one an off-by-one in
/// the normal/subnormal test would silently misencode: the normal path would
/// hand back exponent field 0 with the hidden bit subtracted away, which reads
/// back as a completely different (much smaller) number.
#[test]
fn the_largest_subnormal_binade_is_encoded_as_subnormal() {
    let value = BigRational::new(BigInt::from(1), BigInt::from(1) << 127u32);
    let fields = round32(&value, RoundingMode::NearestTiesToEven);
    assert_eq!(fields, f32_fields(f32::from_bits(0x0040_0000)));
    assert_eq!(fields.exponent, 0);
    assert_eq!(
        fields.significand,
        1 << 22,
        "hidden bit is STORED, not implied"
    );

    // And across the binade, including a value needing rounding.
    for bits in [0x0040_0001u32, 0x005a_5a5a, 0x007f_ffff] {
        let hardware = f32::from_bits(bits);
        let exact = BigRational::new(BigInt::from(u64::from(bits)), BigInt::from(1) << 149u32);
        assert_eq!(
            round32(&exact, RoundingMode::NearestTiesToEven),
            f32_fields(hardware),
            "bits {bits:#010x}"
        );
    }
}

/// A negative value too small to represent underflows to NEGATIVE zero, which
/// SMT-LIB distinguishes from `+0`.
#[test]
fn a_tiny_negative_underflows_to_negative_zero() {
    let tiny = -BigRational::new(BigInt::from(1), BigInt::from(1) << 200u32);
    let fields = round32(&tiny, RoundingMode::TowardZero);
    assert_eq!(fields, f32_fields(-0.0));
    assert!(fields.sign, "underflow keeps the sign");
    assert_eq!((fields.exponent, fields.significand), (0, 0));

    // Toward negative infinity it cannot round to zero — it must reach the
    // smallest subnormal instead.
    let away = round32(&tiny, RoundingMode::TowardNegative);
    assert_eq!(away, f32_fields(-f32::from_bits(1)));

    // An exact zero has no sign to keep.
    assert!(!round32(&int(0), RoundingMode::TowardNegative).sign);
}

/// A subnormal that rounds up to the smallest NORMAL crosses the boundary.
#[test]
fn a_subnormal_can_round_up_into_the_normal_range() {
    // Just under the smallest normal, 2^-126.
    let smallest_normal = BigRational::new(BigInt::from(1), BigInt::from(1) << 126u32);
    let just_under =
        &smallest_normal - BigRational::new(BigInt::from(1), BigInt::from(1) << 151u32);
    let fields = round32(&just_under, RoundingMode::NearestTiesToEven);
    assert_eq!(fields, f32_fields(f32::from_bits(0x0080_0000)));
    assert_eq!(fields.significand, 0);
    assert!(fields.exponent > 0, "it became normal");
}

/// Overflow goes to infinity under the nearest modes.
#[test]
fn overflow_goes_to_infinity_under_nearest() {
    let huge = BigRational::from(BigInt::from(1) << 200u32);
    let fields = round32(&huge, RoundingMode::NearestTiesToEven);
    assert_eq!(fields, f32_fields(f32::INFINITY));
    assert_eq!(fields.significand, 0);
}

/// ... but toward zero it stops at the largest finite value, and toward an
/// infinity it depends on the sign.
#[test]
fn overflow_respects_directed_modes() {
    let huge = BigRational::from(BigInt::from(1) << 200u32);
    assert_eq!(
        round32(&huge, RoundingMode::TowardZero),
        f32_fields(f32::MAX),
        "toward zero cannot reach infinity"
    );
    assert_eq!(
        round32(&huge, RoundingMode::TowardNegative),
        f32_fields(f32::MAX),
        "a positive overflow rounding toward -inf stops at MAX"
    );
    assert_eq!(
        round32(&huge, RoundingMode::TowardPositive),
        f32_fields(f32::INFINITY)
    );
    assert_eq!(
        round32(&(-huge.clone()), RoundingMode::TowardNegative),
        f32_fields(f32::NEG_INFINITY)
    );
    // The mirror image: a NEGATIVE overflow rounding toward +inf stops at
    // -MAX, and toward zero likewise.
    assert_eq!(
        round32(&(-huge.clone()), RoundingMode::TowardPositive),
        f32_fields(f32::MIN),
        "toward +inf cannot reach -inf"
    );
    assert_eq!(
        round32(&(-huge.clone()), RoundingMode::TowardZero),
        f32_fields(f32::MIN)
    );
    assert_eq!(
        round32(&(-huge), RoundingMode::NearestTiesToEven),
        f32_fields(f32::NEG_INFINITY)
    );
}

/// Rounding an exactly-representable value is the identity, in EVERY mode. The
/// sweep pins the boundaries individually-chosen cases keep missing: both
/// subnormal binades, the smallest normal binade (where an off-by-one in the
/// normal/subnormal split hides whenever the fraction happens to be zero), and
/// the largest finite value.
#[test]
fn every_finite_bit_pattern_round_trips_under_every_mode() {
    let patterns = [
        0x0000_0000u32, // +0
        0x0000_0001,    // smallest subnormal
        0x0000_0002,
        0x0040_0000, // top subnormal binade
        0x0040_0001,
        0x007f_ffff, // largest subnormal
        0x0080_0000, // smallest normal
        0x0080_0001,
        0x00c0_0000, // smallest normal binade, NONZERO fraction
        0x00ff_ffff,
        0x3f80_0000, // 1.0
        0x3f80_0001, // the next float up
        0x4048_f5c3, // ~3.14
        0x7f7f_ffff, // MAX
        0x8080_0000, // negatives
        0xbf80_0000,
        0xc048_f5c3,
        0xff7f_ffff, // MIN
    ];
    for bits in patterns {
        let value = exact_f32(bits);
        let expected = f32_fields(f32::from_bits(bits));
        for rm in ALL_MODES {
            assert_eq!(
                round32(&value, rm),
                expected,
                "bits {bits:#010x} under {rm:?}"
            );
        }
    }
}

/// Overflow starts one ulp above MAX, not one binade above it. A value with the
/// overflowing exponent and a NONZERO significand is what separates "detected
/// the overflow" from "wrote the exponent field out of range" — the latter
/// silently encodes a NaN.
#[test]
fn the_overflow_boundary_is_exact() {
    let max = exact_f32(0x7f7f_ffff);
    assert_eq!(
        round32(&max, RoundingMode::NearestTiesToEven),
        f32_fields(f32::MAX),
        "MAX itself does not overflow"
    );

    // 1.5 * 2^128: past MAX, but only one binade past it.
    let just_past = BigRational::from(BigInt::from(3) << 127u32);
    let fields = round32(&just_past, RoundingMode::NearestTiesToEven);
    assert_eq!(fields, f32_fields(f32::INFINITY));
    assert_eq!(
        fields.significand, 0,
        "infinity has a zero significand, not a NaN one"
    );

    // A value BELOW 2^128 that rounds UP past MAX still overflows: the carry
    // out of the significand is what pushes the exponent over.
    let half_ulp_past_max = &max + BigRational::from(BigInt::from(1) << 103u32);
    assert_eq!(
        round32(&half_ulp_past_max, RoundingMode::NearestTiesToEven),
        f32_fields(f32::INFINITY),
        "rounding up out of the top binade overflows"
    );
    assert_eq!(
        round32(&half_ulp_past_max, RoundingMode::TowardZero),
        f32_fields(f32::MAX),
        "...but only when the mode actually rounds up"
    );
}

/// A format the routine cannot encode is refused, not approximated. The gate
/// treats `None` as "cannot confirm", so refusing is the safe answer; returning
/// clamped fields would be a well-formed float that is the wrong number.
#[test]
fn an_unrepresentable_format_is_refused() {
    let one = int(1);
    for (eb, sb) in [
        (0u32, 24u32),
        (1, 24),
        (33, 24),
        (8, 0),
        (8, 1),
        (8, 65),
        (64, 64),
        // Float128: `ModelValue::FloatingPoint` stores the fields in `u64`, so
        // a 113-bit significand has nowhere to go. Refusing keeps the gate
        // fail-closed; the alternative — truncating — would confirm models
        // against a DIFFERENT number than the one the solver produced.
        (15, 113),
    ] {
        assert_eq!(
            round_rational(&one, eb, sb, RoundingMode::NearestTiesToEven),
            None,
            "format ({eb}, {sb}) must be refused"
        );
    }
    // Formats it CAN do, including the small ones SMT-LIB allows.
    for (eb, sb) in [(5u32, 11u32), (8, 24), (11, 53), (2, 2), (15, 64)] {
        assert!(
            round_rational(&one, eb, sb, RoundingMode::NearestTiesToEven).is_some(),
            "format ({eb}, {sb}) is representable"
        );
    }
}

/// An exponent large enough that `2^e` would be a multi-megabyte integer is
/// refused rather than allocated. A shift width is an allocation size, so
/// clamping an absurd one would turn a nonsense value into memory pressure.
#[test]
fn an_absurd_exponent_is_refused_not_allocated() {
    let absurd = BigRational::new(BigInt::from(1), BigInt::from(1) << (1u32 << 25));
    assert_eq!(
        round_rational(&absurd, F32_EB, F32_SB, RoundingMode::NearestTiesToEven),
        None
    );
    let absurd_large = BigRational::from(BigInt::from(1) << (1u32 << 25));
    assert_eq!(
        round_rational(
            &absurd_large,
            F32_EB,
            F32_SB,
            RoundingMode::NearestTiesToEven
        ),
        None
    );
    // Just inside the bound still works, and overflows the way it should.
    let large = BigRational::from(BigInt::from(1) << 1000u32);
    assert_eq!(
        round32(&large, RoundingMode::NearestTiesToEven),
        f32_fields(f32::INFINITY)
    );
    let tiny = BigRational::new(BigInt::from(1), BigInt::from(1) << 1000u32);
    assert_eq!(
        round32(&tiny, RoundingMode::NearestTiesToEven),
        f32_fields(0.0)
    );
}

/// Half precision, to pin a format whose subnormal and overflow boundaries are
/// close enough to ordinary values that an exponent mistake shows up.
#[test]
fn half_precision_boundaries() {
    let half = |v: &BigRational, rm| round_rational(v, 5, 11, rm).unwrap();
    // 1.0 in binary16 is exponent field 15, significand 0.
    assert_eq!(
        half(&int(1), RoundingMode::NearestTiesToEven),
        FpFields {
            sign: false,
            exponent: 15,
            significand: 0
        }
    );
    // 65504 is the largest finite binary16 value; 65536 overflows.
    assert_eq!(
        half(&int(65504), RoundingMode::NearestTiesToEven),
        FpFields {
            sign: false,
            exponent: 30,
            significand: 1023
        }
    );
    assert_eq!(
        half(&int(65536), RoundingMode::NearestTiesToEven),
        FpFields {
            sign: false,
            exponent: 31,
            significand: 0
        },
        "overflow to infinity"
    );
    assert_eq!(
        half(&int(65536), RoundingMode::TowardZero),
        FpFields {
            sign: false,
            exponent: 30,
            significand: 1023
        },
        "toward zero stops at the largest finite"
    );
    // 2^-24 is the smallest binary16 subnormal.
    let smallest = BigRational::new(BigInt::from(1), BigInt::from(1) << 24u32);
    assert_eq!(
        half(&smallest, RoundingMode::NearestTiesToEven),
        FpFields {
            sign: false,
            exponent: 0,
            significand: 1
        }
    );
    // Half of it rounds to even, which is zero.
    assert_eq!(
        half(&(smallest / int(2)), RoundingMode::NearestTiesToEven),
        FpFields {
            sign: false,
            exponent: 0,
            significand: 0
        }
    );
}

/// `floor_log2` starts from a bit-length estimate; the correction must reach
/// the exact answer from EITHER side, not just the side that estimate lands on.
#[test]
fn log2_correction_converges_from_a_wrong_start() {
    for (n, d) in [(1i64, 1i64), (3, 2), (1, 3), (1000, 7), (1, 1024), (7, 4)] {
        let value = rat(n, d);
        let truth = super::floor_log2(&value).unwrap();
        for offset in [-9i64, -3, -1, 0, 1, 3, 9] {
            assert_eq!(
                super::correct_log2(&value, truth + offset).unwrap(),
                truth,
                "{n}/{d} from an estimate {offset} away"
            );
        }
        assert!(
            super::pow2(truth).unwrap() <= value && value < super::pow2(truth + 1).unwrap(),
            "{n}/{d}: 2^{truth} <= v < 2^{}",
            truth + 1
        );
    }
}

// ---------------------------------------------------------------------------
// Mode parsing
// ---------------------------------------------------------------------------

#[test]
fn parses_both_spellings_of_every_mode() {
    for (short, long, expected) in [
        (
            "RNE",
            "roundNearestTiesToEven",
            RoundingMode::NearestTiesToEven,
        ),
        (
            "RNA",
            "roundNearestTiesToAway",
            RoundingMode::NearestTiesToAway,
        ),
        ("RTP", "roundTowardPositive", RoundingMode::TowardPositive),
        ("RTN", "roundTowardNegative", RoundingMode::TowardNegative),
        ("RTZ", "roundTowardZero", RoundingMode::TowardZero),
    ] {
        assert_eq!(RoundingMode::from_name(short), Some(expected));
        assert_eq!(RoundingMode::from_name(long), Some(expected));
    }
    assert_eq!(RoundingMode::from_name("RNZ"), None);
    assert_eq!(RoundingMode::from_name(""), None);
}

/// A value hardware CANNOT represent exactly still rounds exactly here: 1/3 in
/// f32 is a specific bit pattern, and the exact routine must find it.
#[test]
fn an_inexact_value_matches_hardware_rounding() {
    for (n, d) in [(1i64, 3i64), (2, 3), (-1, 3), (22, 7), (1, 10), (-1, 10)] {
        assert_eq!(
            round32(&rat(n, d), RoundingMode::NearestTiesToEven),
            f32_fields(n as f32 / d as f32),
            "value {n}/{d}"
        );
    }
}

/// Double precision, to check the format parameters are not hard-coded to f32.
#[test]
fn double_precision_matches_hardware() {
    for (n, d) in [(1i64, 3i64), (22, 7), (-1, 10), (1, 1)] {
        let value = rat(n, d);
        let fields = round_rational(&value, 11, 53, RoundingMode::NearestTiesToEven).unwrap();
        let expected = n as f64 / d as f64;
        let bits = expected.to_bits();
        assert_eq!(
            fields,
            FpFields {
                sign: bits >> 63 == 1,
                exponent: (bits >> 52) & 0x7ff,
                significand: bits & 0x000f_ffff_ffff_ffff,
            },
            "value {n}/{d}"
        );
    }
}

// ---------------------------------------------------------------------------
// Square root
// ---------------------------------------------------------------------------

fn sqrt32(v: &BigRational, rm: RoundingMode) -> FpFields {
    super::sqrt_rational(v, F32_EB, F32_SB, rm).expect("a well-formed f32 square root")
}

/// Perfect squares come back exactly, in every mode — there is nothing to
/// round, so the modes must not diverge.
#[test]
fn exact_square_roots_are_exact_in_every_mode() {
    for (value, root) in [
        (1i64, 1.0f32),
        (4, 2.0),
        (9, 3.0),
        (16, 4.0),
        (65536, 256.0),
        (1 << 40, 1_048_576.0),
    ] {
        for rm in ALL_MODES {
            assert_eq!(
                sqrt32(&int(value), rm),
                f32_fields(root),
                "sqrt({value}) under {rm:?}"
            );
        }
    }
    for (n, d, root) in [(1i64, 4i64, 0.5f32), (9, 16, 0.75), (1, 1024, 0.031_25)] {
        for rm in ALL_MODES {
            assert_eq!(sqrt32(&rat(n, d), rm), f32_fields(root), "sqrt({n}/{d})");
        }
    }
}

/// Inexact roots must match what IEEE hardware produces under RNE. Hardware
/// `sqrt` is correctly rounded, so it is an independent oracle — but only for
/// inputs that are EXACTLY representable as `f32`, otherwise it is taking the
/// root of a different number than the exact rational given here.
#[test]
fn inexact_square_roots_match_hardware_under_rne() {
    for v in [2i64, 3, 5, 7, 10, 1000, 1 << 20, (1 << 24) - 1] {
        assert_eq!(
            sqrt32(&int(v), RoundingMode::NearestTiesToEven),
            f32_fields((v as f32).sqrt()),
            "sqrt({v})"
        );
    }
}

/// The exact value a set of `FpFields` denotes, for f32.
fn as_rational32(f: FpFields) -> BigRational {
    let (mantissa, exponent) = if f.exponent == 0 {
        (BigInt::from(f.significand), -149i64)
    } else {
        (
            BigInt::from(f.significand | (1 << 23)),
            i64::try_from(f.exponent).unwrap() - 127 - 23,
        )
    };
    if exponent >= 0 {
        BigRational::from(mantissa << u32::try_from(exponent).unwrap())
    } else {
        BigRational::new(
            mantissa,
            BigInt::from(1) << u32::try_from(-exponent).unwrap(),
        )
    }
}

/// The next f32 up from a finite non-negative value.
fn next_up32(f: FpFields) -> FpFields {
    if f.significand == 0x007f_ffff {
        FpFields {
            sign: f.sign,
            exponent: f.exponent + 1,
            significand: 0,
        }
    } else {
        FpFields {
            significand: f.significand + 1,
            ..f
        }
    }
}

/// Correct rounding of a square root, checked by its DEFINITION rather than
/// against another implementation: the truncated root is the largest
/// representable value whose square does not exceed the operand, and the other
/// modes follow from where the operand sits relative to the midpoint. Every
/// comparison is exact rational arithmetic on squares, which shares nothing
/// with the integer-`isqrt` method under test.
#[test]
fn square_roots_are_correctly_rounded_by_definition() {
    let cases = [
        (1i64, 3i64),
        (2, 3),
        (22, 7),
        (1, 10),
        (7, 1),
        (123_456_789, 1),
        (1, 123_456_789),
        (3, 1_000_000),
        (999_999_937, 7),
    ];
    for (n, d) in cases {
        let q = rat(n, d);
        let lo = sqrt32(&q, RoundingMode::TowardZero);
        let hi = next_up32(lo);
        let (lo_q, hi_q) = (as_rational32(lo), as_rational32(hi));

        assert!(
            &lo_q * &lo_q <= q,
            "sqrt({n}/{d}): truncation must not exceed"
        );
        assert!(
            &hi_q * &hi_q > q,
            "sqrt({n}/{d}): truncation must be the LARGEST such"
        );

        assert_eq!(
            sqrt32(&q, RoundingMode::TowardNegative),
            lo,
            "sqrt({n}/{d}): a positive root rounds toward -inf the same as toward zero"
        );

        let exact = &lo_q * &lo_q == q;
        let up = sqrt32(&q, RoundingMode::TowardPositive);
        assert_eq!(up, if exact { lo } else { hi }, "sqrt({n}/{d}) toward +inf");

        // Which neighbour is nearer is decided by squaring the midpoint.
        let mid = (&lo_q + &hi_q) / BigRational::from(BigInt::from(2));
        let mid_sq = &mid * &mid;
        let nearest_even = if mid_sq > q {
            lo
        } else if mid_sq < q {
            hi
        } else if lo.significand % 2 == 0 {
            lo
        } else {
            hi
        };
        let nearest_away = if mid_sq > q { lo } else { hi };
        assert_eq!(
            sqrt32(&q, RoundingMode::NearestTiesToEven),
            nearest_even,
            "sqrt({n}/{d}) RNE"
        );
        assert_eq!(
            sqrt32(&q, RoundingMode::NearestTiesToAway),
            nearest_away,
            "sqrt({n}/{d}) RNA"
        );
    }
}

/// A square root CAN land exactly halfway between two floats, which is the
/// case an approximate root cannot distinguish from its neighbours — and the
/// only case where the two nearest modes disagree.
#[test]
fn a_square_root_that_is_exactly_a_tie_resolves_per_mode() {
    // ((2^24 + 1) * 2^-24)^2 has a root with 25 significant bits: a tie.
    let odd = BigInt::from((1u64 << 24) + 1);
    let root = BigRational::new(odd.clone(), BigInt::from(1) << 24u32);
    let value = &root * &root;

    let ties_even = sqrt32(&value, RoundingMode::NearestTiesToEven);
    let ties_away = sqrt32(&value, RoundingMode::NearestTiesToAway);
    let down = sqrt32(&value, RoundingMode::TowardZero);
    let up = sqrt32(&value, RoundingMode::TowardPositive);

    assert_eq!(down, f32_fields(1.0), "truncates to 1.0f");
    assert_eq!(
        up.significand,
        down.significand + 1,
        "toward +inf takes the next float"
    );
    assert_eq!(
        ties_even, down,
        "1.0f has an even significand, so the tie stays"
    );
    assert_eq!(ties_away, up, "ties away takes the next float");
}

/// The directed modes bracket the exact root, and never cross it.
#[test]
fn directed_square_roots_bracket_the_exact_value() {
    for v in [2i64, 3, 5, 7, 1000] {
        let value = int(v);
        let down = sqrt32(&value, RoundingMode::TowardZero);
        let up = sqrt32(&value, RoundingMode::TowardPositive);
        assert_eq!(
            up.significand,
            down.significand + 1,
            "sqrt({v}) is inexact, so the neighbours are adjacent"
        );
        assert_eq!(
            sqrt32(&value, RoundingMode::TowardNegative),
            down,
            "for a positive root, toward -inf IS toward zero"
        );
    }
}

/// A root landing in the subnormal range still encodes as a subnormal.
#[test]
fn a_subnormal_square_root_is_encoded_as_subnormal() {
    // (2^-140)^2 = 2^-280; its root is 2^-140, a subnormal.
    let root = BigRational::new(BigInt::from(1), BigInt::from(1) << 140u32);
    let value = &root * &root;
    let fields = sqrt32(&value, RoundingMode::NearestTiesToEven);
    assert_eq!(fields.exponent, 0, "subnormal");
    assert_eq!(fields.significand, 1 << 9, "2^-140 = 2^9 * 2^-149");
}

/// A negative operand and an unrepresentable format are refused, not guessed:
/// `fp.sqrt` of a negative is NaN, which the caller handles before rounding.
#[test]
fn sqrt_refuses_what_it_cannot_round() {
    assert_eq!(
        super::sqrt_rational(&int(-4), F32_EB, F32_SB, RoundingMode::NearestTiesToEven),
        None
    );
    assert_eq!(
        super::sqrt_rational(&int(0), F32_EB, F32_SB, RoundingMode::NearestTiesToEven),
        None
    );
    assert_eq!(
        super::sqrt_rational(&int(4), 8, 113, RoundingMode::NearestTiesToEven),
        None
    );
}

/// Double precision, so the format parameters are not baked to f32.
#[test]
fn double_precision_square_roots_match_hardware() {
    for v in [2i64, 3, 5, 10, 123_456_789] {
        let fields =
            super::sqrt_rational(&int(v), 11, 53, RoundingMode::NearestTiesToEven).unwrap();
        let bits = (v as f64).sqrt().to_bits();
        assert_eq!(
            fields,
            FpFields {
                sign: bits >> 63 == 1,
                exponent: (bits >> 52) & 0x7ff,
                significand: bits & 0x000f_ffff_ffff_ffff,
            },
            "sqrt({v})"
        );
    }
}
