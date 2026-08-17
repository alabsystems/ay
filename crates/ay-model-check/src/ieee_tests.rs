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

include!("ieee_tests/rounding_boundaries.rs");

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
        } else if lo.significand.is_multiple_of(2) {
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
