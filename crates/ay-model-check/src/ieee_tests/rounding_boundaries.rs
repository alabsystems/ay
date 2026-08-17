// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `ieee::tests` to preserve test FQNs.

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
