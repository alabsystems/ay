// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_rational::BigRational;

const MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

fn pow2(exponent: i32) -> BigRational {
    if exponent >= 0 {
        BigRational::from_integer(BigInt::from(1) << exponent as usize)
    } else {
        BigRational::new(BigInt::from(1), BigInt::from(1) << (-exponent) as usize)
    }
}

fn quad(sign: bool, exponent: u64, fraction: u128) -> FpModelValue {
    FpModelValue::from_fields(sign, exponent, fraction, 15, 113).unwrap()
}

fn rounded(value: &BigRational, mode: RoundingMode) -> FpModelValue {
    FpModelValue::from_rational_with_format(value, 15, 113, mode).unwrap()
}

fn same(actual: &FpModelValue, expected: &FpModelValue) {
    assert!(actual.structural_eq(expected), "{actual:?} != {expected:?}");
}

#[test]
fn binary128_fields_preserve_high_and_low_fraction_bits() {
    let fraction = (1u128 << 111) | 1;
    let value = quad(false, 16383, fraction);
    let bits = BigInt::parse_bytes(b"3fff8000000000000000000000000001", 16).unwrap();
    assert_eq!(value.to_ieee_bv(), (bits.clone(), 128));
    same(&FpModelValue::from_ieee_bv(&bits, 15, 113).unwrap(), &value);
    let expected = BigRational::new(3.into(), 2.into()) + pow2(-112);
    assert_eq!(value.to_rational(), Some(expected.clone()));
    for mode in MODES {
        same(&rounded(&expected, mode), &value);
    }
    assert!(value.to_f64().is_none());
    assert_eq!(
        value.to_smtlib(),
        format!("(fp #b0 #b011111111111111 #b1{}1)", "0".repeat(110))
    );
}

#[test]
fn field_decoders_reject_truncation_and_unrepresentable_fields() {
    assert!(FpModelValue::from_fields(false, 1 << 15, 0, 15, 113).is_none());
    assert!(FpModelValue::from_fields(false, 0, 1u128 << 112, 15, 113).is_none());
    assert!(FpModelValue::from_ieee_bv(&BigInt::from(-1), 15, 113).is_none());
    assert!(FpModelValue::from_ieee_bv(&(BigInt::from(1) << 128usize), 15, 113).is_none());
    assert!(FpModelValue::from_ieee_bv(&BigInt::from(1u64 << 32), 8, 24).is_none());
    for (eb, sb) in [(0, 24), (1, 24), (15, 1)] {
        assert!(FpModelValue::from_fields(false, 0, 0, eb, sb).is_none());
        assert!(FpModelValue::from_ieee_bv(&BigInt::from(0), eb, sb).is_none());
        assert!(FpModelValue::from_rational_with_format(&pow2(0), eb, sb, MODES[0]).is_none());
    }
    // The native-field constructor still refuses formats requiring the exact
    // variant; data decoding and arithmetic retain distinct admission rules.
    for (eb, sb) in [(64, 24), (15, 130)] {
        assert!(FpModelValue::from_fields(false, 0, 0, eb, sb).is_none());
        assert!(FpModelValue::from_ieee_bv(&BigInt::from(1), eb, sb).is_some());
    }
    assert!(FpModelValue::from_rational_with_format(&pow2(0), 64, 24, MODES[0]).is_none());
    assert!(FpModelValue::from_rational_with_format(&pow2(0), 15, 130, MODES[0]).is_some());
    // Keep the full former u64 field envelope, without a shift by 128.
    assert!(FpModelValue::from_fields(false, 1, 1u128 << 64, 63, 65).is_none());
    let old_frontier = FpModelValue::from_fields(false, 1, u128::from(u64::MAX), 63, 65).unwrap();
    same(
        &FpModelValue::from_ieee_bv(&old_frontier.to_ieee_bv().0, 63, 65).unwrap(),
        &old_frontier,
    );
    for value in [
        quad(false, 0, 0),
        quad(true, 0, 0),
        quad(false, 32767, 0),
        quad(true, 32767, 0),
    ] {
        same(
            &FpModelValue::from_ieee_bv(&value.to_ieee_bv().0, 15, 113).unwrap(),
            &value,
        );
    }
    let nan = quad(true, 32767, 1);
    assert!(nan.is_nan());
    assert_eq!(
        nan.to_ieee_bv().0,
        (BigInt::from(32767) << 112usize) | (BigInt::from(1) << 111usize)
    );
    // No NaN payload roundtrip is asserted: SMT-LIB intentionally merges them.
    for denominator in [0, -1] {
        let malformed = BigRational::new_raw(1.into(), denominator.into());
        assert!(FpModelValue::from_rational_with_format(&malformed, 15, 113, MODES[0]).is_none());
    }
}

#[test]
fn exact_model_preserves_199_fraction_bits_through_arithmetic_and_publication() {
    let fraction = (BigUint::from(1u32) << 198usize) | BigUint::from(1u32);
    let bits = (BigInt::from(127) << 199usize) | BigInt::from(fraction.clone());
    let value = FpModelValue::from_ieee_bv(&bits, 8, 200).unwrap();
    let FpModelValue::Exact(fields) = &value else {
        panic!("199 fraction bits require exact fields");
    };
    assert_eq!(fields.significand(), &fraction);
    assert_eq!(value.to_ieee_bv(), (bits, 208));
    assert!(value.is_normal());
    let rational = BigRational::new(3.into(), 2.into()) + pow2(-199);
    assert_eq!(value.to_rational(), Some(rational.clone()));
    let zero = FpModelValue::from_exact_fields(false, 0u32.into(), 0u32.into(), 8, 200).unwrap();
    for mode in MODES {
        same(
            &FpModelValue::from_rational_with_format(&rational, 8, 200, mode).unwrap(),
            &value,
        );
        same(&crate::exact::add(mode, &value, &zero).unwrap(), &value);
    }
    assert_eq!(
        value.to_smtlib(),
        format!("(fp #b0 #b01111111 #b1{}1)", "0".repeat(197))
    );
    same(&value.negate().negate(), &value);
    same(&value.negate().abs(), &value);
    assert!(!value.structural_eq(&value.negate()));
    assert_eq!(value.negate().fp_lt(&zero), Some(true));
}

#[test]
fn exact_special_values_interoperate_without_rounding_or_losing_zero_sign() {
    let nan = FpModelValue::from_exact_fields(true, 255u32.into(), 7u32.into(), 8, 200).unwrap();
    let other_nan = FpModelValue::NaN { eb: 8, sb: 200 };
    assert!(nan.structural_eq(&other_nan));
    assert!(!nan.fp_eq(&other_nan));
    let zero = FpModelValue::from_exact_fields(false, 0u32.into(), 0u32.into(), 8, 200).unwrap();
    let neg_zero = FpModelValue::NegZero { eb: 8, sb: 200 };
    assert!(zero.fp_eq(&neg_zero));
    assert!(!zero.structural_eq(&neg_zero));
    let inf = FpModelValue::PosInf { eb: 8, sb: 200 };
    assert_eq!(zero.fp_lt(&inf), Some(true));
    assert!(nan.to_rational().is_none());
}

#[test]
fn custom_model_fields_roundtrip_beyond_a_packed_native_word() {
    for (eb, sb) in [(2, 66), (15, 112), (16, 113), (2, 128), (3, 129), (63, 129)] {
        let bias = (1u64 << (eb - 1)) - 1;
        let fraction = u128::MAX >> (129 - sb);
        for sign in [false, true] {
            let value = FpModelValue::from_fields(sign, bias, fraction, eb, sb).unwrap();
            let (bits, width) = value.to_ieee_bv();
            assert_eq!(width, eb + sb);
            same(&FpModelValue::from_ieee_bv(&bits, eb, sb).unwrap(), &value);
            let rational = value.to_rational().unwrap();
            for mode in MODES {
                same(
                    &FpModelValue::from_rational_with_format(&rational, eb, sb, mode).unwrap(),
                    &value,
                );
            }
            assert!(FpModelValue::from_ieee_bv(&(BigInt::from(1) << width), eb, sb).is_none());
        }
    }
    // At the full stored-fraction frontier directed overflow must retain all
    // 128 low bits, without shifting a native integer by its width.
    let maximum = FpModelValue::from_fields(false, 2, u128::MAX, 2, 129).unwrap();
    same(
        &FpModelValue::from_rational_with_format(&pow2(2), 2, 129, RoundingMode::RTZ).unwrap(),
        &maximum,
    );
}

#[test]
fn binary128_exact_normal_subnormal_and_maximum_values() {
    let fraction_max = (1u128 << 112) - 1;
    let cases = [
        (quad(false, 0, 1), pow2(-16494)),
        (
            quad(false, 0, fraction_max),
            BigRational::from_integer(BigInt::from(fraction_max)) * pow2(-16494),
        ),
        (quad(false, 1, 0), pow2(-16382)),
        (
            quad(false, 32766, fraction_max),
            BigRational::from_integer((BigInt::from(1) << 113usize) - 1) * pow2(16271),
        ),
    ];
    for (value, rational) in cases {
        assert_eq!(value.to_rational(), Some(rational.clone()));
        for mode in MODES {
            same(&rounded(&rational, mode), &value);
            same(&rounded(&(-rational.clone()), mode), &value.negate());
        }
    }
}

#[test]
fn binary128_normal_halfway_rounding_keeps_bits_beyond_f64() {
    let even_tie = pow2(0) + pow2(-113);
    let odd_tie = pow2(0) + BigRational::from_integer(3.into()) * pow2(-113);
    for sign in [false, true] {
        for mode in MODES {
            let value = if sign {
                -even_tie.clone()
            } else {
                even_tie.clone()
            };
            let increment = match mode {
                RoundingMode::RNE | RoundingMode::RTZ => false,
                RoundingMode::RNA => true,
                RoundingMode::RTP => !sign,
                RoundingMode::RTN => sign,
            };
            same(
                &rounded(&value, mode),
                &quad(sign, 16383, u128::from(increment)),
            );
        }
        let value = if sign {
            -odd_tie.clone()
        } else {
            odd_tie.clone()
        };
        same(&rounded(&value, RoundingMode::RNE), &quad(sign, 16383, 2));
        same(&rounded(&value, RoundingMode::RNA), &quad(sign, 16383, 2));
    }
}

#[test]
fn binary128_underflow_signed_zero_and_normal_transition() {
    let half_minimum = pow2(-16495);
    let transition = pow2(-16382) - pow2(-16495);
    for sign in [false, true] {
        for mode in MODES {
            let value = if sign {
                -half_minimum.clone()
            } else {
                half_minimum.clone()
            };
            let up = match mode {
                RoundingMode::RNE | RoundingMode::RTZ => false,
                RoundingMode::RNA => true,
                RoundingMode::RTP => !sign,
                RoundingMode::RTN => sign,
            };
            same(&rounded(&value, mode), &quad(sign, 0, u128::from(up)));
            let value = if sign {
                -transition.clone()
            } else {
                transition.clone()
            };
            let normal = match mode {
                RoundingMode::RNE | RoundingMode::RNA => true,
                RoundingMode::RTZ => false,
                RoundingMode::RTP => !sign,
                RoundingMode::RTN => sign,
            };
            let expected = if normal {
                quad(sign, 1, 0)
            } else {
                quad(sign, 0, (1u128 << 112) - 1)
            };
            same(&rounded(&value, mode), &expected);
        }
    }
}

#[test]
fn directed_overflow_obeys_sign_and_mode_in_old_formats_and_binary128() {
    for (eb, sb) in [(5, 11), (8, 24), (11, 53), (15, 113)] {
        let bias = (1i32 << (eb - 1)) - 1;
        let ulp = pow2(bias - (sb as i32 - 1));
        let max = BigRational::from_integer((BigInt::from(1) << sb as usize) - 1) * &ulp;
        let midpoint = &max + &ulp / BigRational::from_integer(2.into());
        // The midpoint exercises significand carry; 2^(emax+1) exercises the
        // early overflow branch. Nearest just below the midpoint stays finite.
        for magnitude in [midpoint.clone(), pow2(bias + 1)] {
            for sign in [false, true] {
                for mode in MODES {
                    let value = if sign {
                        -magnitude.clone()
                    } else {
                        magnitude.clone()
                    };
                    let infinity = match mode {
                        RoundingMode::RNE | RoundingMode::RNA => true,
                        RoundingMode::RTZ => false,
                        RoundingMode::RTP => !sign,
                        RoundingMode::RTN => sign,
                    };
                    let exp = if infinity {
                        (1u64 << eb) - 1
                    } else {
                        (1u64 << eb) - 2
                    };
                    let fraction = if infinity { 0 } else { (1u128 << (sb - 1)) - 1 };
                    same(
                        &FpModelValue::from_rational_with_format(&value, eb, sb, mode).unwrap(),
                        &FpModelValue::from_fields(sign, exp, fraction, eb, sb).unwrap(),
                    );
                }
            }
        }
        let below = midpoint - &ulp / BigRational::from_integer(4.into());
        let expected =
            FpModelValue::from_fields(false, (1u64 << eb) - 2, (1u128 << (sb - 1)) - 1, eb, sb)
                .unwrap();
        same(
            &FpModelValue::from_rational_with_format(&below, eb, sb, RoundingMode::RNE).unwrap(),
            &expected,
        );
    }
}

#[test]
fn binary128_order_is_exact_and_retains_nan_and_signed_zero_semantics() {
    let ordered = [
        quad(true, 32767, 0),
        quad(true, 32766, (1u128 << 112) - 1),
        quad(true, 16383, 1),
        quad(true, 16383, 0),
        quad(true, 0, 1),
        quad(true, 0, 0),
        quad(false, 0, 0),
        quad(false, 0, 1),
        quad(false, 16383, 0),
        quad(false, 16383, 1),
        quad(false, 32766, (1u128 << 112) - 1),
        quad(false, 32767, 0),
    ];
    for (i, a) in ordered.iter().enumerate() {
        for (j, b) in ordered.iter().enumerate() {
            let equal = i == j || (a.is_zero() && b.is_zero());
            assert_eq!(a.fp_lt(b), Some(i < j && !equal));
            assert_eq!(a.fp_leq(b), Some(i < j || equal));
            assert_eq!(a.fp_gt(b), Some(i > j && !equal));
            assert_eq!(a.fp_geq(b), Some(i > j || equal));
        }
        let nan = quad(false, 32767, 1);
        for (a, b) in [(a, &nan), (&nan, a)] {
            assert_eq!(
                (a.fp_lt(b), a.fp_leq(b), a.fp_gt(b), a.fp_geq(b)),
                (Some(false), Some(false), Some(false), Some(false))
            );
        }
    }
}

#[test]
fn existing_binary32_and_binary64_value_paths_keep_exact_bits() {
    for value in [
        0.0f32,
        -0.0,
        1.0,
        -1.5,
        f32::MIN_POSITIVE,
        f32::from_bits(1),
        f32::MAX,
        f32::INFINITY,
        f32::NEG_INFINITY,
    ] {
        let bits = BigInt::from(value.to_bits());
        let decoded = FpModelValue::from_ieee_bv(&bits, 8, 24).unwrap();
        assert_eq!(decoded.to_ieee_bv(), (bits, 32));
        assert_eq!(
            (decoded.to_f64().unwrap() as f32).to_bits(),
            value.to_bits()
        );
    }
    for value in [
        0.0f64,
        -0.0,
        1.0,
        -1.5,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ] {
        let bits = BigInt::from(value.to_bits());
        let decoded = FpModelValue::from_ieee_bv(&bits, 11, 53).unwrap();
        assert_eq!(decoded.to_ieee_bv(), (bits, 64));
        assert_eq!(decoded.to_f64().unwrap().to_bits(), value.to_bits());
    }
}
