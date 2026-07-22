// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigInt;

#[test]
fn test_to_rational_pos_zero() {
    let val = FpModelValue::PosZero { eb: 8, sb: 24 };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(0.into()));
}

#[test]
fn test_to_rational_neg_zero() {
    let val = FpModelValue::NegZero { eb: 8, sb: 24 };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(0.into()));
}

#[test]
fn test_to_rational_nan_returns_none() {
    let val = FpModelValue::NaN { eb: 8, sb: 24 };
    assert!(val.to_rational().is_none());
}

#[test]
fn test_to_rational_pos_inf_returns_none() {
    let val = FpModelValue::PosInf { eb: 8, sb: 24 };
    assert!(val.to_rational().is_none());
}

#[test]
fn test_to_rational_neg_inf_returns_none() {
    let val = FpModelValue::NegInf { eb: 11, sb: 53 };
    assert!(val.to_rational().is_none());
}

#[test]
fn test_to_rational_float32_one() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 127,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(1.into()));
}

#[test]
fn test_to_rational_float32_neg_one() {
    let val = FpModelValue::Fp {
        sign: true,
        exponent: 127,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer((-1).into()));
}

#[test]
fn test_to_rational_float32_two() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 128,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(2.into()));
}

#[test]
fn test_to_rational_float32_half() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 126,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(1.into(), 2.into());
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float32_subnormal_min() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 0,
        significand: 1,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(1.into(), BigInt::from(1u64) << 149u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float32_subnormal_max() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 0,
        significand: (1u64 << 23) - 1,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(
        BigInt::from((1u64 << 23) - 1),
        BigInt::from(1u64) << 149u64,
    );
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float32_neg_subnormal() {
    let val = FpModelValue::Fp {
        sign: true,
        exponent: 0,
        significand: 42,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let expected = -num_rational::BigRational::new(42.into(), BigInt::from(1u64) << 149u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float32_max_normal() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 254,
        significand: (1u64 << 23) - 1,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let sig = BigInt::from((1u64 << 24) - 1);
    let expected = num_rational::BigRational::from_integer(sig << 104u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float32_min_normal() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 1,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(1.into(), BigInt::from(1u64) << 126u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float64_one() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 1023,
        significand: 0,
        eb: 11,
        sb: 53,
    };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(1.into()));
}

#[test]
fn test_to_rational_float64_large_exponent() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 1123,
        significand: 0,
        eb: 11,
        sb: 53,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::from_integer(BigInt::from(1u64) << 100u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float64_subnormal() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 0,
        significand: 1,
        eb: 11,
        sb: 53,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(1.into(), BigInt::from(1u64) << 1074u64);
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_float16_quarter() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 13,
        significand: 0,
        eb: 5,
        sb: 11,
    };
    let r = val.to_rational().expect("should convert");
    let expected = num_rational::BigRational::new(1.into(), 4.into());
    assert_eq!(r, expected);
}

#[test]
fn test_to_rational_subnormal_zero_sig_returns_zero() {
    let val = FpModelValue::Fp {
        sign: false,
        exponent: 0,
        significand: 0,
        eb: 8,
        sb: 24,
    };
    let r = val.to_rational().expect("should convert");
    assert_eq!(r, num_rational::BigRational::from_integer(0.into()));
}

#[test]
fn test_from_rational_extended_precision_exact_integer() {
    let value = num_rational::BigRational::from_integer(BigInt::from(9_007_199_254_740_993u64));
    let fp = FpModelValue::from_rational_with_format(&value, 11, 54, RoundingMode::RNE)
        .expect("extended-precision integer should convert");

    match fp {
        FpModelValue::Fp {
            sign,
            exponent,
            significand,
            eb,
            sb,
        } => {
            assert!(!sign, "converted value should be positive");
            assert_eq!(exponent, 1076, "biased exponent should encode 2^53 scale");
            assert_eq!(
                significand, 1,
                "2^53 + 1 must stay exact at 54-bit precision"
            );
            assert_eq!((eb, sb), (11, 54));
        }
        other => panic!("expected finite FP value, got {other:?}"),
    }
}
