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

include!("fp_tests/standard_rounding_and_arithmetic.rs");

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

include!("fp_tests/hardware_classification_and_arithmetic.rs");

include!("fp_tests/hardware_rounding_and_conversion.rs");
