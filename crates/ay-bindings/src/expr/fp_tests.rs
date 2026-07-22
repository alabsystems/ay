// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn test_fp_sort_constructors() {
    assert!(Sort::fp16().is_floating_point());
    assert_eq!(Sort::fp16().fp_exponent_bits(), Some(5));
    assert_eq!(Sort::fp32().fp_exponent_bits(), Some(8));
    assert_eq!(Sort::fp64().fp_exponent_bits(), Some(11));
    assert_eq!(Sort::fp64().fp_significand_bits(), Some(53));
}

#[test]
fn test_fp_operations() {
    let s = Sort::fp32();
    // Constants
    assert!(Expr::fp_plus_infinity(&s).sort().is_floating_point());
    assert!(Expr::fp_nan(&s).sort().is_floating_point());
    // Arithmetic
    let x = Expr::var("x", s.clone());
    let y = Expr::var("y", s);
    assert!(x
        .clone()
        .fp_add(RoundingMode::RNE, y.clone())
        .sort()
        .is_floating_point());
    assert!(x
        .clone()
        .fp_mul(RoundingMode::RTZ, y.clone())
        .sort()
        .is_floating_point());
    assert!(x.clone().fp_neg().sort().is_floating_point());
    // Comparisons
    assert!(x.clone().fp_lt(y.clone()).sort().is_bool());
    assert!(x.clone().fp_eq(y).sort().is_bool());
    // Classification
    assert!(x.clone().fp_is_nan().sort().is_bool());
    assert!(x.clone().fp_is_infinite().sort().is_bool());
    // Conversions
    assert!(x
        .clone()
        .fp_to_sbv(RoundingMode::RTZ, 32)
        .sort()
        .is_bitvec());
    assert!(x.fp_to_real().sort().is_real());
}

#[test]
fn test_fp_display() {
    let s = Sort::fp32();
    let x = Expr::var("x", s.clone());
    let y = Expr::var("y", s.clone());
    assert_eq!(
        format!("{}", x.clone().fp_add(RoundingMode::RNE, y)),
        "(fp.add RNE x y)"
    );
    assert_eq!(format!("{}", Expr::fp_nan(&s)), "(_ NaN 8 24)");
    assert_eq!(format!("{}", x.clone().fp_is_nan()), "(fp.isNaN x)");
    assert_eq!(
        format!("{}", x.fp_to_sbv(RoundingMode::RTZ, 32)),
        "((_ fp.to_sbv 32) RTZ x)"
    );
}

#[test]
fn test_fp_from_bvs() {
    let sign = Expr::var("s", Sort::bitvec(1));
    let exp = Expr::var("e", Sort::bitvec(8));
    let sig = Expr::var("m", Sort::bitvec(23));
    let fp = Expr::fp_from_bvs(sign, exp, sig);
    assert!(fp.sort().is_floating_point());
    assert_eq!(fp.sort().fp_exponent_bits(), Some(8));
    assert_eq!(fp.sort().fp_significand_bits(), Some(24)); // 23 + 1
    assert_eq!(format!("{fp}"), "(fp s e m)");
}

#[test]
fn test_fp_from_bvs_fp16() {
    let sign = Expr::var("s", Sort::bitvec(1));
    let exp = Expr::var("e", Sort::bitvec(5));
    let sig = Expr::var("m", Sort::bitvec(10));
    let fp = Expr::fp_from_bvs(sign, exp, sig);
    assert_eq!(*fp.sort(), Sort::fp16());
}

#[test]
fn test_bv_to_fp() {
    let bv = Expr::var("bv32", Sort::bitvec(32));
    let fp = bv.bv_to_fp(RoundingMode::RNE, 8, 24);
    assert!(fp.sort().is_floating_point());
    assert_eq!(fp.sort().fp_exponent_bits(), Some(8));
    assert_eq!(fp.sort().fp_significand_bits(), Some(24));
    assert_eq!(format!("{fp}"), "((_ to_fp 8 24) RNE bv32)");
}

#[test]
fn test_bv_to_fp_unsigned() {
    let bv = Expr::var("u", Sort::bitvec(16));
    let fp = bv.bv_to_fp_unsigned(RoundingMode::RTZ, 5, 11);
    assert_eq!(*fp.sort(), Sort::fp16());
    assert_eq!(format!("{fp}"), "((_ to_fp_unsigned 5 11) RTZ u)");
}

#[test]
fn test_fp_to_fp_precision_cast() {
    let s32 = Sort::fp32();
    let x = Expr::var("x", s32);
    let fp64 = x.fp_to_fp(RoundingMode::RNE, 11, 53);
    assert_eq!(*fp64.sort(), Sort::fp64());
    assert_eq!(format!("{fp64}"), "((_ to_fp 11 53) RNE x)");
}

#[test]
fn test_qf_fp_program_display() {
    use crate::program::AYProgram;
    let mut prog = AYProgram::qf_fp();
    let s = Sort::fp32();
    let _ = prog.declare_const("x", s.clone());
    let _ = prog.declare_const("y", s);
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp32());
    prog.assert(x.fp_lt(y));
    prog.check_sat();
    let text = format!("{prog}");
    assert!(text.contains("(set-logic QF_FP)"));
    assert!(text.contains("(_ FloatingPoint 8 24)"));
    assert!(text.contains("(fp.lt x y)"));
}

// ===== Tests for try_* fallible API (#5733) =====

#[test]
fn test_try_fp_abs_ok() {
    let x = Expr::var("x", Sort::fp32());
    let result = x.try_fp_abs();
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_floating_point());
}

#[test]
fn test_try_fp_abs_wrong_sort() {
    let x = Expr::var("x", Sort::int());
    let result = x.try_fp_abs();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{err}").contains("fp_abs"));
}

#[test]
fn test_try_fp_add_ok() {
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp32());
    let result = x.try_fp_add(RoundingMode::RNE, y);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_floating_point());
}

#[test]
fn test_try_fp_add_mismatched_sorts() {
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp64());
    let result = x.try_fp_add(RoundingMode::RNE, y);
    assert!(result.is_err());
}

#[test]
fn test_try_fp_add_wrong_sort() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let result = x.try_fp_add(RoundingMode::RNE, y);
    assert!(result.is_err());
}

#[test]
fn test_try_fp_lt_ok() {
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp32());
    let result = x.try_fp_lt(y);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bool());
}

#[test]
fn test_try_fp_is_nan_ok() {
    let x = Expr::var("x", Sort::fp64());
    let result = x.try_fp_is_nan();
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bool());
}

#[test]
fn test_try_fp_is_nan_wrong_sort() {
    let x = Expr::var("x", Sort::bool());
    let result = x.try_fp_is_nan();
    assert!(result.is_err());
}

#[test]
fn test_try_fp_to_sbv_ok() {
    let x = Expr::var("x", Sort::fp32());
    let result = x.try_fp_to_sbv(RoundingMode::RTZ, 32);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_bitvec());
}

#[test]
fn test_try_fp_to_real_wrong_sort() {
    let x = Expr::var("x", Sort::bitvec(32));
    let result = x.try_fp_to_real();
    assert!(result.is_err());
}

#[test]
fn test_try_bv_to_fp_ok() {
    let bv = Expr::var("bv32", Sort::bitvec(32));
    let result = bv.try_bv_to_fp(RoundingMode::RNE, 8, 24);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_floating_point());
}

#[test]
fn test_try_bv_to_fp_wrong_sort() {
    let x = Expr::var("x", Sort::fp32());
    let result = x.try_bv_to_fp(RoundingMode::RNE, 8, 24);
    assert!(result.is_err());
}

#[test]
fn test_try_fp_to_fp_ok() {
    let x = Expr::var("x", Sort::fp32());
    let result = x.try_fp_to_fp(RoundingMode::RNE, 11, 53);
    assert!(result.is_ok());
    let fp64 = result.unwrap();
    assert_eq!(*fp64.sort(), Sort::fp64());
}

#[test]
fn test_try_fp_fma_ok() {
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp32());
    let z = Expr::var("z", Sort::fp32());
    let result = x.try_fp_fma(RoundingMode::RNE, y, z);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_floating_point());
}

#[test]
fn test_try_fp_fma_mismatched() {
    let x = Expr::var("x", Sort::fp32());
    let y = Expr::var("y", Sort::fp64());
    let z = Expr::var("z", Sort::fp32());
    let result = x.try_fp_fma(RoundingMode::RNE, y, z);
    assert!(result.is_err());
}

#[test]
fn test_try_fp_from_bvs_ok() {
    let sign = Expr::var("s", Sort::bitvec(1));
    let exp = Expr::var("e", Sort::bitvec(8));
    let sig = Expr::var("m", Sort::bitvec(23));
    let result = Expr::try_fp_from_bvs(sign, exp, sig);
    assert!(result.is_ok());
    let fp = result.unwrap();
    assert!(fp.sort().is_floating_point());
    assert_eq!(fp.sort().fp_exponent_bits(), Some(8));
    assert_eq!(fp.sort().fp_significand_bits(), Some(24));
}

#[test]
fn test_try_fp_from_bvs_wrong_sign_sort() {
    let sign = Expr::var("s", Sort::int());
    let exp = Expr::var("e", Sort::bitvec(8));
    let sig = Expr::var("m", Sort::bitvec(23));
    let result = Expr::try_fp_from_bvs(sign, exp, sig);
    assert!(result.is_err());
}

#[test]
fn test_try_fp_from_bvs_wrong_sign_width() {
    let sign = Expr::var("s", Sort::bitvec(2));
    let exp = Expr::var("e", Sort::bitvec(8));
    let sig = Expr::var("m", Sort::bitvec(23));
    let result = Expr::try_fp_from_bvs(sign, exp, sig);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{err}").contains("1-bit"));
}

// ===== Tests for try_fp_* constant constructors (#5786) =====

#[test]
fn test_try_fp_plus_infinity_ok() {
    let s = Sort::fp32();
    let result = Expr::try_fp_plus_infinity(&s);
    assert!(result.is_ok());
    assert!(result.unwrap().sort().is_floating_point());
}

#[test]
fn test_try_fp_plus_infinity_wrong_sort() {
    let s = Sort::int();
    let result = Expr::try_fp_plus_infinity(&s);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{err}").contains("fp_plus_infinity"));
}

#[test]
fn test_try_fp_minus_infinity_ok() {
    let result = Expr::try_fp_minus_infinity(&Sort::fp64());
    assert!(result.is_ok());
}

#[test]
fn test_try_fp_nan_ok() {
    let result = Expr::try_fp_nan(&Sort::fp16());
    assert!(result.is_ok());
}

#[test]
fn test_try_fp_nan_wrong_sort() {
    let result = Expr::try_fp_nan(&Sort::bool());
    assert!(result.is_err());
}

#[test]
fn test_try_fp_plus_zero_ok() {
    let result = Expr::try_fp_plus_zero(&Sort::fp32());
    assert!(result.is_ok());
}

#[test]
fn test_try_fp_minus_zero_ok() {
    let result = Expr::try_fp_minus_zero(&Sort::fp64());
    assert!(result.is_ok());
}

#[test]
fn test_try_fp_minus_zero_wrong_sort() {
    let result = Expr::try_fp_minus_zero(&Sort::bitvec(32));
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{err}").contains("fp_minus_zero"));
}
