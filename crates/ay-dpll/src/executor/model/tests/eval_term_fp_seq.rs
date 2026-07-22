// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for FP conversion operations and seq.replace_all evaluation.
//! Part of #5995 — model evaluator coverage for FP/seq operations.

use super::*;

// ==========================================================================
// evaluate_term: FP conversion operations (Part of #5995)
// ==========================================================================

#[test]
fn test_evaluate_to_fp_from_rational() {
    // (_ to_fp 5 11) RNE 3.0 → Float16 representing 3.0
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    let three = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(3)));
    let to_fp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("to_fp"), vec![rne, three], fp16);

    let model = empty_model();
    let result = executor.evaluate_term(&model, to_fp);
    match result {
        EvalValue::Fp(v) => {
            let f = v.to_f64().expect("should convert to f64");
            assert!((f - 3.0).abs() < 1e-10, "expected ~3.0, got {f}");
        }
        other => panic!("expected Fp, got {other:?}"),
    }
}

#[test]
fn test_evaluate_to_fp_from_fp_cast() {
    // (_ to_fp 5 11) RNE fp32_value → cast Float32 → Float16
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let fp32 = Sort::FloatingPoint(8, 24);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));

    // Float32 2.5: sign=0, exp=128 (bias=127, real exp=1), sig=0x200000
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(128u32), 8);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(0x200000u32), 23);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp32);

    let cast = executor
        .ctx
        .terms
        .mk_app(Symbol::named("to_fp"), vec![rne, fp_val], fp16);

    let model = empty_model();
    let result = executor.evaluate_term(&model, cast);
    match result {
        EvalValue::Fp(v) => {
            let f = v.to_f64().expect("should convert to f64");
            assert!((f - 2.5).abs() < 1e-10, "expected ~2.5, got {f}");
            assert_eq!(v.eb(), 5, "target should be Float16 eb=5");
            assert_eq!(v.sb(), 11, "target should be Float16 sb=11");
        }
        other => panic!("expected Fp, got {other:?}"),
    }
}

#[test]
fn test_evaluate_fp_to_ubv() {
    // (_ fp.to_ubv 8) RNE (Float16 42.0) → 42 as 8-bit unsigned BV
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));

    // Float16 42.0: 1.0101 * 2^5, bias=15, biased_exp=20, sig=0b0101000000=320
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(20u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(320u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);

    let to_ubv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_ubv"), vec![rne, fp_val], bv8);

    let model = empty_model();
    let result = executor.evaluate_term(&model, to_ubv);
    assert_eq!(
        result,
        EvalValue::BitVec {
            value: BigInt::from(42),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_fp_to_ubv_negative_returns_unknown() {
    // (_ fp.to_ubv 8) RNE (-3.0) → Unknown
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));

    // Float16 -3.0: sign=1, exp=16, sig=512
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(1), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(16u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(512u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);

    let to_ubv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_ubv"), vec![rne, fp_val], bv8);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_ubv), EvalValue::Unknown);
}

#[test]
fn test_evaluate_fp_to_sbv() {
    // (_ fp.to_sbv 8) RNE (-3.0) → 253 (0xFD, -3 in two's complement)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));

    // Float16 -3.0: sign=1, exp=16, sig=512
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(1), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(16u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(512u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);

    let to_sbv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_sbv"), vec![rne, fp_val], bv8);

    let model = empty_model();
    let result = executor.evaluate_term(&model, to_sbv);
    // -3 in two's complement 8-bit = 253
    assert_eq!(
        result,
        EvalValue::BitVec {
            value: BigInt::from(253u32),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_fp_to_real() {
    // fp.to_real (Float16 2.5) → 5/2
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    // Float16 2.5: sign=0, exp=16, sig=256
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(16u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(256u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);

    let to_real = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_real"), vec![fp_val], Sort::Real);

    let model = empty_model();
    let result = executor.evaluate_term(&model, to_real);
    match result {
        EvalValue::Rational(r) => {
            let expected = BigRational::new(BigInt::from(5), BigInt::from(2));
            assert_eq!(r, expected, "expected 5/2, got {r}");
        }
        other => panic!("expected Rational, got {other:?}"),
    }
}

#[test]
fn test_evaluate_fp_to_real_nan_returns_unknown() {
    // fp.to_real NaN → Unknown
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    // Float16 NaN: exp=31 (all 1s), sig=1 (nonzero)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);

    let to_real = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_real"), vec![fp_val], Sort::Real);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_real), EvalValue::Unknown);
}

/// Precision test for fp.to_real: custom FP format wider than Float64.
///
/// FloatingPoint(11, 54) has 53 stored significand bits, which fits in u64
/// but exceeds Float64's sb=53 limit. The old evaluator path (to_f64 →
/// BigRational) would return Unknown for this format (to_f64() returns
/// None when sb > 53). The correct to_rational() path returns the exact
/// rational value.
///
/// Re: #6241 — verifies that to_rational() handles formats that to_f64()
/// rejects, demonstrating the fix is necessary for custom FP widths.
#[test]
fn test_evaluate_fp_to_real_wider_than_f64_format() {
    let mut executor = Executor::new();
    // Custom format: eb=11, sb=54 (53 stored significand bits)
    // to_f64() rejects this (sb > 53), but to_rational() handles it.
    let fp_wide = Sort::FloatingPoint(11, 54);

    // Construct: sign=0, exp=1024 (bias=1023 → effective_exp=1),
    // sig = 2^52 + 1 (53-bit significand with high and low bits set)
    // Value = 2^1 * (2^53 + 2^52 + 1) / 2^53 = 3 + 2^(-52)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(1024u64), 11);
    let sig_val = (1u64 << 52) + 1;
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(sig_val), 53);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp_wide);

    let to_real = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_real"), vec![fp_val], Sort::Real);

    let model = empty_model();
    let result = executor.evaluate_term(&model, to_real);
    match result {
        EvalValue::Rational(r) => {
            // Exact value: (3 * 2^52 + 1) / 2^52
            let denom = BigInt::from(1u64 << 52);
            let numer = BigInt::from(3u64) * &denom + BigInt::from(1u64);
            let expected = BigRational::new(numer, denom);
            assert_eq!(
                r, expected,
                "fp.to_real must return exact rational for formats wider than Float64"
            );
        }
        other => panic!(
            "expected Rational for custom FP format (to_rational() should handle sb=54), \
             got {other:?}"
        ),
    }
}

// ==========================================================================
// evaluate_term: seq.replace_all (Part of #5995)
// ==========================================================================

#[test]
fn test_evaluate_seq_replace_all() {
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));

    let mk_unit = |exec: &mut Executor, v: i64| -> TermId {
        let int_val = exec.ctx.terms.mk_int(BigInt::from(v));
        exec.ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![int_val], seq_sort.clone())
    };

    // Build [1, 2, 1, 2, 1]
    let e1 = mk_unit(&mut executor, 1);
    let e2 = mk_unit(&mut executor, 2);
    let e1b = mk_unit(&mut executor, 1);
    let e2b = mk_unit(&mut executor, 2);
    let e1c = mk_unit(&mut executor, 1);

    let cat1 = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![e1, e2], seq_sort.clone());
    let cat2 =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![cat1, e1b], seq_sort.clone());
    let cat3 =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![cat2, e2b], seq_sort.clone());
    let seq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![cat3, e1c], seq_sort.clone());

    let pattern = mk_unit(&mut executor, 1);
    let replacement = mk_unit(&mut executor, 9);

    let replace_all = executor.ctx.terms.mk_app(
        Symbol::named("seq.replace_all"),
        vec![seq, pattern, replacement],
        seq_sort,
    );

    let model = empty_model();
    let result = executor.evaluate_term(&model, replace_all);
    // [1,2,1,2,1] with 1→9 = [9,2,9,2,9]
    let expected = EvalValue::Seq(vec![
        EvalValue::Rational(BigRational::from(BigInt::from(9))),
        EvalValue::Rational(BigRational::from(BigInt::from(2))),
        EvalValue::Rational(BigRational::from(BigInt::from(9))),
        EvalValue::Rational(BigRational::from(BigInt::from(2))),
        EvalValue::Rational(BigRational::from(BigInt::from(9))),
    ]);
    assert_eq!(result, expected);
}

#[test]
fn test_evaluate_seq_replace_all_empty_pattern() {
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));

    let e1 = {
        let v = executor.ctx.terms.mk_int(BigInt::from(1));
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![v], seq_sort.clone())
    };
    let e2 = {
        let v = executor.ctx.terms.mk_int(BigInt::from(2));
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![v], seq_sort.clone())
    };
    let seq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.++"), vec![e1, e2], seq_sort.clone());

    let empty = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.empty"), vec![], seq_sort.clone());
    let repl = {
        let v = executor.ctx.terms.mk_int(BigInt::from(9));
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![v], seq_sort.clone())
    };

    let replace_all = executor.ctx.terms.mk_app(
        Symbol::named("seq.replace_all"),
        vec![seq, empty, repl],
        seq_sort,
    );

    let model = empty_model();
    let result = executor.evaluate_term(&model, replace_all);
    // Empty pattern: return original
    let expected = EvalValue::Seq(vec![
        EvalValue::Rational(BigRational::from(BigInt::from(1))),
        EvalValue::Rational(BigRational::from(BigInt::from(2))),
    ]);
    assert_eq!(result, expected);
}

// ==========================================================================
// evaluate_term: FP conversion edge cases (Part of #5995, P2:34)
// ==========================================================================

#[test]
fn test_evaluate_fp_to_ubv_nan_returns_unknown() {
    // fp.to_ubv NaN → Unknown (per SMT-LIB: conversion of NaN is undefined)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    // Float16 NaN: exp=31 (all 1s), sig=1 (nonzero)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);
    let to_ubv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_ubv"), vec![rne, fp_val], bv8);
    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_ubv), EvalValue::Unknown);
}

#[test]
fn test_evaluate_fp_to_sbv_nan_returns_unknown() {
    // fp.to_sbv NaN → Unknown (per SMT-LIB: conversion of NaN is undefined)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    // Float16 NaN: exp=31 (all 1s), sig=1 (nonzero)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);
    let to_sbv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_sbv"), vec![rne, fp_val], bv8);
    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_sbv), EvalValue::Unknown);
}

#[test]
fn test_evaluate_fp_to_ubv_overflow_returns_unknown() {
    // fp.to_ubv 8 with 300.0 → Unknown (300 > 255 = max for 8-bit unsigned)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    // Float16 300.0: not representable exactly in Float16 (max normal ≈ 65504).
    // Use a rational conversion instead.
    let three_hundred = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(300)));
    let to_fp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("to_fp"), vec![rne, three_hundred], fp16);
    let to_ubv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_ubv"), vec![rne, to_fp], bv8);
    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_ubv), EvalValue::Unknown);
}

#[test]
fn test_evaluate_fp_to_sbv_overflow_returns_unknown() {
    // fp.to_sbv 8 with 200.0 → Unknown (200 > 127 = max for 8-bit signed)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    let two_hundred = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(200)));
    let to_fp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("to_fp"), vec![rne, two_hundred], fp16);
    let to_sbv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_sbv"), vec![rne, to_fp], bv8);
    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_sbv), EvalValue::Unknown);
}

#[test]
fn test_evaluate_fp_to_ubv_inf_returns_unknown() {
    // fp.to_ubv +Inf → Unknown (per SMT-LIB: conversion of infinity is undefined)
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let bv8 = Sort::bitvec(8);
    let rne = executor
        .ctx
        .terms
        .mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()));
    // Float16 +Inf: sign=0, exp=31 (all 1s), sig=0
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(0u32), 10);
    let fp_val = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16);
    let to_ubv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.to_ubv"), vec![rne, fp_val], bv8);
    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, to_ubv), EvalValue::Unknown);
}

// ==========================================================================
// is_known_theory_symbol: new entries (Part of #5995)
// ==========================================================================

#[test]
fn test_is_known_theory_symbol_fp_conversions() {
    assert!(Executor::is_known_theory_symbol("fp.to_ubv"));
    assert!(Executor::is_known_theory_symbol("fp.to_sbv"));
    assert!(Executor::is_known_theory_symbol("fp.to_real"));
    assert!(Executor::is_known_theory_symbol("to_fp"));
    assert!(Executor::is_known_theory_symbol("fp"));
    assert!(Executor::is_known_theory_symbol("bv2nat"));
}

#[test]
fn test_is_known_theory_symbol_seq_replace_all() {
    assert!(Executor::is_known_theory_symbol("seq.replace_all"));
}

// ==========================================================================
// is_known_theory_symbol: str.< and str.<= (Part of #5995)
// ==========================================================================

#[test]
fn test_is_known_theory_symbol_str_lt_leq() {
    assert!(Executor::is_known_theory_symbol("str.<"));
    assert!(Executor::is_known_theory_symbol("str.<="));
}

// ==========================================================================
// FP NaN comparison: fp.lt/fp.leq/fp.gt/fp.geq return false (Part of #5995)
// IEEE 754 §5.11: all ordered comparisons involving NaN return false.
// ==========================================================================

#[test]
fn test_evaluate_fp_lt_nan_returns_false() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    // NaN: exp=31 (all 1s), sig=1 (nonzero)
    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16.clone());

    // 1.0: exp=15 (bias), sig=0
    let sign2 = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp2 = executor.ctx.terms.mk_bitvec(BigInt::from(15u32), 5);
    let sig2 = executor.ctx.terms.mk_bitvec(BigInt::from(0u32), 10);
    let one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign2, exp2, sig2], fp16);

    let lt_nan_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.lt"), vec![nan, one], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, lt_nan_one),
        EvalValue::Bool(false),
        "NaN < 1.0 should be false per IEEE 754"
    );
}

#[test]
fn test_evaluate_fp_leq_nan_returns_false() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16.clone());

    let sign2 = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp2 = executor.ctx.terms.mk_bitvec(BigInt::from(15u32), 5);
    let sig2 = executor.ctx.terms.mk_bitvec(BigInt::from(0u32), 10);
    let one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign2, exp2, sig2], fp16);

    let leq_nan_one =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("fp.leq"), vec![nan, one], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, leq_nan_one),
        EvalValue::Bool(false),
        "NaN <= 1.0 should be false per IEEE 754"
    );
}

#[test]
fn test_evaluate_fp_gt_nan_returns_false() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16.clone());

    let sign2 = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp2 = executor.ctx.terms.mk_bitvec(BigInt::from(15u32), 5);
    let sig2 = executor.ctx.terms.mk_bitvec(BigInt::from(0u32), 10);
    let one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign2, exp2, sig2], fp16);

    let gt_nan_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.gt"), vec![nan, one], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, gt_nan_one),
        EvalValue::Bool(false),
        "NaN > 1.0 should be false per IEEE 754"
    );
}

#[test]
fn test_evaluate_fp_geq_nan_returns_false() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);

    let sign = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp = executor.ctx.terms.mk_bitvec(BigInt::from(31u32), 5);
    let sig = executor.ctx.terms.mk_bitvec(BigInt::from(1u32), 10);
    let nan = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign, exp, sig], fp16.clone());

    let sign2 = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let exp2 = executor.ctx.terms.mk_bitvec(BigInt::from(15u32), 5);
    let sig2 = executor.ctx.terms.mk_bitvec(BigInt::from(0u32), 10);
    let one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp"), vec![sign2, exp2, sig2], fp16);

    let geq_nan_one =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("fp.geq"), vec![nan, one], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, geq_nan_one),
        EvalValue::Bool(false),
        "NaN >= 1.0 should be false per IEEE 754"
    );
}

// ==========================================================================
// str.< and str.<= evaluation (Part of #5995)
// ==========================================================================

#[test]
fn test_evaluate_str_lt_true() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_string("abc".to_string());
    let b = executor.ctx.terms.mk_string("abd".to_string());
    let lt = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.<"), vec![a, b], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, lt),
        EvalValue::Bool(true),
        "\"abc\" < \"abd\" should be true"
    );
}

#[test]
fn test_evaluate_str_lt_false() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_string("abd".to_string());
    let b = executor.ctx.terms.mk_string("abc".to_string());
    let lt = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.<"), vec![a, b], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, lt),
        EvalValue::Bool(false),
        "\"abd\" < \"abc\" should be false"
    );
}

#[test]
fn test_evaluate_str_leq_equal() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_string("abc".to_string());
    let b = executor.ctx.terms.mk_string("abc".to_string());
    let leq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.<="), vec![a, b], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, leq),
        EvalValue::Bool(true),
        "\"abc\" <= \"abc\" should be true"
    );
}
