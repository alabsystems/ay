// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::One;

fn fields(t: &mut TermStore, eb: u32, sb: u32, negative: bool, exp: u64, frac: BigInt) -> TermId {
    let s = t.mk_bitvec(u8::from(negative).into(), 1);
    let e = t.mk_bitvec(exp.into(), eb);
    let m = t.mk_bitvec(frac, sb - 1);
    app(t, "fp", vec![s, e, m], Sort::FloatingPoint(eb, sb))
}

fn bits(t: &mut TermStore, term: TermId) -> BigInt {
    let result = FpRewriter::new().rewrite(t, term);
    numeral::non_nan_ieee_bits(t, result)
        .unwrap_or_else(|| panic!("not folded: {:?}", t.get(result)))
        .0
}

#[test]
fn bounded_wide_addition_preserves_exact_model_fields() {
    for (eb, sb) in [(2, 66), (2, 127), (2, 129), (2, 130), (3, 239), (3, 256)] {
        let mut t = TermStore::new();
        let rm = mode(&mut t, RoundingMode::RNE);
        let bias = (1u64 << (eb - 1)) - 1;
        let one = fields(&mut t, eb, sb, false, bias, 0.into());
        let sum = app(
            &mut t,
            "fp.add",
            vec![rm, one, one],
            Sort::FloatingPoint(eb, sb),
        );
        assert_eq!(bits(&mut t, sum), BigInt::from(bias + 1) << (sb - 1));
        assert_eq!(
            fp_numeral(&t, one).unwrap().to_ieee_bv(),
            (BigInt::from(bias) << (sb - 1), eb + sb)
        );
        assert_eq!(
            FpModelValue::from_fields(false, bias, 0, eb, sb).is_some(),
            sb <= 129
        );
    }
    let mut t = TermStore::new();
    let rm = mode(&mut t, RoundingMode::RNE);
    // The fraction's 129th bit cannot be stored in u128: this is 1.5.
    let x = fields(&mut t, 2, 130, false, 1, BigInt::one() << 128u32);
    assert_eq!(
        fp_numeral(&t, x).unwrap().to_ieee_bv(),
        ((BigInt::one() << 129u32) | (BigInt::one() << 128u32), 132)
    );
    let sum = app(
        &mut t,
        "fp.add",
        vec![rm, x, x],
        Sort::FloatingPoint(2, 130),
    );
    assert_eq!(
        bits(&mut t, sum),
        (BigInt::from(2) << 129u32) | (BigInt::one() << 128u32)
    );
}

#[test]
fn wide_rounding_ties_underflow_overflow_and_signed_zero() {
    for rm in MODES {
        for negative in [false, true] {
            let mut t = TermStore::new();
            let mode = mode(&mut t, rm);
            let sort = Sort::FloatingPoint(3, 130);
            let sign = BigInt::from(u8::from(negative)) << 132u32;
            let outward = rm == RoundingMode::RNA
                || (rm == RoundingMode::RTP && !negative)
                || (rm == RoundingMode::RTN && negative);
            let one = fields(&mut t, 3, 130, negative, 3, 0.into());
            // quantum=2^-131, so fraction 2 is half an ulp at 1.
            let half = fields(&mut t, 3, 130, negative, 0, 2.into());
            let sum = app(&mut t, "fp.add", vec![mode, one, half], sort.clone());
            assert_eq!(
                bits(&mut t, sum),
                &sign | (BigInt::from(3) << 129u32) | BigInt::from(u8::from(outward)),
                "{rm:?} negative={negative}"
            );
            let tiny = fields(&mut t, 3, 130, negative, 0, 1.into());
            let two = fields(&mut t, 3, 130, false, 4, 0.into());
            let div = app(&mut t, "fp.div", vec![mode, tiny, two], sort.clone());
            assert_eq!(bits(&mut t, div), &sign | BigInt::from(u8::from(outward)));
            let max = fields(&mut t, 3, 130, negative, 6, (BigInt::one() << 129u32) - 1);
            let mul = app(&mut t, "fp.mul", vec![mode, max, two], sort);
            let inf = matches!(rm, RoundingMode::RNE | RoundingMode::RNA)
                || (rm == RoundingMode::RTP && !negative)
                || (rm == RoundingMode::RTN && negative);
            let magnitude = if inf {
                BigInt::from(7) << 129u32
            } else {
                (BigInt::from(7) << 129u32) - 1
            };
            assert_eq!(bits(&mut t, mul), sign | magnitude);
        }
        let mut t = TermStore::new();
        let mode = mode(&mut t, rm);
        let a = fields(&mut t, 3, 130, false, 3, 0.into());
        let b = fields(&mut t, 3, 130, true, 3, 0.into());
        let sum = app(
            &mut t,
            "fp.add",
            vec![mode, a, b],
            Sort::FloatingPoint(3, 130),
        );
        assert_eq!(
            bits(&mut t, sum),
            BigInt::from(u8::from(rm == RoundingMode::RTN)) << 132u32
        );
    }
}

#[test]
fn wide_fma_rounds_once_and_other_operations_share_the_core() {
    let mut t = TermStore::new();
    let rm = mode(&mut t, RoundingMode::RNE);
    let a = fields(&mut t, 10, 130, false, 511, 1.into());
    let b = fields(&mut t, 10, 130, false, 510, (BigInt::one() << 129u32) - 2);
    let c = fields(&mut t, 10, 130, true, 511, 0.into());
    let fma = app(
        &mut t,
        "fp.fma",
        vec![rm, a, b, c],
        Sort::FloatingPoint(10, 130),
    );
    assert_eq!(
        bits(&mut t, fma),
        (BigInt::one() << 139u32) | (BigInt::from(253) << 129u32)
    );
    let product = app(
        &mut t,
        "fp.mul",
        vec![rm, a, b],
        Sort::FloatingPoint(10, 130),
    );
    let separate = app(
        &mut t,
        "fp.add",
        vec![rm, product, c],
        Sort::FloatingPoint(10, 130),
    );
    assert_eq!(bits(&mut t, separate), BigInt::from(0));
    let sort = Sort::FloatingPoint(3, 130);
    let four = fields(&mut t, 3, 130, false, 5, 0.into());
    let sqrt = app(&mut t, "fp.sqrt", vec![rm, four], sort.clone());
    assert_eq!(bits(&mut t, sqrt), BigInt::from(4) << 129u32);
    let x = real(&mut t, 3, 2);
    let x = to_fp(&mut t, (3, 130), rm, x);
    let rti = app(&mut t, "fp.roundToIntegral", vec![rm, x], sort.clone());
    assert_eq!(bits(&mut t, rti), BigInt::from(4) << 129u32);
    let rem = app(&mut t, "fp.rem", vec![four, x], sort);
    assert_eq!(
        bits(&mut t, rem),
        (BigInt::one() << 132u32) | (BigInt::from(2) << 129u32)
    );
}

#[test]
fn wide_unspecified_results_and_out_of_bound_formats_refuse() {
    let mut t = TermStore::new();
    let sort = Sort::FloatingPoint(3, 130);
    let nan = t.mk_app(Symbol::indexed("NaN", vec![3, 130]), vec![], sort.clone());
    let pz = fields(&mut t, 3, 130, false, 0, 0.into());
    let nz = fields(&mut t, 3, 130, true, 0, 0.into());
    let ieee = app(&mut t, "fp.to_ieee_bv", vec![nan], Sort::bitvec(133));
    let min = app(&mut t, "fp.min", vec![pz, nz], sort);
    for term in [ieee, min] {
        assert_eq!(FpRewriter::new().rewrite(&mut t, term), term);
    }
    for (eb, sb) in [(21, 130), (3, 257)] {
        let rm = mode(&mut t, RoundingMode::RNE);
        let one = fields(&mut t, eb, sb, false, (1u64 << (eb - 1)) - 1, 0.into());
        let sum = app(
            &mut t,
            "fp.add",
            vec![rm, one, one],
            Sort::FloatingPoint(eb, sb),
        );
        assert_eq!(FpRewriter::new().rewrite(&mut t, sum), sum);
    }
}

#[test]
fn wide_symbolic_mode_and_case_splits_preserve_exact_semantics() {
    let mut t = TermStore::new();
    let rm = t.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
    let one = fields(&mut t, 3, 130, false, 3, 0.into());
    let sum = app(
        &mut t,
        "fp.add",
        vec![rm, one, one],
        Sort::FloatingPoint(3, 130),
    );
    assert_eq!(bits(&mut t, sum), BigInt::from(4) << 129u32);
    let half = fields(&mut t, 3, 130, false, 0, 2.into());
    let tie = app(
        &mut t,
        "fp.add",
        vec![rm, one, half],
        Sort::FloatingPoint(3, 130),
    );
    let split = FpRewriter::new().rewrite(&mut t, tie);
    assert!(
        matches!(t.get(split), TermData::Ite(..)),
        "inexact symbolic mode must split"
    );
    for mode_value in MODES {
        let mode_term = mode(&mut t, mode_value);
        let instantiated = t.substitute(split, &[rm], &[mode_term]);
        let instantiated = t.simplify(instantiated);
        let up = matches!(mode_value, RoundingMode::RNA | RoundingMode::RTP);
        assert_eq!(
            bits(&mut t, instantiated),
            (BigInt::from(3) << 129u32) | BigInt::from(u8::from(up))
        );
    }
}
