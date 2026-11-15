// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The evaluator's rounding arithmetic is exact under every mode: it once ran
//! through host `f64`, which rounds `fp.roundToIntegral` ties away from zero
//! (`f64::round`) and had no answer for any mode but RNE.

use super::*;
use ay_core::term::Symbol;

#[test]
fn rounding_names_use_the_model_binding_of_free_variables() {
    for name in ["RNE", "RTP", "roundNearestTiesToEven"] {
        for mode in crate::executor::rm_domain::RM_MODES {
            let mut executor = Executor::new();
            let rm = executor
                .ctx
                .terms
                .mk_var(name, crate::executor::rm_domain::rm_sort());
            let mut model = Model::empty();
            assert_eq!(executor.rounding_mode(&model, rm), None);
            let mut fp = ay_fp::FpModel::default();
            fp.rm_values.insert(rm, mode);
            model.fp_model = Some(fp);
            assert_eq!(
                executor.rounding_mode(&model, rm),
                Some(mode),
                "{name}: {mode:?}"
            );
        }
    }
}

#[test]
fn rounding_names_require_typed_undeclared_literal_heads() {
    let mut executor = Executor::new();
    let model = Model::empty();
    let sort = crate::executor::rm_domain::rm_sort();
    let literal = executor
        .ctx
        .terms
        .mk_app(Symbol::named("RNE"), [], sort.clone());
    assert_eq!(
        executor.rounding_mode(&model, literal),
        Some(RoundingMode::RNE)
    );
    let malformed = executor
        .ctx
        .terms
        .mk_app(Symbol::named("RTP"), [], Sort::Bool);
    assert_eq!(executor.rounding_mode(&model, malformed), None);
    let indexed = executor
        .ctx
        .terms
        .mk_app(Symbol::indexed("RNE", vec![0]), [], sort);
    assert_eq!(executor.rounding_mode(&model, indexed), None);
    executor.ctx.terms.register_declared_function("RNE");
    assert_eq!(executor.rounding_mode(&model, literal), None);
}

fn f32_value(v: f32) -> FpModelValue {
    let b = v.to_bits();
    FpModelValue::from_fields(
        b >> 31 == 1,
        u64::from((b >> 23) & 0xff),
        u128::from(b & 0x7f_ffff),
        8,
        24,
    )
    .expect("binary32")
}

fn evaluate_under(mode: RoundingMode, op: &str, x: f32, y: Option<f32>) -> EvalValue {
    let mut executor = Executor::new();
    let f32s = Sort::FloatingPoint(8, 24);
    let rm = executor
        .ctx
        .terms
        .mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
    let xv = executor.ctx.terms.mk_var("x", f32s.clone());
    let yv = executor.ctx.terms.mk_var("y", f32s.clone());
    let args = if y.is_some() {
        vec![rm, xv, yv]
    } else {
        vec![rm, xv]
    };
    let term = executor.ctx.terms.mk_app(Symbol::named(op), args, f32s);
    let mut model = Model::empty();
    let mut fp = ay_fp::FpModel::default();
    fp.values.insert(xv, f32_value(x));
    if let Some(y) = y {
        fp.values.insert(yv, f32_value(y));
    }
    fp.rm_values.insert(rm, mode);
    model.fp_model = Some(fp);
    executor.evaluate_term(&model, term)
}

#[test]
fn round_to_integral_breaks_ties_by_the_mode() {
    for (mode, want) in [
        (RoundingMode::RNE, 2.0),
        (RoundingMode::RNA, 3.0),
        (RoundingMode::RTP, 3.0),
        (RoundingMode::RTN, 2.0),
        (RoundingMode::RTZ, 2.0),
    ] {
        assert_eq!(
            evaluate_under(mode, "fp.roundToIntegral", 2.5, None),
            EvalValue::Fp(f32_value(want)),
            "{mode:?}"
        );
    }
}

#[test]
fn directed_modes_round_an_inexact_sum_their_own_way() {
    let tiny = f32::from_bits(0x3000_0000); // 2^-31: below half an ulp of 1.0
    let up = f32::from_bits(0x3f80_0001); // the float after 1.0
    for (mode, want) in [
        (RoundingMode::RNE, 1.0),
        (RoundingMode::RTZ, 1.0),
        (RoundingMode::RTN, 1.0),
        (RoundingMode::RTP, up),
    ] {
        assert_eq!(
            evaluate_under(mode, "fp.add", 1.0, Some(tiny)),
            EvalValue::Fp(f32_value(want)),
            "{mode:?}"
        );
    }
}
