// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Term};

use super::expect_result;
use crate::TranslationHost;

/// FP rounding mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundingMode {
    /// Round to nearest, ties to even.
    Rne,
    /// Round to nearest, ties away from zero.
    Rna,
    /// Round toward positive infinity.
    Rtp,
    /// Round toward negative infinity.
    Rtn,
    /// Round toward zero.
    Rtz,
}

impl RoundingMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Rne => "RNE",
            Self::Rna => "RNA",
            Self::Rtp => "RTP",
            Self::Rtn => "RTN",
            Self::Rtz => "RTZ",
        }
    }
}

/// FP binary arithmetic operation (requires rounding mode).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// FP comparison predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// FP classification predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassPred {
    IsNaN,
    IsInfinite,
    IsZero,
    IsNormal,
    IsSubnormal,
    IsPositive,
    IsNegative,
}

/// Create a rounding mode term. Panics on malformed input; see [`try_rounding_mode`].
pub fn rounding_mode<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_rounding_mode(ctx, rm), "fp.rounding_mode")
}

/// Fallible [`rounding_mode`] returning a `SolverError` instead of panicking.
pub fn try_rounding_mode<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_rounding_mode(rm.as_str())
}

/// FP binary arithmetic with rounding mode. Panics on malformed input; see [`try_binop`].
pub fn binop<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    op: BinOp,
    a: Term,
    b: Term,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_binop(ctx, rm, op, a, b), "fp.binop")
}

/// Fallible [`binop`] returning a `SolverError` instead of panicking.
pub fn try_binop<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    op: BinOp,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    match op {
        BinOp::Add => ctx.solver().try_fp_add(rm_term, a, b),
        BinOp::Sub => ctx.solver().try_fp_sub(rm_term, a, b),
        BinOp::Mul => ctx.solver().try_fp_mul(rm_term, a, b),
        BinOp::Div => ctx.solver().try_fp_div(rm_term, a, b),
    }
}

/// FP addition with rounding mode.
pub fn add<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Add, a, b)
}

/// FP subtraction with rounding mode.
pub fn sub<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Sub, a, b)
}

/// FP multiplication with rounding mode.
pub fn mul<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Mul, a, b)
}

/// FP division with rounding mode.
pub fn div<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, rm, BinOp::Div, a, b)
}

/// FP square root with rounding mode. Panics on malformed input; see [`try_sqrt`].
pub fn sqrt<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_sqrt(ctx, rm, a), "fp.sqrt")
}

/// Fallible [`sqrt`] returning a `SolverError` instead of panicking.
pub fn try_sqrt<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    a: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_sqrt(rm_term, a)
}

/// FP fused multiply-add with rounding mode: `a * b + c` with single rounding.
/// Panics on malformed input; see [`try_fma`].
pub fn fma<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    a: Term,
    b: Term,
    c: Term,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_fma(ctx, rm, a, b, c), "fp.fma")
}

/// Fallible [`fma`] returning a `SolverError` instead of panicking.
pub fn try_fma<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    a: Term,
    b: Term,
    c: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_fma(rm_term, a, b, c)
}

/// FP IEEE 754 remainder (no rounding mode). Panics on malformed input; see [`try_rem`].
pub fn rem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_rem(ctx, a, b), "fp.rem")
}

/// Fallible [`rem`] returning a `SolverError` instead of panicking.
pub fn try_rem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_rem(a, b)
}

/// FP round-to-integral with rounding mode. Panics on malformed input; see
/// [`try_round_to_integral`].
pub fn round_to_integral<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_round_to_integral(ctx, rm, a), "fp.round_to_integral")
}

/// Fallible [`round_to_integral`] returning a `SolverError` instead of panicking.
pub fn try_round_to_integral<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    a: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_round_to_integral(rm_term, a)
}

/// FP absolute value. Panics on malformed input; see [`try_abs`].
pub fn abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_abs(ctx, a), "fp.abs")
}

/// Fallible [`abs`] returning a `SolverError` instead of panicking.
pub fn try_abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_abs(a)
}

/// FP negation. Panics on malformed input; see [`try_neg`].
pub fn neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_neg(ctx, a), "fp.neg")
}

/// Fallible [`neg`] returning a `SolverError` instead of panicking.
pub fn try_neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_neg(a)
}

/// FP comparison predicate. Panics on malformed input; see [`try_cmp`].
pub fn cmp<V>(ctx: &mut impl TranslationHost<V>, cmp: Cmp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match cmp {
        Cmp::Eq => (ctx.solver().try_fp_eq(a, b), "fp.cmp.eq"),
        Cmp::Lt => (ctx.solver().try_fp_lt(a, b), "fp.cmp.lt"),
        Cmp::Le => (ctx.solver().try_fp_le(a, b), "fp.cmp.le"),
        Cmp::Gt => (ctx.solver().try_fp_gt(a, b), "fp.cmp.gt"),
        Cmp::Ge => (ctx.solver().try_fp_ge(a, b), "fp.cmp.ge"),
    };
    expect_result(result, tag)
}

/// Fallible [`cmp`] returning a `SolverError` instead of panicking.
pub fn try_cmp<V>(
    ctx: &mut impl TranslationHost<V>,
    cmp: Cmp,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match cmp {
        Cmp::Eq => ctx.solver().try_fp_eq(a, b),
        Cmp::Lt => ctx.solver().try_fp_lt(a, b),
        Cmp::Le => ctx.solver().try_fp_le(a, b),
        Cmp::Gt => ctx.solver().try_fp_gt(a, b),
        Cmp::Ge => ctx.solver().try_fp_ge(a, b),
    }
}

/// FP classification predicate. Panics on malformed input; see [`try_classify`].
pub fn classify<V>(ctx: &mut impl TranslationHost<V>, pred: ClassPred, a: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match pred {
        ClassPred::IsNaN => (ctx.solver().try_fp_is_nan(a), "fp.classify.is_nan"),
        ClassPred::IsInfinite => (
            ctx.solver().try_fp_is_infinite(a),
            "fp.classify.is_infinite",
        ),
        ClassPred::IsZero => (ctx.solver().try_fp_is_zero(a), "fp.classify.is_zero"),
        ClassPred::IsNormal => (ctx.solver().try_fp_is_normal(a), "fp.classify.is_normal"),
        ClassPred::IsSubnormal => (
            ctx.solver().try_fp_is_subnormal(a),
            "fp.classify.is_subnormal",
        ),
        ClassPred::IsPositive => (
            ctx.solver().try_fp_is_positive(a),
            "fp.classify.is_positive",
        ),
        ClassPred::IsNegative => (
            ctx.solver().try_fp_is_negative(a),
            "fp.classify.is_negative",
        ),
    };
    expect_result(result, tag)
}

/// Fallible [`classify`] returning a `SolverError` instead of panicking.
pub fn try_classify<V>(
    ctx: &mut impl TranslationHost<V>,
    pred: ClassPred,
    a: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match pred {
        ClassPred::IsNaN => ctx.solver().try_fp_is_nan(a),
        ClassPred::IsInfinite => ctx.solver().try_fp_is_infinite(a),
        ClassPred::IsZero => ctx.solver().try_fp_is_zero(a),
        ClassPred::IsNormal => ctx.solver().try_fp_is_normal(a),
        ClassPred::IsSubnormal => ctx.solver().try_fp_is_subnormal(a),
        ClassPred::IsPositive => ctx.solver().try_fp_is_positive(a),
        ClassPred::IsNegative => ctx.solver().try_fp_is_negative(a),
    }
}

/// FP minimum. Panics on malformed input; see [`try_min`].
pub fn min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_min(ctx, a, b), "fp.min")
}

/// Fallible [`min`] returning a `SolverError` instead of panicking.
pub fn try_min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_min(a, b)
}

/// FP maximum. Panics on malformed input; see [`try_max`].
pub fn max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_max(ctx, a, b), "fp.max")
}

/// Fallible [`max`] returning a `SolverError` instead of panicking.
pub fn try_max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_max(a, b)
}

include!("fp/constants_and_conversions.rs");

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "fp_tests.rs"]
mod tests;
