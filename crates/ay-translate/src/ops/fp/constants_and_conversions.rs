// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// FP +infinity constant. Infallible — no fallible variant needed.
pub fn plus_infinity<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_plus_infinity(eb, sb)
}

/// FP -infinity constant. Infallible — no fallible variant needed.
pub fn minus_infinity<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_minus_infinity(eb, sb)
}

/// FP NaN constant. Infallible — no fallible variant needed.
pub fn nan<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_nan(eb, sb)
}

/// FP +zero constant. Infallible — no fallible variant needed.
pub fn plus_zero<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_plus_zero(eb, sb)
}

/// FP -zero constant. Infallible — no fallible variant needed.
pub fn minus_zero<V>(ctx: &mut impl TranslationHost<V>, eb: u32, sb: u32) -> Term
where
    V: Eq + Hash,
{
    ctx.solver().fp_minus_zero(eb, sb)
}

/// Convert FP to signed bitvector. Panics on malformed input; see [`try_to_sbv`].
pub fn to_sbv<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, x: Term, width: u32) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_sbv(ctx, rm, x, width), "fp.to_sbv")
}

/// Fallible [`to_sbv`] returning a `SolverError` instead of panicking.
pub fn try_to_sbv<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    x: Term,
    width: u32,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_to_sbv(rm_term, x, width)
}

/// Convert FP to unsigned bitvector. Panics on malformed input; see [`try_to_ubv`].
pub fn to_ubv<V>(ctx: &mut impl TranslationHost<V>, rm: RoundingMode, x: Term, width: u32) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_ubv(ctx, rm, x, width), "fp.to_ubv")
}

/// Fallible [`to_ubv`] returning a `SolverError` instead of panicking.
pub fn try_to_ubv<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    x: Term,
    width: u32,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_to_ubv(rm_term, x, width)
}

/// Convert FP to real. Panics on malformed input; see [`try_to_real`].
pub fn to_real<V>(ctx: &mut impl TranslationHost<V>, x: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_real(ctx, x), "fp.to_real")
}

/// Fallible [`to_real`] returning a `SolverError` instead of panicking.
pub fn try_to_real<V>(ctx: &mut impl TranslationHost<V>, x: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_fp_to_real(x)
}

/// Convert bitvector to FP. Panics on malformed input; see [`try_from_bv`].
pub fn from_bv<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    bv: Term,
    eb: u32,
    sb: u32,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_from_bv(ctx, rm, bv, eb, sb), "fp.from_bv")
}

/// Fallible [`from_bv`] returning a `SolverError` instead of panicking.
pub fn try_from_bv<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    bv: Term,
    eb: u32,
    sb: u32,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_bv_to_fp(rm_term, bv, eb, sb)
}

/// Convert FP to different precision. Panics on malformed input; see [`try_to_fp`].
pub fn to_fp<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    fp: Term,
    eb: u32,
    sb: u32,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_to_fp(ctx, rm, fp, eb, sb), "fp.to_fp")
}

/// Fallible [`to_fp`] returning a `SolverError` instead of panicking.
pub fn try_to_fp<V>(
    ctx: &mut impl TranslationHost<V>,
    rm: RoundingMode,
    fp: Term,
    eb: u32,
    sb: u32,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    let rm_term = ctx.solver().try_fp_rounding_mode(rm.as_str())?;
    ctx.solver().try_fp_to_fp(rm_term, fp, eb, sb)
}
