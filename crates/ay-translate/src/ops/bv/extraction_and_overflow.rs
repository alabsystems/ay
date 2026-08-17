// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `ops::bv` to preserve item DefPaths.

/// Extract bits `[hi:lo]`. Panics on malformed input; see [`try_extract`].
pub fn extract<V>(ctx: &mut impl TranslationHost<V>, hi: u32, lo: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_extract(ctx, hi, lo, t), "bv.extract")
}

/// Fallible [`extract`] returning a `SolverError` instead of panicking.
pub fn try_extract<V>(
    ctx: &mut impl TranslationHost<V>,
    hi: u32,
    lo: u32,
    t: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvextract(t, hi, lo)
}

/// Concatenate two bitvectors. Panics on malformed input; see [`try_concat`].
pub fn concat<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_concat(ctx, a, b), "bv.concat")
}

/// Fallible [`concat()`] returning a `SolverError` instead of panicking.
pub fn try_concat<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvconcat(a, b)
}

/// Extend a bitvector. Panics on malformed input; see [`try_extend`].
pub fn extend<V>(ctx: &mut impl TranslationHost<V>, sign: bool, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        try_extend(ctx, sign, bits, t),
        if sign { "bv.signext" } else { "bv.zeroext" },
    )
}

/// Fallible [`extend`] returning a `SolverError` instead of panicking.
pub fn try_extend<V>(
    ctx: &mut impl TranslationHost<V>,
    sign: bool,
    bits: u32,
    t: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    if sign {
        ctx.solver().try_bvsignext(t, bits)
    } else {
        ctx.solver().try_bvzeroext(t, bits)
    }
}

/// Zero extension.
pub fn zext<V>(ctx: &mut impl TranslationHost<V>, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    extend(ctx, false, bits, t)
}

/// Fallible [`zext`].
pub fn try_zext<V>(
    ctx: &mut impl TranslationHost<V>,
    bits: u32,
    t: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_extend(ctx, false, bits, t)
}

/// Sign extension.
pub fn sext<V>(ctx: &mut impl TranslationHost<V>, bits: u32, t: Term) -> Term
where
    V: Eq + Hash,
{
    extend(ctx, true, bits, t)
}

/// Fallible [`sext`].
pub fn try_sext<V>(
    ctx: &mut impl TranslationHost<V>,
    bits: u32,
    t: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_extend(ctx, true, bits, t)
}

// Overflow detection operations

/// Check that a + b does not overflow. Panics on malformed input; see [`try_add_no_overflow`].
pub fn add_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term, signed: bool) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_add_no_overflow(ctx, a, b, signed), "bv.add_no_overflow")
}

/// Fallible [`add_no_overflow`] returning a `SolverError` instead of panicking.
pub fn try_add_no_overflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
    signed: bool,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvadd_no_overflow(a, b, signed)
}

/// Check that a + b does not underflow. Panics on malformed input; see [`try_add_no_underflow`].
pub fn add_no_underflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_add_no_underflow(ctx, a, b), "bv.add_no_underflow")
}

/// Fallible [`add_no_underflow`] returning a `SolverError` instead of panicking.
pub fn try_add_no_underflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvadd_no_underflow(a, b)
}

/// Check that a - b does not overflow. Panics on malformed input; see [`try_sub_no_overflow`].
pub fn sub_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_sub_no_overflow(ctx, a, b), "bv.sub_no_overflow")
}

/// Fallible [`sub_no_overflow`] returning a `SolverError` instead of panicking.
pub fn try_sub_no_overflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvsub_no_overflow(a, b)
}

/// Check that a - b does not underflow. Panics on malformed input; see [`try_sub_no_underflow`].
pub fn sub_no_underflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
    signed: bool,
) -> Term
where
    V: Eq + Hash,
{
    expect_result(
        try_sub_no_underflow(ctx, a, b, signed),
        "bv.sub_no_underflow",
    )
}

/// Fallible [`sub_no_underflow`] returning a `SolverError` instead of panicking.
pub fn try_sub_no_underflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
    signed: bool,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvsub_no_underflow(a, b, signed)
}

/// Check that a * b does not overflow. Panics on malformed input; see [`try_mul_no_overflow`].
pub fn mul_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term, signed: bool) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_mul_no_overflow(ctx, a, b, signed), "bv.mul_no_overflow")
}

/// Fallible [`mul_no_overflow`] returning a `SolverError` instead of panicking.
pub fn try_mul_no_overflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
    signed: bool,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvmul_no_overflow(a, b, signed)
}

/// Check that a * b does not underflow. Panics on malformed input; see [`try_mul_no_underflow`].
pub fn mul_no_underflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_mul_no_underflow(ctx, a, b), "bv.mul_no_underflow")
}

/// Fallible [`mul_no_underflow`] returning a `SolverError` instead of panicking.
pub fn try_mul_no_underflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvmul_no_underflow(a, b)
}

/// Check that -a does not overflow. Panics on malformed input; see [`try_neg_no_overflow`].
pub fn neg_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_neg_no_overflow(ctx, a), "bv.neg_no_overflow")
}

/// Fallible [`neg_no_overflow`] returning a `SolverError` instead of panicking.
pub fn try_neg_no_overflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvneg_no_overflow(a)
}

/// Check that a / b does not overflow. Panics on malformed input; see [`try_sdiv_no_overflow`].
pub fn sdiv_no_overflow<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_sdiv_no_overflow(ctx, a, b), "bv.sdiv_no_overflow")
}

/// Fallible [`sdiv_no_overflow`] returning a `SolverError` instead of panicking.
pub fn try_sdiv_no_overflow<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_bvsdiv_no_overflow(a, b)
}
