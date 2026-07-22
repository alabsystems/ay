// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Term};

use super::expect_result;
use crate::TranslationHost;

/// Arithmetic binary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
}

/// Arithmetic unary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Abs,
}

/// Binary arithmetic operation. Panics on malformed input; see [`try_binop`].
pub fn binop<V>(ctx: &mut impl TranslationHost<V>, op: BinOp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match op {
        BinOp::Add => (ctx.solver().try_add(a, b), "arith.add"),
        BinOp::Sub => (ctx.solver().try_sub(a, b), "arith.sub"),
        BinOp::Mul => (ctx.solver().try_mul(a, b), "arith.mul"),
        BinOp::Div => (ctx.solver().try_div(a, b), "arith.div"),
        BinOp::IntDiv => (ctx.solver().try_int_div(a, b), "arith.int_div"),
        BinOp::Mod => (ctx.solver().try_modulo(a, b), "arith.modulo"),
    };
    expect_result(result, tag)
}

/// Fallible [`binop`] returning a `SolverError` instead of panicking.
pub fn try_binop<V>(
    ctx: &mut impl TranslationHost<V>,
    op: BinOp,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match op {
        BinOp::Add => ctx.solver().try_add(a, b),
        BinOp::Sub => ctx.solver().try_sub(a, b),
        BinOp::Mul => ctx.solver().try_mul(a, b),
        BinOp::Div => ctx.solver().try_div(a, b),
        BinOp::IntDiv => ctx.solver().try_int_div(a, b),
        BinOp::Mod => ctx.solver().try_modulo(a, b),
    }
}

/// Unary arithmetic operation. Panics on malformed input; see [`try_unary`].
pub fn unary<V>(ctx: &mut impl TranslationHost<V>, op: UnaryOp, a: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match op {
        UnaryOp::Neg => (ctx.solver().try_neg(a), "arith.neg"),
        UnaryOp::Abs => (ctx.solver().try_abs(a), "arith.abs"),
    };
    expect_result(result, tag)
}

/// Fallible [`unary`] returning a `SolverError` instead of panicking.
pub fn try_unary<V>(
    ctx: &mut impl TranslationHost<V>,
    op: UnaryOp,
    a: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match op {
        UnaryOp::Neg => ctx.solver().try_neg(a),
        UnaryOp::Abs => ctx.solver().try_abs(a),
    }
}

/// Addition.
pub fn add<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Add, a, b)
}

/// Fallible [`add`].
pub fn try_add<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Add, a, b)
}

/// Subtraction.
pub fn sub<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Sub, a, b)
}

/// Fallible [`sub`].
pub fn try_sub<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Sub, a, b)
}

/// Multiplication.
pub fn mul<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Mul, a, b)
}

/// Fallible [`mul`].
pub fn try_mul<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Mul, a, b)
}

/// Division (real).
pub fn div<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Div, a, b)
}

/// Fallible [`div`].
pub fn try_div<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Div, a, b)
}

/// Integer division.
pub fn int_div<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::IntDiv, a, b)
}

/// Fallible [`int_div`].
pub fn try_int_div<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::IntDiv, a, b)
}

/// Modulo.
pub fn modulo<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Mod, a, b)
}

/// Fallible [`modulo`].
pub fn try_modulo<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Mod, a, b)
}

/// Negation.
pub fn neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Neg, a)
}

/// Fallible [`neg`].
pub fn try_neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_unary(ctx, UnaryOp::Neg, a)
}

/// Absolute value.
pub fn abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Abs, a)
}

/// Fallible [`abs`].
pub fn try_abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_unary(ctx, UnaryOp::Abs, a)
}

/// Minimum of two terms.
pub fn min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_min(ctx, a, b), "arith.min")
}

/// Fallible [`min`].
pub fn try_min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_min(a, b)
}

/// Maximum of two terms.
pub fn max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_max(ctx, a, b), "arith.max")
}

/// Fallible [`max`].
pub fn try_max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_max(a, b)
}
