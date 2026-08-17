// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector operations.

use std::hash::Hash;

use ay_dpll::api::{SolverError, Term};

use super::expect_result;
use crate::TranslationHost;

/// Bitvector binary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

/// Bitvector unary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Bitvector comparison type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    ULt,
    ULe,
    UGt,
    UGe,
    SLt,
    SLe,
    SGt,
    SGe,
}

/// Bitvector binary operation. Panics on malformed input; see [`try_binop`].
pub fn binop<V>(ctx: &mut impl TranslationHost<V>, op: BinOp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match op {
        BinOp::Add => (ctx.solver().try_bvadd(a, b), "bv.add"),
        BinOp::Sub => (ctx.solver().try_bvsub(a, b), "bv.sub"),
        BinOp::Mul => (ctx.solver().try_bvmul(a, b), "bv.mul"),
        BinOp::UDiv => (ctx.solver().try_bvudiv(a, b), "bv.udiv"),
        BinOp::SDiv => (ctx.solver().try_bvsdiv(a, b), "bv.sdiv"),
        BinOp::URem => (ctx.solver().try_bvurem(a, b), "bv.urem"),
        BinOp::SRem => (ctx.solver().try_bvsrem(a, b), "bv.srem"),
        BinOp::And => (ctx.solver().try_bvand(a, b), "bv.and"),
        BinOp::Or => (ctx.solver().try_bvor(a, b), "bv.or"),
        BinOp::Xor => (ctx.solver().try_bvxor(a, b), "bv.xor"),
        BinOp::Shl => (ctx.solver().try_bvshl(a, b), "bv.shl"),
        BinOp::LShr => (ctx.solver().try_bvlshr(a, b), "bv.lshr"),
        BinOp::AShr => (ctx.solver().try_bvashr(a, b), "bv.ashr"),
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
        BinOp::Add => ctx.solver().try_bvadd(a, b),
        BinOp::Sub => ctx.solver().try_bvsub(a, b),
        BinOp::Mul => ctx.solver().try_bvmul(a, b),
        BinOp::UDiv => ctx.solver().try_bvudiv(a, b),
        BinOp::SDiv => ctx.solver().try_bvsdiv(a, b),
        BinOp::URem => ctx.solver().try_bvurem(a, b),
        BinOp::SRem => ctx.solver().try_bvsrem(a, b),
        BinOp::And => ctx.solver().try_bvand(a, b),
        BinOp::Or => ctx.solver().try_bvor(a, b),
        BinOp::Xor => ctx.solver().try_bvxor(a, b),
        BinOp::Shl => ctx.solver().try_bvshl(a, b),
        BinOp::LShr => ctx.solver().try_bvlshr(a, b),
        BinOp::AShr => ctx.solver().try_bvashr(a, b),
    }
}

/// Bitvector unary operation. Panics on malformed input; see [`try_unary`].
pub fn unary<V>(ctx: &mut impl TranslationHost<V>, op: UnaryOp, a: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match op {
        UnaryOp::Not => (ctx.solver().try_bvnot(a), "bv.not"),
        UnaryOp::Neg => (ctx.solver().try_bvneg(a), "bv.neg"),
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
        UnaryOp::Not => ctx.solver().try_bvnot(a),
        UnaryOp::Neg => ctx.solver().try_bvneg(a),
    }
}

/// Bitvector comparison. Panics on malformed input; see [`try_cmp`].
pub fn cmp<V>(ctx: &mut impl TranslationHost<V>, cmp: Cmp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match cmp {
        Cmp::ULt => (ctx.solver().try_bvult(a, b), "bv.cmp.ult"),
        Cmp::ULe => (ctx.solver().try_bvule(a, b), "bv.cmp.ule"),
        Cmp::UGt => (ctx.solver().try_bvugt(a, b), "bv.cmp.ugt"),
        Cmp::UGe => (ctx.solver().try_bvuge(a, b), "bv.cmp.uge"),
        Cmp::SLt => (ctx.solver().try_bvslt(a, b), "bv.cmp.slt"),
        Cmp::SLe => (ctx.solver().try_bvsle(a, b), "bv.cmp.sle"),
        Cmp::SGt => (ctx.solver().try_bvsgt(a, b), "bv.cmp.sgt"),
        Cmp::SGe => (ctx.solver().try_bvsge(a, b), "bv.cmp.sge"),
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
        Cmp::ULt => ctx.solver().try_bvult(a, b),
        Cmp::ULe => ctx.solver().try_bvule(a, b),
        Cmp::UGt => ctx.solver().try_bvugt(a, b),
        Cmp::UGe => ctx.solver().try_bvuge(a, b),
        Cmp::SLt => ctx.solver().try_bvslt(a, b),
        Cmp::SLe => ctx.solver().try_bvsle(a, b),
        Cmp::SGt => ctx.solver().try_bvsgt(a, b),
        Cmp::SGe => ctx.solver().try_bvsge(a, b),
    }
}

/// Bitvector addition.
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

/// Bitvector subtraction.
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

/// Bitvector multiplication.
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

/// Unsigned bitvector division.
pub fn udiv<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::UDiv, a, b)
}

/// Fallible [`udiv`].
pub fn try_udiv<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::UDiv, a, b)
}

/// Signed bitvector division.
pub fn sdiv<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::SDiv, a, b)
}

/// Fallible [`sdiv`].
pub fn try_sdiv<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::SDiv, a, b)
}

/// Unsigned bitvector remainder.
pub fn urem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::URem, a, b)
}

/// Fallible [`urem`].
pub fn try_urem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::URem, a, b)
}

/// Signed bitvector remainder.
pub fn srem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::SRem, a, b)
}

/// Fallible [`srem`].
pub fn try_srem<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::SRem, a, b)
}

/// Bitvector bitwise AND.
pub fn and<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::And, a, b)
}

/// Fallible [`and`].
pub fn try_and<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::And, a, b)
}

/// Bitvector bitwise OR.
pub fn or<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Or, a, b)
}

/// Fallible [`or`].
pub fn try_or<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Or, a, b)
}

/// Bitvector bitwise XOR.
pub fn xor<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Xor, a, b)
}

/// Fallible [`xor`].
pub fn try_xor<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Xor, a, b)
}

/// Bitvector shift left.
pub fn shl<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Shl, a, b)
}

/// Fallible [`shl`].
pub fn try_shl<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::Shl, a, b)
}

/// Logical bitvector shift right.
pub fn lshr<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::LShr, a, b)
}

/// Fallible [`lshr`].
pub fn try_lshr<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::LShr, a, b)
}

/// Arithmetic bitvector shift right.
pub fn ashr<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::AShr, a, b)
}

/// Fallible [`ashr`].
pub fn try_ashr<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_binop(ctx, BinOp::AShr, a, b)
}

/// Bitvector bitwise NOT.
pub fn not<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Not, a)
}

/// Fallible [`not`].
pub fn try_not<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    try_unary(ctx, UnaryOp::Not, a)
}

/// Bitvector two's-complement negation.
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

include!("bv/extraction_and_overflow.rs");

#[cfg(test)]
#[path = "bv_tests.rs"]
mod tests;
