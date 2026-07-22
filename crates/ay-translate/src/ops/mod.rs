// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator builder modules.

use std::hash::Hash;

pub use ay_dpll::api::SolverError;
use ay_dpll::api::Term;

use crate::TranslationHost;

pub mod arith;
pub mod array;
pub mod bv;
pub mod dt;
pub mod fp;
pub mod seq;
pub mod string;
pub mod uf;

/// Unwrap a fallible solver call, treating the error as a programmer invariant violation.
///
/// The `try_*` builders on `Solver` fail only when the caller passed malformed terms
/// (mismatched sorts, unknown term IDs, wrong logic). For well-formed translator input
/// these are invariant violations — programmer bugs, not runtime errors — so
/// `.unwrap_or_else(|e| panic!("invariant: ..."))` is the appropriate failure mode.
/// `rust_excellence.md` permits `.expect("invariant: ...")`-style invariant panics.
///
/// Callers that must recover from malformed input — e.g. external-facing bridges that
/// validate user SMT-LIB input — must use the fallible `try_*` variants of these
/// builders (added in #8851) which propagate `SolverError` directly.
#[allow(clippy::panic)] // invariant violation: see doc comment
pub(crate) fn expect_result<T>(result: Result<T, SolverError>, operation: &'static str) -> T {
    result.unwrap_or_else(|e| {
        panic!("invariant: ay-translate {operation} called with malformed input: {e}")
    })
}

/// N-ary boolean operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaryBoolOp {
    And,
    Or,
}

/// Comparison operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comparison {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// N-ary boolean builder. Panics on malformed input; see [`try_bool_nary`] for the
/// fallible variant.
pub fn bool_nary<V>(ctx: &mut impl TranslationHost<V>, op: NaryBoolOp, terms: &[Term]) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match op {
        NaryBoolOp::And => (ctx.solver().try_and_many(terms), "bool_nary.and"),
        NaryBoolOp::Or => (ctx.solver().try_or_many(terms), "bool_nary.or"),
    };
    expect_result(result, tag)
}

/// Fallible [`bool_nary`] returning a `SolverError` instead of panicking.
pub fn try_bool_nary<V>(
    ctx: &mut impl TranslationHost<V>,
    op: NaryBoolOp,
    terms: &[Term],
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match op {
        NaryBoolOp::And => ctx.solver().try_and_many(terms),
        NaryBoolOp::Or => ctx.solver().try_or_many(terms),
    }
}

/// Boolean negation. Panics on malformed input; see [`try_bool_not`] for the fallible variant.
pub fn bool_not<V>(ctx: &mut impl TranslationHost<V>, t: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_bool_not(ctx, t), "bool_not")
}

/// Fallible [`bool_not`] returning a `SolverError` instead of panicking.
pub fn try_bool_not<V>(ctx: &mut impl TranslationHost<V>, t: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_not(t)
}

/// Boolean implication. Panics on malformed input; see [`try_implies`] for the fallible variant.
pub fn implies<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_implies(ctx, a, b), "implies")
}

/// Fallible [`implies`] returning a `SolverError` instead of panicking.
pub fn try_implies<V>(
    ctx: &mut impl TranslationHost<V>,
    a: Term,
    b: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_implies(a, b)
}

/// If-then-else. Panics on malformed input; see [`try_ite`] for the fallible variant.
pub fn ite<V>(ctx: &mut impl TranslationHost<V>, cond: Term, then_: Term, else_: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_ite(ctx, cond, then_, else_), "ite")
}

/// Fallible [`ite`] returning a `SolverError` instead of panicking.
pub fn try_ite<V>(
    ctx: &mut impl TranslationHost<V>,
    cond: Term,
    then_: Term,
    else_: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_ite(cond, then_, else_)
}

/// Boolean exclusive-or. Panics on malformed input; see [`try_xor`] for the fallible variant.
pub fn xor<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_xor(ctx, a, b), "xor")
}

/// Fallible [`xor`] returning a `SolverError` instead of panicking.
pub fn try_xor<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_xor(a, b)
}

/// Comparison builder. Panics on malformed input; see [`try_compare`] for the fallible variant.
pub fn compare<V>(
    ctx: &mut impl TranslationHost<V>,
    cmp: Comparison,
    left: Term,
    right: Term,
) -> Term
where
    V: Eq + Hash,
{
    let (result, tag) = match cmp {
        Comparison::Lt => (ctx.solver().try_lt(left, right), "compare.lt"),
        Comparison::Le => (ctx.solver().try_le(left, right), "compare.le"),
        Comparison::Gt => (ctx.solver().try_gt(left, right), "compare.gt"),
        Comparison::Ge => (ctx.solver().try_ge(left, right), "compare.ge"),
        Comparison::Eq => (ctx.solver().try_eq(left, right), "compare.eq"),
        Comparison::Ne => (ctx.solver().try_neq(left, right), "compare.ne"),
    };
    expect_result(result, tag)
}

/// Fallible [`compare`] returning a `SolverError` instead of panicking.
pub fn try_compare<V>(
    ctx: &mut impl TranslationHost<V>,
    cmp: Comparison,
    left: Term,
    right: Term,
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    match cmp {
        Comparison::Lt => ctx.solver().try_lt(left, right),
        Comparison::Le => ctx.solver().try_le(left, right),
        Comparison::Gt => ctx.solver().try_gt(left, right),
        Comparison::Ge => ctx.solver().try_ge(left, right),
        Comparison::Eq => ctx.solver().try_eq(left, right),
        Comparison::Ne => ctx.solver().try_neq(left, right),
    }
}

/// Distinct (pairwise disequality) builder. Panics on malformed input; see [`try_distinct`]
/// for the fallible variant.
pub fn distinct<V>(ctx: &mut impl TranslationHost<V>, terms: &[Term]) -> Term
where
    V: Eq + Hash,
{
    expect_result(try_distinct(ctx, terms), "distinct")
}

/// Fallible [`distinct`] returning a `SolverError` instead of panicking.
pub fn try_distinct<V>(
    ctx: &mut impl TranslationHost<V>,
    terms: &[Term],
) -> Result<Term, SolverError>
where
    V: Eq + Hash,
{
    ctx.solver().try_distinct(terms)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "ops_tests.rs"]
mod tests;
