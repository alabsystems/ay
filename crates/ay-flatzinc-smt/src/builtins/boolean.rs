// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc Boolean constraint translations to SMT-LIB2

use ay_flatzinc_parser::ast::Expr;

use super::check_args;
use crate::error::TranslateError;
use crate::translate::Context;

/// `bool_op(a, b, r)` → iff decomposition for Bool-typed results
pub(super) fn ternary_bool_func(
    ctx: &mut Context,
    args: &[Expr],
    op: &str,
) -> Result<(), TranslateError> {
    check_args(op, args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} ({op} {a} {b})))"));
    ctx.emit_fmt(format_args!("(assert (=> ({op} {a} {b}) {r}))"));
    Ok(())
}

/// `bool_not(a, b)` → iff decomposition: `b => (not a)` ∧ `(not a) => b`
pub(super) fn bool_not(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("bool_not", args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert (=> {b} (not {a})))"));
    ctx.emit_fmt(format_args!("(assert (=> (not {a}) {b}))"));
    Ok(())
}

/// `bool_clause(pos, neg)` → `(assert (or pos... (not neg)...))`
pub(super) fn bool_clause(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("bool_clause", args, 2)?;
    let pos = ctx.expr_to_smt_array(&args[0])?;
    let neg = ctx.expr_to_smt_array(&args[1])?;
    let mut terms = pos;
    for n in &neg {
        terms.push(format!("(not {n})"));
    }
    if terms.is_empty() {
        ctx.emit("(assert false)");
    } else if terms.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", terms[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", terms.join(" ")));
    }
    Ok(())
}

/// `array_bool_and(bs, r)` → iff decomposition: `r => (and bs)` ∧ `(and bs) => r`
///
/// r is true iff all elements of bs are true.
pub(super) fn array_bool_and(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_and", args, 2)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    let r = ctx.expr_to_smt(&args[1])?;
    if bs.is_empty() {
        // Conjunction of empty set is vacuously true
        ctx.emit_fmt(format_args!("(assert {r})"));
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert (=> {r} {}))", bs[0]));
        ctx.emit_fmt(format_args!("(assert (=> {} {r}))", bs[0]));
    } else {
        let conjunction = format!("(and {})", bs.join(" "));
        ctx.emit_fmt(format_args!("(assert (=> {r} {conjunction}))"));
        ctx.emit_fmt(format_args!("(assert (=> {conjunction} {r}))"));
    }
    Ok(())
}

/// `array_bool_or(bs, r)` → iff decomposition: `r => (or bs)` ∧ `(or bs) => r`
///
/// r is true iff at least one element of bs is true.
pub(super) fn array_bool_or(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_or", args, 2)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    let r = ctx.expr_to_smt(&args[1])?;
    if bs.is_empty() {
        // Disjunction of empty set is false
        ctx.emit_fmt(format_args!("(assert (not {r}))"));
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert (=> {r} {}))", bs[0]));
        ctx.emit_fmt(format_args!("(assert (=> {} {r}))", bs[0]));
    } else {
        let disjunction = format!("(or {})", bs.join(" "));
        ctx.emit_fmt(format_args!("(assert (=> {r} {disjunction}))"));
        ctx.emit_fmt(format_args!("(assert (=> {disjunction} {r}))"));
    }
    Ok(())
}

/// `array_bool_xor(bs)` → parity constraint (odd number of elements true)
///
/// Uses chained binary xor since SMT-LIB `xor` is binary.
pub(super) fn array_bool_xor(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_xor", args, 1)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    if bs.is_empty() {
        // xor of empty set is false → constraint is unsatisfiable
        ctx.emit("(assert false)");
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", bs[0]));
    } else {
        // Chain binary xor: (xor b1 (xor b2 (... bN)))
        let mut expr = bs[bs.len() - 1].clone();
        for i in (0..bs.len() - 1).rev() {
            expr = format!("(xor {} {expr})", bs[i]);
        }
        ctx.emit_fmt(format_args!("(assert {expr})"));
    }
    Ok(())
}
