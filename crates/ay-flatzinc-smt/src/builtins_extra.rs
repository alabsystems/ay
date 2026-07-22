// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Extended built-in FlatZinc constraint handlers: linear sums, exponentiation,
// and reified variants. Split from builtins.rs to keep files under 500 lines.

use ay_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::translate::{Context, SmtInt};

// --- Integer exponentiation ---

/// `int_pow(a, b, r)` → r = a^b (integer exponentiation)
///
/// SMT-LIB2 has no native power operator. Encoding:
/// - If b is a known constant, unroll to repeated multiplication.
/// - If b is a variable, build an ite chain over its domain.
pub(crate) fn int_pow(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_pow", args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let r = ctx.expr_to_smt(&args[2])?;

    // Try to resolve b as a constant first (literal or parameter)
    if let Ok(exp) = ctx.resolve_int(&args[1]) {
        let pow_expr = build_pow_expr(&a, exp);
        ctx.emit_fmt(format_args!("(assert (= {r} {pow_expr}))"));
        return Ok(());
    }

    // b is a variable: build ite chain over its domain
    let b = ctx.expr_to_smt(&args[1])?;
    let range = exponent_range(ctx, &args[1]);
    let mut ite_expr = String::from("1"); // fallback for out-of-range
    for exp in range.rev() {
        let pow_val = build_pow_expr(&a, exp);
        ite_expr = format!("(ite (= {b} {}) {pow_val} {ite_expr})", SmtInt(exp));
    }
    ctx.emit_fmt(format_args!("(assert (= {r} {ite_expr}))"));
    Ok(())
}

/// Build the SMT expression for base^exp using repeated multiplication.
fn build_pow_expr(base: &str, exp: i64) -> String {
    match exp {
        0 => "1".to_string(),
        1 => base.to_string(),
        n if n < 0 => "0".to_string(), // integer division: a^(-n) rounds to 0
        _ => {
            let mut expr = base.to_string();
            for _ in 1..exp {
                expr = format!("(* {base} {expr})");
            }
            expr
        }
    }
}

/// Determine the range of exponent values for the ite chain.
/// Uses the variable's domain if available, otherwise defaults to 0..=16.
fn exponent_range(ctx: &Context, expr: &Expr) -> std::ops::RangeInclusive<i64> {
    if let Expr::Ident(name) = expr {
        if let Some(domain) = ctx.var_domains.get(name) {
            match domain {
                crate::translate::VarDomain::IntRange(lo, hi) => {
                    let lo = (*lo).max(0); // negative exponents → 0 in int
                    let hi = (*hi).min(64); // cap at 64 to avoid huge expressions
                    return lo..=hi;
                }
                crate::translate::VarDomain::IntSet(values) => {
                    if let (Some(&lo), Some(&hi)) = (values.first(), values.last()) {
                        let lo = lo.max(0);
                        let hi = hi.min(64);
                        return lo..=hi;
                    }
                }
                _ => {}
            }
        }
    }
    0..=16 // reasonable default for unbounded exponents
}

// --- Linear sum constraints ---

/// Build a linear sum: `(+ (* c1 x1) (* c2 x2) ...)`
pub(crate) fn build_linear_sum(
    ctx: &Context,
    coeffs_expr: &Expr,
    vars_expr: &Expr,
) -> Result<String, TranslateError> {
    let cs = ctx.resolve_int_array(coeffs_expr)?;
    let xs = ctx.expr_to_smt_array(vars_expr)?;
    let terms: Vec<String> = cs
        .iter()
        .zip(xs.iter())
        .filter_map(|(c, x)| match *c {
            0 => None,
            1 => Some(x.clone()),
            -1 => Some(format!("(- {x})")),
            _ => Some(format!("(* {} {x})", SmtInt(*c))),
        })
        .collect();
    match terms.len() {
        0 => Ok("0".into()),
        1 => Ok(terms[0].clone()),
        _ => Ok(format!("(+ {})", terms.join(" "))),
    }
}

/// `int_lin_eq/le(cs, xs, k)` → `(assert (op sum k))`
pub(crate) fn int_lin(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args("int_lin_*", args, 3)?;
    let sum = build_linear_sum(ctx, &args[0], &args[1])?;
    let k = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert ({op} {sum} {k}))"));
    Ok(())
}

/// `int_lin_ne(cs, xs, k)` → `(assert (not (= sum k)))`
pub(crate) fn int_lin_ne(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_lin_ne", args, 3)?;
    let sum = build_linear_sum(ctx, &args[0], &args[1])?;
    let k = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (not (= {sum} {k})))"));
    Ok(())
}

/// Build a boolean linear sum: `(+ (* c1 (ite b1 1 0)) ...)`
fn build_bool_linear_sum(
    ctx: &Context,
    coeffs_expr: &Expr,
    bools_expr: &Expr,
) -> Result<String, TranslateError> {
    let cs = ctx.resolve_int_array(coeffs_expr)?;
    let bs = ctx.expr_to_smt_array(bools_expr)?;
    let terms: Vec<String> = cs
        .iter()
        .zip(bs.iter())
        .filter_map(|(c, b)| {
            if *c == 0 {
                return None;
            }
            let b_int = format!("(ite {b} 1 0)");
            match *c {
                1 => Some(b_int),
                -1 => Some(format!("(- {b_int})")),
                _ => Some(format!("(* {} {b_int})", SmtInt(*c))),
            }
        })
        .collect();
    match terms.len() {
        0 => Ok("0".into()),
        1 => Ok(terms[0].clone()),
        _ => Ok(format!("(+ {})", terms.join(" "))),
    }
}

/// `bool_lin_eq/le(cs, bs, k)` → `(assert (op sum k))`
pub(crate) fn bool_lin(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args("bool_lin_*", args, 3)?;
    let sum = build_bool_linear_sum(ctx, &args[0], &args[1])?;
    let k = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert ({op} {sum} {k}))"));
    Ok(())
}

// --- Reified variants ---

/// `op_reif(a, b, r)` → iff decomposition: `r => (op a b)` ∧ `(op a b) => r`
///
/// Uses two implications instead of `(= r (op a b))` to work around ay
/// model validation failures on `(= Bool Bool)` patterns (see #273 blocker).
pub(crate) fn reified_binary(
    ctx: &mut Context,
    args: &[Expr],
    op: &str,
) -> Result<(), TranslateError> {
    check_args("*_reif", args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} ({op} {a} {b})))"));
    ctx.emit_fmt(format_args!("(assert (=> ({op} {a} {b}) {r}))"));
    Ok(())
}

/// `ne_reif(a, b, r)` → iff decomposition: `r => (not (op a b))` ∧ `(not (op a b)) => r`
pub(crate) fn reified_binary_neg(
    ctx: &mut Context,
    args: &[Expr],
    op: &str,
) -> Result<(), TranslateError> {
    check_args("*_reif", args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} (not ({op} {a} {b}))))"));
    ctx.emit_fmt(format_args!("(assert (=> (not ({op} {a} {b})) {r}))"));
    Ok(())
}

/// `int_lin_eq_reif / int_lin_le_reif(cs, xs, k, r)` → iff decomposition for reified linear
pub(crate) fn int_lin_reif(
    ctx: &mut Context,
    args: &[Expr],
    op: &str,
) -> Result<(), TranslateError> {
    check_args("int_lin_*_reif", args, 4)?;
    let sum = build_linear_sum(ctx, &args[0], &args[1])?;
    let k = ctx.expr_to_smt(&args[2])?;
    let r = ctx.expr_to_smt(&args[3])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} ({op} {sum} {k})))"));
    ctx.emit_fmt(format_args!("(assert (=> ({op} {sum} {k}) {r}))"));
    Ok(())
}

/// `int_lin_ne_reif(cs, xs, k, r)` → iff decomposition for reified linear not-equal
pub(crate) fn int_lin_ne_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_lin_ne_reif", args, 4)?;
    let sum = build_linear_sum(ctx, &args[0], &args[1])?;
    let k = ctx.expr_to_smt(&args[2])?;
    let r = ctx.expr_to_smt(&args[3])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} (not (= {sum} {k}))))"));
    ctx.emit_fmt(format_args!("(assert (=> (not (= {sum} {k})) {r}))"));
    Ok(())
}

/// `set_in_reif(x, S, r)` → iff decomposition for reified set membership
pub(crate) fn set_in_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in_reif", args, 3)?;
    // Check if second arg is a set variable (boolean decomposition)
    if let Expr::Ident(name) = &args[1] {
        if ctx.set_vars.contains_key(name) {
            return crate::set_constraints::set_in_reif_var(ctx, args);
        }
    }
    let x = ctx.expr_to_smt(&args[0])?;
    let values = ctx.resolve_set(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    if values.is_empty() {
        // Empty set: r is always false (no iff needed)
        ctx.emit_fmt(format_args!("(assert (not {r}))"));
    } else if values.len() == 1 {
        let membership = format!("(= {x} {})", SmtInt(values[0]));
        ctx.emit_fmt(format_args!("(assert (=> {r} {membership}))"));
        ctx.emit_fmt(format_args!("(assert (=> {membership} {r}))"));
    } else {
        let disjuncts: Vec<String> = values
            .iter()
            .map(|v| format!("(= {x} {})", SmtInt(*v)))
            .collect();
        let membership = format!("(or {})", disjuncts.join(" "));
        ctx.emit_fmt(format_args!("(assert (=> {r} {membership}))"));
        ctx.emit_fmt(format_args!("(assert (=> {membership} {r}))"));
    }
    Ok(())
}
