// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc integer multiplication, division, and modulo translations.

use ay_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::translate::{smt_int, Context, VarDomain};

#[derive(Clone, Copy)]
enum IntDivResult {
    Quotient,
    Remainder,
}

/// `constraint op(a, b, r)` → `(assert (= r (op a b)))` for Int-typed results.
pub(super) fn ternary_func(
    ctx: &mut Context,
    args: &[Expr],
    op: &str,
) -> Result<(), TranslateError> {
    check_args(op, args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (= {r} ({op} {a} {b})))"));
    Ok(())
}

pub(super) fn int_div(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    int_div_mod(ctx, args, IntDivResult::Quotient)
}

pub(super) fn int_mod(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    int_div_mod(ctx, args, IntDivResult::Remainder)
}

/// FlatZinc integer division truncates toward zero, unlike SMT-LIB `div` on
/// negative operands. Division by zero is undefined in FlatZinc but total in
/// SMT-LIB, so it must be excluded explicitly.
fn int_div_mod(
    ctx: &mut Context,
    args: &[Expr],
    result_kind: IntDivResult,
) -> Result<(), TranslateError> {
    let name = match result_kind {
        IntDivResult::Quotient => "int_div",
        IntDivResult::Remainder => "int_mod",
    };
    check_args(name, args, 3)?;
    let dividend = ctx.expr_to_smt(&args[0])?;
    let divisor = ctx.expr_to_smt(&args[1])?;
    let result = ctx.expr_to_smt(&args[2])?;

    ctx.emit_fmt(format_args!("(assert (not (= {divisor} 0)))"));

    let abs_dividend = format!("(ite (>= {dividend} 0) {dividend} (- {dividend}))");
    let abs_divisor = format!("(ite (>= {divisor} 0) {divisor} (- {divisor}))");
    let magnitude = format!("(div {abs_dividend} {abs_divisor})");
    let quotient =
        format!("(ite (= (>= {dividend} 0) (>= {divisor} 0)) {magnitude} (- {magnitude}))");
    match result_kind {
        IntDivResult::Quotient => {
            ctx.emit_fmt(format_args!("(assert (= {result} {quotient}))"));
        }
        IntDivResult::Remainder => {
            ctx.emit_fmt(format_args!(
                "(assert (= {result} (- {dividend} (* {quotient} {divisor}))))"
            ));
        }
    }
    Ok(())
}

/// Maximum domain size for linearizing `int_times(a, b, r)`.
/// When one operand has at most this many values, the product is encoded as
/// an ITE chain over its domain, avoiding QF_NIA.
pub(super) const LINEARIZE_DOMAIN_LIMIT: i64 = 32;

/// `int_times(a, b, r)` — linearize when one operand has a small bounded domain.
///
/// If operand `a` has domain `{v1, v2, ..., vk}` with k ≤ LINEARIZE_DOMAIN_LIMIT,
/// emit: `r = ite(a = v1, v1*b, ite(a = v2, v2*b, ... vk*b ...))`.
/// This keeps the logic in QF_LIA instead of QF_NIA.
pub(super) fn int_times(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_times", args, 3)?;

    // Try to find a small-domain operand for linearization.
    let small_domain = expr_small_domain(ctx, &args[0]);
    let (case_values, case_idx) = match &small_domain {
        Some(vals) if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize => (vals.clone(), 0usize),
        _ => {
            let other = expr_small_domain(ctx, &args[1]);
            match other {
                Some(vals) if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize => (vals, 1usize),
                _ => {
                    // Both operands have large/unknown domains — fall back to nonlinear `*`.
                    return ternary_func(ctx, args, "*");
                }
            }
        }
    };

    let other_idx = 1 - case_idx;
    let case_var = ctx.expr_to_smt(&args[case_idx])?;
    let other_var = ctx.expr_to_smt(&args[other_idx])?;
    let r = ctx.expr_to_smt(&args[2])?;

    // Build ITE chain: ite(case_var = v1, v1*other, ite(case_var = v2, v2*other, ...))
    let Some(ite_expr) = build_linear_ite(&case_var, &other_var, &case_values) else {
        ctx.emit("(assert false)");
        return Ok(());
    };

    ctx.emit_fmt(format_args!("(assert (= {r} {ite_expr}))"));
    Ok(())
}

/// Build an ITE chain: `ite(x=v1, v1*y, ite(x=v2, v2*y, ... vk*y))`.
fn build_linear_ite(case_var: &str, other_var: &str, values: &[i64]) -> Option<String> {
    let (&last, preceding) = values.split_last()?;
    let mut result = linear_product_term(last, other_var);
    for &v in preceding.iter().rev() {
        let prod = linear_product_term(v, other_var);
        result = format!(
            "(ite (= {case_var} {val}) {prod} {result})",
            val = smt_int(v)
        );
    }
    Some(result)
}

/// Generate a linear product term `v * other` as an SMT expression.
fn linear_product_term(v: i64, other_var: &str) -> String {
    match v {
        0 => "0".to_string(),
        1 => other_var.to_string(),
        -1 => format!("(- {other_var})"),
        _ => format!("(* {} {other_var})", smt_int(v)),
    }
}

/// Get the domain values for an expression if it refers to a variable with a small
/// bounded domain. Returns None for non-variables or large/unbounded domains.
fn expr_small_domain(ctx: &Context, expr: &Expr) -> Option<Vec<i64>> {
    let name = match expr {
        Expr::Ident(name) => name.as_str(),
        _ => return None,
    };
    match ctx.var_domains.get(name)? {
        VarDomain::Bool => Some(vec![0, 1]),
        VarDomain::IntRange(lo, hi) => {
            let size = hi.checked_sub(*lo)?.checked_add(1)?;
            if size > 0 && size <= LINEARIZE_DOMAIN_LIMIT {
                Some((*lo..=*hi).collect())
            } else {
                None
            }
        }
        VarDomain::IntSet(vals) => {
            if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize {
                Some(vals.clone())
            } else {
                None
            }
        }
        VarDomain::IntUnbounded => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{build_linear_ite, int_times};
    use crate::translate::{Context, Sort, VarDomain};
    use ay_flatzinc_parser::ast::Expr;

    #[test]
    fn empty_linear_ite_is_rejected_without_panicking() {
        assert!(build_linear_ite("x", "y", &[]).is_none());

        let mut ctx = Context::new();
        for name in ["x", "y", "r"] {
            ctx.scalar_vars
                .insert(name.to_string(), (name.to_string(), Sort::Int));
        }
        ctx.var_domains
            .insert("x".to_string(), VarDomain::IntSet(Vec::new()));
        let args = ["x", "y", "r"].map(|name| Expr::Ident(name.to_string()));

        int_times(&mut ctx, &args).expect("empty domain is a valid unsatisfiable translation");

        assert_eq!(ctx.output, "(assert false)\n");
    }
}
