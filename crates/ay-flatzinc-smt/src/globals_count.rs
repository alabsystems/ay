// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Count-family global constraint encodings for FlatZinc-to-SMT translation.
// Contains: count_eq, count_neq, count_lt, count_gt, count_leq, count_geq, among.

use ay_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::translate::{Context, SmtInt};

enum CountCompareOrder {
    CountFirst,
    ArgumentFirst,
}

/// Shared helper for all count_* variants: builds the count sum and compares.
///
/// args: [x_array, y, c]
/// `smt_op`: SMT-LIB comparison operator (=, distinct, <, >, <=, >=)
/// `order`: which side receives the computed occurrence count.
fn count_compare(
    ctx: &mut Context,
    args: &[Expr],
    name: &str,
    smt_op: &str,
    order: CountCompareOrder,
) -> Result<(), TranslateError> {
    if args.len() != 3 {
        return Err(TranslateError::WrongArgCount {
            name: name.into(),
            expected: 3,
            got: args.len(),
        });
    }
    let vars = ctx.expr_to_smt_array(&args[0])?;
    let val = ctx.expr_to_smt(&args[1])?;
    let cnt = ctx.expr_to_smt(&args[2])?;

    let occurrence_count = if vars.is_empty() {
        "0".to_string()
    } else {
        let terms: Vec<String> = vars
            .iter()
            .map(|v| format!("(ite (= {v} {val}) 1 0)"))
            .collect();

        if terms.len() == 1 {
            terms[0].clone()
        } else {
            format!("(+ {})", terms.join(" "))
        }
    };

    let (left, right) = match order {
        CountCompareOrder::CountFirst => (occurrence_count.as_str(), cnt.as_str()),
        CountCompareOrder::ArgumentFirst => (cnt.as_str(), occurrence_count.as_str()),
    };

    ctx.emit_fmt(format_args!("(assert ({smt_op} {left} {right}))"));
    Ok(())
}

/// Count-eq: count of x[i] == y equals c.
pub(crate) fn count_eq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(ctx, args, "count_eq", "=", CountCompareOrder::CountFirst)
}

/// Count-neq: count of x[i] == y is not equal to c.
pub(crate) fn count_neq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(
        ctx,
        args,
        "count_neq",
        "distinct",
        CountCompareOrder::CountFirst,
    )
}

/// Count-lt: c is strictly less than count of x[i] == y.
pub(crate) fn count_lt(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(ctx, args, "count_lt", "<", CountCompareOrder::ArgumentFirst)
}

/// Count-gt: c is strictly greater than count of x[i] == y.
pub(crate) fn count_gt(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(ctx, args, "count_gt", ">", CountCompareOrder::ArgumentFirst)
}

/// Count-leq: c is less than or equal to count of x[i] == y.
pub(crate) fn count_leq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(
        ctx,
        args,
        "count_leq",
        "<=",
        CountCompareOrder::ArgumentFirst,
    )
}

/// Count-geq: c is greater than or equal to count of x[i] == y.
pub(crate) fn count_geq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    count_compare(
        ctx,
        args,
        "count_geq",
        ">=",
        CountCompareOrder::ArgumentFirst,
    )
}

/// Among constraint: n = count of elements in x whose value is in set S.
///
/// args: [n, x_array, S_set]
/// Encoding: n = sum_{i} (ite (member x[i] S) 1 0)
pub(crate) fn among(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    if args.len() != 3 {
        return Err(TranslateError::WrongArgCount {
            name: "among".into(),
            expected: 3,
            got: args.len(),
        });
    }
    let n_expr = ctx.expr_to_smt(&args[0])?;
    let vars = ctx.expr_to_smt_array(&args[1])?;
    let vals = ctx.resolve_set(&args[2])?;

    if vars.is_empty() {
        ctx.emit_fmt(format_args!("(assert (= {n_expr} 0))"));
        return Ok(());
    }

    // For each x[i], build membership test over the set of values
    let terms: Vec<String> = vars
        .iter()
        .map(|v| {
            if vals.is_empty() {
                "0".to_string()
            } else if vals.len() == 1 {
                format!("(ite (= {} {}) 1 0)", v, SmtInt(vals[0]))
            } else {
                let disj: Vec<String> = vals
                    .iter()
                    .map(|&s| format!("(= {} {})", v, SmtInt(s)))
                    .collect();
                format!("(ite (or {}) 1 0)", disj.join(" "))
            }
        })
        .collect();

    let sum = if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(+ {})", terms.join(" "))
    };

    ctx.emit_fmt(format_args!("(assert (= {n_expr} {sum}))"));
    Ok(())
}
