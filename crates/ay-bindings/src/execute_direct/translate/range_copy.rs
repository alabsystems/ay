// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compact range-copy lowering; all five operands precede the fresh binder.
//! Existing builders/read-over-lambda reduction and result validation remain
//! authoritative. This legacy direct route is not original-owner accounting.

use super::*;

pub(super) fn translate(ctx: &mut ExecutionContext, expr: &Expr) -> Result<Term, ExecuteError> {
    let ExprValue::ArrayRangeCopy {
        dst,
        src,
        lo,
        hi,
        src_start,
    } = expr.value()
    else {
        return Err(ExecuteError::Internal(
            "expected range-copy expression".to_owned(),
        ));
    };
    if expr.sort() != dst.sort()
        || dst.sort() != src.sort()
        || dst
            .sort()
            .array_sort()
            .is_none_or(|array| array.index_sort.bitvec_width() != Some(64))
        || [lo, hi, src_start]
            .iter()
            .any(|bound| bound.sort().bitvec_width() != Some(64))
    {
        return Err(ExecuteError::ExprTranslation(
            "range-copy array/bound sorts differ".to_owned(),
        ));
    }
    let dst = translate_expr(ctx, dst)?;
    let src = translate_expr(ctx, src)?;
    let lo = translate_expr(ctx, lo)?;
    let hi = translate_expr(ctx, hi)?;
    let src_start = translate_expr(ctx, src_start)?;
    // A fresh native Var is excluded from declared_variables/model extraction.
    let index = expr_solver_op(
        ctx.solver.try_fresh_var("ay_range_i", ApiSort::bitvec(64)),
        "fresh_var",
    )?;
    let after_start = expr_solver_op(ctx.solver.try_bvule(lo, index), "bvule")?;
    let before_end = expr_solver_op(ctx.solver.try_bvult(index, hi), "bvult")?;
    let inside = expr_solver_op(ctx.solver.try_and(after_start, before_end), "and")?;
    let relative = expr_solver_op(ctx.solver.try_bvsub(index, lo), "bvsub")?;
    let source_index = expr_solver_op(ctx.solver.try_bvadd(relative, src_start), "bvadd")?;
    let source_value = expr_solver_op(ctx.solver.try_select(src, source_index), "select")?;
    let old_value = expr_solver_op(ctx.solver.try_select(dst, index), "select")?;
    let body = expr_solver_op(ctx.solver.try_ite(inside, source_value, old_value), "ite")?;
    Ok(ctx.solver.lambda_array(index, body))
}
