// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV (bitvector) evaluation helpers for CHC expression evaluation.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::bv_util::{bv_mask, bv_to_signed};
use crate::smt::SmtValue;
use crate::ChcExpr;

use super::evaluate_expr;

/// Extract a BV value from a subexpression: returns (value, width).
pub(super) fn eval_bv_val(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(u128, u32)> {
    match evaluate_expr(expr, model)? {
        SmtValue::BitVec(v, w) => Some((v, w)),
        _ => None,
    }
}

/// Evaluate a binary BV operation, checking width match.
pub(super) fn eval_bv_binop(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    op: impl FnOnce(u128, u128, u128) -> u128,
) -> Option<SmtValue> {
    let (av, aw) = eval_bv_val(lhs, model)?;
    let (bv, bw) = eval_bv_val(rhs, model)?;
    if aw != bw {
        return None;
    }
    let mask = bv_mask(aw);
    Some(SmtValue::BitVec(op(av, bv, mask) & mask, aw))
}

/// Evaluate a BV comparison, returning Bool.
pub(super) fn eval_bv_cmp(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    cmp: impl FnOnce(u128, u128, u32) -> bool,
) -> Option<SmtValue> {
    let (av, aw) = eval_bv_val(lhs, model)?;
    let (bv, bw) = eval_bv_val(rhs, model)?;
    if aw != bw {
        return None;
    }
    Some(SmtValue::Bool(cmp(av, bv, aw)))
}

/// SMT-LIB bvashr: arithmetic shift right.
pub(super) fn eval_bv_ashr(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    let (av, aw) = eval_bv_val(lhs, model)?;
    let (bv, bw) = eval_bv_val(rhs, model)?;
    if aw != bw {
        return None;
    }
    let signed = bv_to_signed(av, aw);
    let result = if bv >= u128::from(aw) {
        if signed < 0 {
            bv_mask(aw)
        } else {
            0
        }
    } else {
        (signed >> bv) as u128 & bv_mask(aw)
    };
    Some(SmtValue::BitVec(result, aw))
}

/// SMT-LIB bvsdiv: signed division (rounds toward zero).
pub(super) fn eval_bv_signed_div(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    let (av, aw) = eval_bv_val(lhs, model)?;
    let (bv, bw) = eval_bv_val(rhs, model)?;
    if aw != bw {
        return None;
    }
    if bv == 0 {
        // SMT-LIB: bvsdiv by 0 is all-ones if dividend >= 0, 1 if negative
        let sa = bv_to_signed(av, aw);
        return Some(SmtValue::BitVec(if sa >= 0 { bv_mask(aw) } else { 1 }, aw));
    }
    let sa = bv_to_signed(av, aw);
    let sb = bv_to_signed(bv, aw);
    let q = sa.wrapping_div(sb);
    Some(SmtValue::BitVec((q as u128) & bv_mask(aw), aw))
}

/// SMT-LIB bvsmod: signed modulo (result sign matches divisor).
pub(super) fn eval_bv_smod(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    let (av, aw) = eval_bv_val(lhs, model)?;
    let (bv, bw) = eval_bv_val(rhs, model)?;
    if aw != bw {
        return None;
    }
    if bv == 0 {
        return Some(SmtValue::BitVec(av, aw));
    }
    let sa = bv_to_signed(av, aw);
    let sb = bv_to_signed(bv, aw);
    // SMT-LIB smod: result has same sign as divisor
    let rem = sa.wrapping_rem(sb);
    let result = if rem == 0 {
        0i128
    } else if (rem > 0) == (sb > 0) {
        rem
    } else {
        rem.wrapping_add(sb)
    };
    Some(SmtValue::BitVec((result as u128) & bv_mask(aw), aw))
}
