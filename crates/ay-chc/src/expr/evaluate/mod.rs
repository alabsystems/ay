// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Evaluation for CHC expressions.
//!
//! Display formatting is in `display.rs`. SmtValue comparison and array
//! evaluation helpers are in `value_ops.rs`.

mod display;
mod eval_bv;
mod value_ops;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ExprDepthGuard};
use crate::bv_util::{bv_mask, bv_to_signed};
use crate::smt::SmtValue;
use eval_bv::{
    eval_bv_ashr, eval_bv_binop, eval_bv_cmp, eval_bv_signed_div, eval_bv_smod, eval_bv_val,
};

pub(crate) use value_ops::{eval_array_select, eval_int_big, eval_real_big};
// Re-export for tests (super::* glob) and internal use.
#[allow(unused_imports)]
pub(super) use value_ops::eval_array_store;
use value_ops::{eval_int_cmp, real_eval_enabled, smt_values_equal};

/// True when both operands are statically integer-sorted.
///
/// Used to route integer (dis)equalities through the widened `i128` evaluator
/// (`eval_int_cmp`) while leaving cross-sort equalities (e.g. the Bool/Int
/// coercion handled by `smt_values_equal`) on the canonical evaluator.
fn both_int_sorted(a: &ChcExpr, b: &ChcExpr) -> bool {
    a.sort() == super::ChcSort::Int && b.sort() == super::ChcSort::Int
}

/// Exact-rational (dis)equality fallback for the LRA lane.
///
/// Called only when the generic [`evaluate_expr`] path abstains on one side of
/// an `=`/`distinct` (typically because a side is a Real arithmetic tree the
/// generic arms do not fold). Both sides are evaluated exactly as
/// [`BigRational`](num_rational::BigRational); `want_eq` selects `=` vs `!=`.
/// Returns `None` (Indeterminate) when either side is not a fully-assigned
/// rational expression, preserving fail-closed behavior.
fn real_eq(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    want_eq: bool,
) -> Option<SmtValue> {
    if !real_eval_enabled() {
        return None;
    }
    let a = eval_real_big(lhs, model)?;
    let b = eval_real_big(rhs, model)?;
    Some(SmtValue::Bool((a == b) == want_eq))
}

fn eval_datatype_selector(
    name: &str,
    arg: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    // The subject only has to be a DATATYPE-SORTED expression that evaluates to
    // a datatype value; restricting it to `Var`/`FuncApp` made a selector over a
    // `select`, an `ite` or any other datatype-valued term indeterminate even
    // when the model decides it. The `SmtValue::Datatype` requirement below is
    // what keeps this exact.
    let super::ChcSort::Datatype { constructors, .. } = arg.sort() else {
        return None;
    };
    let SmtValue::Datatype(active_ctor, fields) = evaluate_expr(arg, model)? else {
        return None;
    };

    for ctor in constructors.iter() {
        if let Some((field_idx, _)) = ctor
            .selectors
            .iter()
            .enumerate()
            .find(|(_, selector)| selector.name == name)
        {
            if active_ctor == ctor.name {
                return fields.get(field_idx).cloned();
            }
            return None;
        }
    }

    None
}

fn eval_datatype_func_app(
    name: &str,
    sort: &super::ChcSort,
    args: &[Arc<ChcExpr>],
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if let super::ChcSort::Datatype { constructors, .. } = sort {
        for ctor in constructors.iter() {
            if ctor.name == name && ctor.selectors.len() == args.len() {
                let fields = args
                    .iter()
                    .map(|arg| evaluate_expr(arg, model))
                    .collect::<Option<Vec<_>>>()?;
                return Some(SmtValue::Datatype(name.to_string(), fields));
            }
        }
    }

    if args.len() == 1 {
        let arg = args[0].as_ref();

        if let Some(rest) = name.strip_prefix("is-") {
            let SmtValue::Datatype(active_ctor, _) = evaluate_expr(arg, model)? else {
                return None;
            };
            return Some(SmtValue::Bool(active_ctor == rest));
        }

        if let Some(selector_value) = eval_datatype_selector(name, arg, model) {
            return Some(selector_value);
        }
    }

    None
}

/// Evaluate a CHC expression to an `SmtValue` under the given model.
///
/// Returns `None` when evaluation is indeterminate (missing variable,
/// unsupported operation like arrays/predicates, or arithmetic overflow).
/// Uses checked arithmetic and SMT-LIB Euclidean division/remainder semantics.
///
/// This is the single canonical evaluator for `ChcExpr`; all call sites in
/// PDR verification, model verification, and cube extraction delegate here.
pub(crate) fn evaluate_expr(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    maybe_grow_expr_stack(|| {
        ExprDepthGuard::check()?;
        match expr {
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
            ChcExpr::BitVec(val, width) => Some(SmtValue::BitVec(*val & bv_mask(*width), *width)),
            // Real literal `num/den` → exact rational. Previously absent, so a
            // bare Real constant evaluated to `None` (Indeterminate); the LRA
            // model verifier could not validate any Real atom (#LRA-Lin gap).
            ChcExpr::Real(num, den) if *den != 0 && real_eval_enabled() => Some(SmtValue::Real(
                num_rational::BigRational::new((*num).into(), (*den).into()),
            )),
            ChcExpr::Var(v) => model.get(&v.name).cloned(),

            // Boolean connectives
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(b) => Some(SmtValue::Bool(!b)),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::And, args) => {
                let mut all_determined = true;
                for arg in args {
                    match evaluate_expr(arg, model) {
                        Some(SmtValue::Bool(false)) => return Some(SmtValue::Bool(false)),
                        Some(SmtValue::Bool(true)) => {}
                        _ => all_determined = false,
                    }
                }
                if all_determined {
                    Some(SmtValue::Bool(true))
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut all_determined = true;
                for arg in args {
                    match evaluate_expr(arg, model) {
                        Some(SmtValue::Bool(true)) => return Some(SmtValue::Bool(true)),
                        Some(SmtValue::Bool(false)) => {}
                        _ => all_determined = false,
                    }
                }
                if all_determined {
                    Some(SmtValue::Bool(false))
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(SmtValue::Bool(false)), _) => Some(SmtValue::Bool(true)),
                    (_, Some(SmtValue::Bool(true))) => Some(SmtValue::Bool(true)),
                    (Some(SmtValue::Bool(true)), Some(SmtValue::Bool(false))) => {
                        Some(SmtValue::Bool(false))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(SmtValue::Bool(a)), Some(SmtValue::Bool(b))) => {
                        Some(SmtValue::Bool(a == b))
                    }
                    _ => None,
                }
            }

            // Comparisons (integer)
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Integer-sorted equalities go through the widened i128 evaluator
                // (see eval_int_cmp) so equalities against parser-encoded large
                // integer literals are decided correctly. Cross-sort / non-integer
                // operands fall back to smt_values_equal (Bool/Int coercion, etc.).
                if both_int_sorted(&args[0], &args[1]) {
                    return eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_eq);
                }
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(a), Some(b)) => Some(SmtValue::Bool(smt_values_equal(&a, &b)?)),
                    // Real (LRA) lane: an operand is a Real arithmetic tree the
                    // generic evaluator cannot fold to a value. Compare exactly
                    // as rationals. Reached only when the generic path abstains.
                    _ => real_eq(&args[0], &args[1], model, true),
                }
            }
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                if both_int_sorted(&args[0], &args[1]) {
                    return eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_ne);
                }
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(a), Some(b)) => Some(SmtValue::Bool(!smt_values_equal(&a, &b)?)),
                    _ => real_eq(&args[0], &args[1], model, false),
                }
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_lt)
            }
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_le)
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_gt)
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_ge)
            }

            // Arithmetic
            ChcExpr::Op(ChcOp::Add, args) => {
                // i128-lockstep: checked i128 arithmetic; overflow beyond i128
                // still degrades to None (Indeterminate), never wraps.
                let mut sum: i128 = 0;
                for arg in args {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => sum = sum.checked_add(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(sum))
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = match evaluate_expr(&args[0], model)? {
                    SmtValue::Int(n) => n,
                    _ => return None,
                };
                if args.len() == 1 {
                    return first.checked_neg().map(SmtValue::Int);
                }
                let mut result = first;
                for arg in &args[1..] {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => result = result.checked_sub(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(result))
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product: i128 = 1;
                for arg in args {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => product = product.checked_mul(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(product))
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Int(n) => n.checked_neg().map(SmtValue::Int),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model)?,
                    evaluate_expr(&args[1], model)?,
                ) {
                    (SmtValue::Int(_), SmtValue::Int(0)) => {
                        // SMT-LIB total semantics: (div x 0) = 0
                        // Must match eliminate_mod (eliminate.rs).
                        Some(SmtValue::Int(0))
                    }
                    (SmtValue::Int(a), SmtValue::Int(b)) => {
                        // SMT-LIB div is Euclidean (remainder always non-negative)
                        a.checked_div_euclid(b).map(SmtValue::Int)
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model)?,
                    evaluate_expr(&args[1], model)?,
                ) {
                    (SmtValue::Int(a), SmtValue::Int(0)) => {
                        // SMT-LIB total semantics: (mod x 0) = x
                        // Must match eliminate_mod (eliminate.rs).
                        Some(SmtValue::Int(a))
                    }
                    (SmtValue::Int(a), SmtValue::Int(b)) => {
                        a.checked_rem_euclid(b).map(SmtValue::Int)
                    }
                    _ => None,
                }
            }

            // ITE
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(true) => evaluate_expr(&args[1], model),
                    SmtValue::Bool(false) => evaluate_expr(&args[2], model),
                    _ => None,
                }
            }

            // BV arithmetic
            ChcExpr::Op(ChcOp::BvAdd, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| a.wrapping_add(b) & m)
            }
            ChcExpr::Op(ChcOp::BvSub, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| a.wrapping_sub(b) & m)
            }
            ChcExpr::Op(ChcOp::BvMul, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| a.wrapping_mul(b) & m)
            }
            ChcExpr::Op(ChcOp::BvUDiv, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| {
                    a.checked_div(b).unwrap_or(m)
                })
            }
            ChcExpr::Op(ChcOp::BvURem, args) if args.len() == 2 => eval_bv_binop(
                &args[0],
                &args[1],
                model,
                |a, b, _m| {
                    if b == 0 {
                        a
                    } else {
                        a % b
                    }
                },
            ),
            ChcExpr::Op(ChcOp::BvSDiv, args) if args.len() == 2 => {
                eval_bv_signed_div(&args[0], &args[1], model)
            }
            ChcExpr::Op(ChcOp::BvSRem, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_val(&args[0], model)?;
                let (bv, bw) = eval_bv_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                if bv == 0 {
                    return Some(SmtValue::BitVec(av, aw));
                }
                let sa = bv_to_signed(av, aw);
                let sb = bv_to_signed(bv, aw);
                let r = sa.wrapping_rem(sb);
                Some(SmtValue::BitVec((r as u128) & bv_mask(aw), aw))
            }
            ChcExpr::Op(ChcOp::BvSMod, args) if args.len() == 2 => {
                eval_bv_smod(&args[0], &args[1], model)
            }
            ChcExpr::Op(ChcOp::BvNeg, args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                Some(SmtValue::BitVec((!v).wrapping_add(1) & bv_mask(w), w))
            }

            // BV bitwise
            ChcExpr::Op(ChcOp::BvAnd, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, _| a & b)
            }
            ChcExpr::Op(ChcOp::BvOr, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, _| a | b)
            }
            ChcExpr::Op(ChcOp::BvXor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, _| a ^ b)
            }
            ChcExpr::Op(ChcOp::BvNand, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| (!(a & b)) & m)
            }
            ChcExpr::Op(ChcOp::BvNor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| (!(a | b)) & m)
            }
            ChcExpr::Op(ChcOp::BvXnor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, |a, b, m| (!(a ^ b)) & m)
            }
            ChcExpr::Op(ChcOp::BvNot, args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                Some(SmtValue::BitVec((!v) & bv_mask(w), w))
            }

            // BV shifts
            ChcExpr::Op(ChcOp::BvShl, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_val(&args[0], model)?;
                let (bv, bw) = eval_bv_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                let result = if bv >= u128::from(aw) {
                    0
                } else {
                    (av << bv) & bv_mask(aw)
                };
                Some(SmtValue::BitVec(result, aw))
            }
            ChcExpr::Op(ChcOp::BvLShr, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_val(&args[0], model)?;
                let (bv, bw) = eval_bv_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                let result = if bv >= u128::from(aw) { 0 } else { av >> bv };
                Some(SmtValue::BitVec(result, aw))
            }
            ChcExpr::Op(ChcOp::BvAShr, args) if args.len() == 2 => {
                eval_bv_ashr(&args[0], &args[1], model)
            }

            // BV unsigned comparisons
            ChcExpr::Op(ChcOp::BvULt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, _| a < b)
            }
            ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, _| a <= b)
            }
            ChcExpr::Op(ChcOp::BvUGt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, _| a > b)
            }
            ChcExpr::Op(ChcOp::BvUGe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, _| a >= b)
            }

            // BV signed comparisons
            ChcExpr::Op(ChcOp::BvSLt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, w| {
                    bv_to_signed(a, w) < bv_to_signed(b, w)
                })
            }
            ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, w| {
                    bv_to_signed(a, w) <= bv_to_signed(b, w)
                })
            }
            ChcExpr::Op(ChcOp::BvSGt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, w| {
                    bv_to_signed(a, w) > bv_to_signed(b, w)
                })
            }
            ChcExpr::Op(ChcOp::BvSGe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, |a, b, w| {
                    bv_to_signed(a, w) >= bv_to_signed(b, w)
                })
            }

            // BV comp (1-bit equality)
            ChcExpr::Op(ChcOp::BvComp, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_val(&args[0], model)?;
                let (bv, bw) = eval_bv_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                Some(SmtValue::BitVec(if av == bv { 1 } else { 0 }, 1))
            }

            // BV concat
            ChcExpr::Op(ChcOp::BvConcat, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_val(&args[0], model)?;
                let (bv, bw) = eval_bv_val(&args[1], model)?;
                let new_w = aw + bw;
                if new_w > 128 {
                    return None;
                }
                let result = (av << bw) | bv;
                Some(SmtValue::BitVec(result & bv_mask(new_w), new_w))
            }

            // BV extract
            ChcExpr::Op(ChcOp::BvExtract(hi, lo), args) if args.len() == 1 => {
                let (v, _w) = eval_bv_val(&args[0], model)?;
                let new_w = hi - lo + 1;
                let result = (v >> lo) & bv_mask(new_w);
                Some(SmtValue::BitVec(result, new_w))
            }

            // BV zero_extend
            ChcExpr::Op(ChcOp::BvZeroExtend(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                let new_w = w + n;
                if new_w > 128 {
                    return None;
                }
                Some(SmtValue::BitVec(v, new_w))
            }

            // BV sign_extend
            ChcExpr::Op(ChcOp::BvSignExtend(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                let new_w = w + n;
                if new_w > 128 {
                    return None;
                }
                let signed = bv_to_signed(v, w);
                Some(SmtValue::BitVec((signed as u128) & bv_mask(new_w), new_w))
            }

            // BV rotate
            ChcExpr::Op(ChcOp::BvRotateLeft(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                if w == 0 {
                    return Some(SmtValue::BitVec(0, w));
                }
                let rot = n % w;
                let result = ((v << rot) | (v >> (w - rot))) & bv_mask(w);
                Some(SmtValue::BitVec(result, w))
            }
            ChcExpr::Op(ChcOp::BvRotateRight(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                if w == 0 {
                    return Some(SmtValue::BitVec(0, w));
                }
                let rot = n % w;
                let result = ((v >> rot) | (v << (w - rot))) & bv_mask(w);
                Some(SmtValue::BitVec(result, w))
            }

            // BV repeat
            ChcExpr::Op(ChcOp::BvRepeat(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_val(&args[0], model)?;
                let new_w = w * n;
                if new_w > 128 {
                    return None;
                }
                let mut result = 0u128;
                for i in 0..*n {
                    result |= v << (i * w);
                }
                Some(SmtValue::BitVec(result & bv_mask(new_w), new_w))
            }

            // BV/Int conversions
            ChcExpr::Op(ChcOp::Bv2Nat, args) if args.len() == 1 => {
                let (v, _w) = eval_bv_val(&args[0], model)?;
                // i128-lockstep: fail-closed for bv values beyond i128 range.
                i128::try_from(v).ok().map(SmtValue::Int)
            }
            ChcExpr::Op(ChcOp::Int2Bv(w), args) if args.len() == 1 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Int(n) => Some(SmtValue::BitVec((n as u128) & bv_mask(*w), *w)),
                    _ => None,
                }
            }

            // Array select: select(arr, idx) → look up idx in array value
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let arr_val = evaluate_expr(&args[0], model)?;
                let idx_val = evaluate_expr(&args[1], model)?;
                eval_array_select(&arr_val, &idx_val)
            }

            // Array store: store(arr, idx, val) → insert/overwrite in array value
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let arr_val = evaluate_expr(&args[0], model)?;
                let idx_val = evaluate_expr(&args[1], model)?;
                let elem_val = evaluate_expr(&args[2], model)?;
                Some(eval_array_store(arr_val, idx_val, elem_val))
            }

            // Constant array: ((as const (Array K V)) val)
            ChcExpr::ConstArray(_key_sort, val) => {
                let v = evaluate_expr(val, model)?;
                Some(SmtValue::ConstArray(Box::new(v)))
            }

            ChcExpr::FuncApp(name, sort, args) => eval_datatype_func_app(name, sort, args, model),

            // Predicates, functions, etc. - cannot evaluate
            _ => None,
        }
    })
}

#[cfg(test)]
mod tests;
