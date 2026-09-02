// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector expression evaluation under partial models.
//!
//! Evaluates BV expressions to concrete `(value, width)` pairs for use in
//! Array MBP index comparison, select-store reduction, and Ackermannization.
//!
//! This helper is deliberately the allocation-free `u128` MBP lane. It returns
//! `None` for zero-width, wider-than-128, or otherwise malformed values. Wide
//! reconstruction and fully concrete evaluation use the canonical BigUint-
//! backed evaluator; BV projection treats `None` as inapplicability and falls
//! back to exact model-value substitution.

use crate::bv_util::{bv_apply_mask, bv_mask, bv_to_signed};
use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::Mbp;

impl Mbp {
    /// Evaluate a bitvector expression under a model.
    /// Returns `(value, width)` where `value` is masked to `width` bits.
    /// Deliberately declines widths outside `1..=128`.
    pub(crate) fn eval_bv(
        &self,
        expr: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(u128, u32)> {
        crate::expr::maybe_grow_expr_stack(|| {
            let _g = crate::expr::ExprDepthGuard::check()?;
            match expr {
                ChcExpr::BitVec(v, w) if *w != 0 && *w <= 128 => Some((bv_apply_mask(*v, *w), *w)),
                ChcExpr::Var(v) => match &v.sort {
                    ChcSort::BitVec(expected_width)
                        if *expected_width != 0 && *expected_width <= 128 =>
                    {
                        match model.get(&v.name) {
                            Some(SmtValue::BitVec(val, w)) if w == expected_width => {
                                Some((bv_apply_mask(*val, *w), *w))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                },
                ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    let cond = self.eval_bool(&args[0], model)?;
                    if cond {
                        self.eval_bv(&args[1], model)
                    } else {
                        self.eval_bv(&args[2], model)
                    }
                }
                ChcExpr::Op(op, args) if args.len() == 2 => {
                    self.eval_bv_binary(op, &args[0], &args[1], model)
                }
                ChcExpr::Op(op, args) if args.len() == 1 => self.eval_bv_unary(op, &args[0], model),
                _ => None,
            }
        })
    }

    /// Evaluate a binary BV operation.
    fn eval_bv_binary(
        &self,
        op: &ChcOp,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(u128, u32)> {
        let (a, wa) = self.eval_bv(lhs, model)?;
        let (b, wb) = self.eval_bv(rhs, model)?;
        if !matches!(op, ChcOp::BvConcat) && wa != wb {
            return None;
        }
        match op {
            ChcOp::BvAdd => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(a.wrapping_add(b), wa), wa))
            }
            ChcOp::BvSub => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(a.wrapping_sub(b), wa), wa))
            }
            ChcOp::BvMul => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(a.wrapping_mul(b), wa), wa))
            }
            ChcOp::BvUDiv => {
                debug_assert_eq!(wa, wb);
                // SMT-LIB: bvudiv by 0 returns all-ones.
                Some((
                    a.checked_div(b)
                        .unwrap_or_else(|| bv_apply_mask(u128::MAX, wa)),
                    wa,
                ))
            }
            ChcOp::BvURem => {
                debug_assert_eq!(wa, wb);
                if b == 0 {
                    Some((a, wa))
                } else {
                    Some((a % b, wa))
                }
            }
            ChcOp::BvSDiv => {
                debug_assert_eq!(wa, wb);
                let sa = bv_to_signed(a, wa);
                let sb = bv_to_signed(b, wb);
                if sb == 0 {
                    // SMT-LIB: bvsdiv by 0 defined as: if a < 0 then 1 else -1
                    let r = if sa < 0 { 1i128 } else { -1i128 };
                    Some((bv_apply_mask(r as u128, wa), wa))
                } else {
                    let q = if (sa < 0) != (sb < 0) {
                        // Different signs: negate the unsigned quotient
                        -(sa.wrapping_abs().wrapping_div(sb.wrapping_abs()))
                    } else {
                        sa.wrapping_abs().wrapping_div(sb.wrapping_abs())
                    };
                    Some((bv_apply_mask(q as u128, wa), wa))
                }
            }
            ChcOp::BvSRem => {
                debug_assert_eq!(wa, wb);
                let sa = bv_to_signed(a, wa);
                let sb = bv_to_signed(b, wb);
                if sb == 0 {
                    Some((a, wa))
                } else {
                    // Sign follows dividend
                    let r = sa.wrapping_rem(sb);
                    Some((bv_apply_mask(r as u128, wa), wa))
                }
            }
            ChcOp::BvSMod => {
                debug_assert_eq!(wa, wb);
                let sa = bv_to_signed(a, wa);
                let sb = bv_to_signed(b, wb);
                if sb == 0 {
                    Some((a, wa))
                } else {
                    // SMT-LIB bvsmod: sign follows divisor
                    let r = sa.wrapping_rem(sb);
                    let m = if r == 0 || (r > 0) == (sb > 0) {
                        r
                    } else {
                        r.wrapping_add(sb)
                    };
                    Some((bv_apply_mask(m as u128, wa), wa))
                }
            }
            ChcOp::BvAnd => {
                debug_assert_eq!(wa, wb);
                Some((a & b, wa))
            }
            ChcOp::BvOr => {
                debug_assert_eq!(wa, wb);
                Some((a | b, wa))
            }
            ChcOp::BvXor => {
                debug_assert_eq!(wa, wb);
                Some((a ^ b, wa))
            }
            ChcOp::BvNand => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(!(a & b), wa), wa))
            }
            ChcOp::BvNor => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(!(a | b), wa), wa))
            }
            ChcOp::BvXnor => {
                debug_assert_eq!(wa, wb);
                Some((bv_apply_mask(!(a ^ b), wa), wa))
            }
            ChcOp::BvShl => {
                debug_assert_eq!(wa, wb);
                if b >= u128::from(wa) {
                    Some((0, wa))
                } else {
                    Some((bv_apply_mask(a << b, wa), wa))
                }
            }
            ChcOp::BvLShr => {
                debug_assert_eq!(wa, wb);
                if b >= u128::from(wa) {
                    Some((0, wa))
                } else {
                    Some((a >> b, wa))
                }
            }
            ChcOp::BvAShr => {
                debug_assert_eq!(wa, wb);
                let sa = bv_to_signed(a, wa);
                if b >= u128::from(wa) {
                    let fill = if sa < 0 {
                        bv_apply_mask(u128::MAX, wa)
                    } else {
                        0
                    };
                    Some((fill, wa))
                } else {
                    Some((bv_apply_mask((sa >> b) as u128, wa), wa))
                }
            }
            ChcOp::BvComp => {
                debug_assert_eq!(wa, wb);
                Some((if a == b { 1 } else { 0 }, 1))
            }
            ChcOp::BvConcat => {
                let total_width = wa.checked_add(wb)?;
                // Can only fold if result fits in u128 (#7040)
                if total_width <= 128 {
                    let shifted = if wb == 128 { 0 } else { a << wb };
                    let result = shifted | b;
                    Some((bv_apply_mask(result, total_width), total_width))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Evaluate a unary BV operation.
    fn eval_bv_unary(
        &self,
        op: &ChcOp,
        arg: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(u128, u32)> {
        match op {
            ChcOp::BvNot => {
                let (v, w) = self.eval_bv(arg, model)?;
                Some((bv_apply_mask(!v, w), w))
            }
            ChcOp::BvNeg => {
                let (v, w) = self.eval_bv(arg, model)?;
                Some((bv_apply_mask(v.wrapping_neg(), w), w))
            }
            ChcOp::BvExtract(hi, lo) => {
                let (v, input_width) = self.eval_bv(arg, model)?;
                if hi < lo || *hi >= input_width {
                    return None;
                }
                let width = hi.checked_sub(*lo)?.checked_add(1)?;
                Some(((v >> *lo) & bv_mask(width), width))
            }
            ChcOp::BvZeroExtend(n) => {
                let (v, w) = self.eval_bv(arg, model)?;
                let new_w = w.checked_add(*n)?;
                (new_w <= 128).then_some((v, new_w))
            }
            ChcOp::BvSignExtend(n) => {
                let (v, w) = self.eval_bv(arg, model)?;
                let new_w = w.checked_add(*n)?;
                if new_w > 128 {
                    return None;
                }
                let sa = bv_to_signed(v, w);
                Some((bv_apply_mask(sa as u128, new_w), new_w))
            }
            ChcOp::BvRotateLeft(n) => {
                let (v, w) = self.eval_bv(arg, model)?;
                if w == 0 || w > 128 {
                    return if w == 0 { Some((0, w)) } else { None };
                }
                let n = n % w;
                if n == 0 {
                    return Some((v, w));
                }
                let rotated = (v << n) | (v >> (w - n));
                Some((bv_apply_mask(rotated, w), w))
            }
            ChcOp::BvRotateRight(n) => {
                let (v, w) = self.eval_bv(arg, model)?;
                if w == 0 || w > 128 {
                    return if w == 0 { Some((0, w)) } else { None };
                }
                let n = n % w;
                if n == 0 {
                    return Some((v, w));
                }
                let rotated = (v >> n) | (v << (w - n));
                Some((bv_apply_mask(rotated, w), w))
            }
            ChcOp::BvRepeat(n) => {
                let (v, w) = self.eval_bv(arg, model)?;
                let total = w.checked_mul(*n)?;
                if *n == 0 || total == 0 || total > 128 {
                    return None;
                }
                let mut result = 0u128;
                for i in 0..*n {
                    result |= v << (i * w);
                }
                Some((bv_apply_mask(result, total), total))
            }
            ChcOp::Bv2Nat => {
                // bv2nat returns a natural number, not a bitvector.
                // This doesn't fit the (u128, u32) return type cleanly,
                // so we decline to evaluate it here.
                None
            }
            _ => None,
        }
    }
}
