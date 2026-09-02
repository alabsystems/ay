// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV (bitvector) evaluation helpers for CHC expression evaluation.

use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::bv_util::{bv_mask, bv_to_signed};
use crate::smt::SmtValue;
use crate::ChcExpr;

use super::evaluate_expr;

#[derive(Clone, Copy)]
pub(super) enum BvBinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    URem,
    And,
    Or,
    Xor,
    Nand,
    Nor,
    Xnor,
}

#[derive(Clone, Copy)]
pub(super) enum BvCmpOp {
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

pub(super) fn big_bv_modulus(width: u32) -> BigUint {
    BigUint::one() << width
}

pub(super) fn bigint_to_bv(value: BigInt, width: u32) -> BigUint {
    if width == 0 {
        return BigUint::zero();
    }
    let modulus = BigInt::from_biguint(Sign::Plus, big_bv_modulus(width));
    let mut reduced = value % &modulus;
    if reduced.is_negative() {
        reduced += modulus;
    }
    let Some(unsigned) = reduced.to_biguint() else {
        unreachable!("a reduced bitvector residue must be non-negative");
    };
    unsigned
}

fn bv_to_signed_big(value: BigUint, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::zero();
    }
    let modulus = big_bv_modulus(width);
    let sign_bit = BigUint::one() << (width - 1);
    if (&value & sign_bit).is_zero() {
        BigInt::from(value)
    } else {
        BigInt::from(value) - BigInt::from(modulus)
    }
}

fn exact_bitvec_operands(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(BigUint, BigUint, u32)> {
    let (lhs, lhs_width) = eval_bv_big_val(lhs, model)?;
    let (rhs, rhs_width) = eval_bv_big_val(rhs, model)?;
    (lhs_width == rhs_width).then_some((lhs, rhs, lhs_width))
}

/// Extract a BV value from a subexpression: returns (value, width).
pub(super) fn eval_bv_val(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(u128, u32)> {
    match evaluate_expr(expr, model)? {
        SmtValue::BitVec(v, w) if w != 0 && w <= 128 => Some((v & bv_mask(w), w)),
        _ => None,
    }
}

/// Extract an exact BV value from a subexpression.
///
/// This is intentionally separate from [`eval_bv_val`]: the common <=128-bit
/// arithmetic lane stays on `u128`, while exact wide operations opt into
/// `BigUint` explicitly.
pub(super) fn eval_bv_big_val(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(BigUint, u32)> {
    let (value, width) = evaluate_expr(expr, model)?.bitvec_to_biguint()?;
    (width != 0 && width <= crate::MAX_BITVECTOR_WIDTH).then_some((value, width))
}

/// Evaluate a binary BV operation, checking width match.
pub(super) fn eval_bv_binop(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    op: BvBinOp,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
        if aw != bw {
            return None;
        }
        let mask = bv_mask(aw);
        let value = match op {
            BvBinOp::Add => av.wrapping_add(bv),
            BvBinOp::Sub => av.wrapping_sub(bv),
            BvBinOp::Mul => av.wrapping_mul(bv),
            BvBinOp::UDiv => av.checked_div(bv).unwrap_or(mask),
            BvBinOp::URem => {
                if bv == 0 {
                    av
                } else {
                    av % bv
                }
            }
            BvBinOp::And => av & bv,
            BvBinOp::Or => av | bv,
            BvBinOp::Xor => av ^ bv,
            BvBinOp::Nand => !(av & bv),
            BvBinOp::Nor => !(av | bv),
            BvBinOp::Xnor => !(av ^ bv),
        };
        return Some(SmtValue::BitVec(value & mask, aw));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    let mask = big_bv_modulus(width) - BigUint::one();
    let value = match op {
        BvBinOp::Add => av + bv,
        BvBinOp::Sub => {
            if av >= bv {
                av - bv
            } else {
                big_bv_modulus(width) - (bv - av)
            }
        }
        BvBinOp::Mul => av * bv,
        BvBinOp::UDiv => {
            if bv.is_zero() {
                mask.clone()
            } else {
                av / bv
            }
        }
        BvBinOp::URem => {
            if bv.is_zero() {
                av
            } else {
                av % bv
            }
        }
        BvBinOp::And => av & bv,
        BvBinOp::Or => av | bv,
        BvBinOp::Xor => av ^ bv,
        BvBinOp::Nand => mask ^ (av & bv),
        BvBinOp::Nor => mask ^ (av | bv),
        BvBinOp::Xnor => mask ^ (av ^ bv),
    };
    Some(SmtValue::bitvec_from_biguint(value, width))
}

/// Evaluate a BV comparison, returning Bool.
pub(super) fn eval_bv_cmp(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    op: BvCmpOp,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
        if aw != bw {
            return None;
        }
        let result = match op {
            BvCmpOp::Ult => av < bv,
            BvCmpOp::Ule => av <= bv,
            BvCmpOp::Ugt => av > bv,
            BvCmpOp::Uge => av >= bv,
            BvCmpOp::Slt => bv_to_signed(av, aw) < bv_to_signed(bv, aw),
            BvCmpOp::Sle => bv_to_signed(av, aw) <= bv_to_signed(bv, aw),
            BvCmpOp::Sgt => bv_to_signed(av, aw) > bv_to_signed(bv, aw),
            BvCmpOp::Sge => bv_to_signed(av, aw) >= bv_to_signed(bv, aw),
        };
        return Some(SmtValue::Bool(result));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    let result = match op {
        BvCmpOp::Ult => av < bv,
        BvCmpOp::Ule => av <= bv,
        BvCmpOp::Ugt => av > bv,
        BvCmpOp::Uge => av >= bv,
        BvCmpOp::Slt => bv_to_signed_big(av, width) < bv_to_signed_big(bv, width),
        BvCmpOp::Sle => bv_to_signed_big(av, width) <= bv_to_signed_big(bv, width),
        BvCmpOp::Sgt => bv_to_signed_big(av, width) > bv_to_signed_big(bv, width),
        BvCmpOp::Sge => bv_to_signed_big(av, width) >= bv_to_signed_big(bv, width),
    };
    Some(SmtValue::Bool(result))
}

/// SMT-LIB bvashr: arithmetic shift right.
pub(super) fn eval_bv_ashr(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
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
        return Some(SmtValue::BitVec(result, aw));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    let signed = bv_to_signed_big(av, width);
    let result = if bv >= BigUint::from(width) {
        if signed.is_negative() {
            big_bv_modulus(width) - BigUint::one()
        } else {
            BigUint::zero()
        }
    } else {
        bigint_to_bv(signed >> bv.to_u32()?, width)
    };
    Some(SmtValue::bitvec_from_biguint(result, width))
}

/// SMT-LIB bvsdiv: signed division (rounds toward zero).
pub(super) fn eval_bv_signed_div(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
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
        return Some(SmtValue::BitVec((q as u128) & bv_mask(aw), aw));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    let sa = bv_to_signed_big(av, width);
    let sb = bv_to_signed_big(bv, width);
    let result = if sb.is_zero() {
        if sa.is_negative() {
            BigUint::one()
        } else {
            big_bv_modulus(width) - BigUint::one()
        }
    } else {
        bigint_to_bv(sa / sb, width)
    };
    Some(SmtValue::bitvec_from_biguint(result, width))
}

/// SMT-LIB bvsrem: signed remainder (result sign matches dividend).
pub(super) fn eval_bv_signed_rem(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
        if aw != bw {
            return None;
        }
        if bv == 0 {
            return Some(SmtValue::BitVec(av, aw));
        }
        let result = bv_to_signed(av, aw).wrapping_rem(bv_to_signed(bv, aw));
        return Some(SmtValue::BitVec((result as u128) & bv_mask(aw), aw));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    if bv.is_zero() {
        return Some(SmtValue::bitvec_from_biguint(av, width));
    }
    let result = bv_to_signed_big(av, width) % bv_to_signed_big(bv, width);
    Some(SmtValue::bitvec_from_biguint(
        bigint_to_bv(result, width),
        width,
    ))
}

/// SMT-LIB bvsmod: signed modulo (result sign matches divisor).
pub(super) fn eval_bv_smod(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if let (Some((av, aw)), Some((bv, bw))) = (eval_bv_val(lhs, model), eval_bv_val(rhs, model)) {
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
        return Some(SmtValue::BitVec((result as u128) & bv_mask(aw), aw));
    }

    let (av, bv, width) = exact_bitvec_operands(lhs, rhs, model)?;
    if bv.is_zero() {
        return Some(SmtValue::bitvec_from_biguint(av, width));
    }
    let sa = bv_to_signed_big(av, width);
    let sb = bv_to_signed_big(bv, width);
    // SMT-LIB smod: result has same sign as divisor
    let rem = &sa % &sb;
    let result = if rem.is_zero() || rem.is_positive() == sb.is_positive() {
        rem
    } else {
        rem + sb
    };
    Some(SmtValue::bitvec_from_biguint(
        bigint_to_bv(result, width),
        width,
    ))
}
