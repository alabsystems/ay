// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn eval_app(
    terms: &TermStore,
    sym: &Symbol,
    args: &[TermId],
    env: &[(TermId, EvalValue)],
) -> Option<EvalValue> {
    // Indexed BV ops (extract / zero_extend / sign_extend) carry their indices in
    // the symbol, so dispatch on them before the name-based match below.
    if let Symbol::Indexed(name, indices) = sym {
        return eval_indexed_bv(terms, name, indices, args, env);
    }
    let name = sym.name();
    match name {
        "=" if args.len() == 2 => Some(EvalValue::Bool(
            eval_term(terms, args[0], env)? == eval_term(terms, args[1], env)?,
        )),
        "or" => {
            let mut any_true = false;
            for &arg in args {
                any_true |= eval_bool_term(terms, arg, env)?;
            }
            Some(EvalValue::Bool(any_true))
        }
        "and" => {
            let mut all_true = true;
            for &arg in args {
                all_true &= eval_bool_term(terms, arg, env)?;
            }
            Some(EvalValue::Bool(all_true))
        }
        "bvnot" if args.len() == 1 => {
            let (value, width) = eval_bv_arg(terms, args[0], env)?;
            Some(EvalValue::BitVec {
                value: (!value) & bv_mask(width),
                width,
            })
        }
        "bvneg" if args.len() == 1 => {
            let (value, width) = eval_bv_arg(terms, args[0], env)?;
            Some(EvalValue::BitVec {
                value: value.wrapping_neg() & bv_mask(width),
                width,
            })
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            if args.len() == 2 =>
        {
            let (lhs, rhs, width) = eval_same_width_bv_args(terms, args, env)?;
            let (sl, sr) = (to_signed_u64(lhs, width), to_signed_u64(rhs, width));
            let result = match name {
                "bvult" => lhs < rhs,
                "bvule" => lhs <= rhs,
                "bvugt" => lhs > rhs,
                "bvuge" => lhs >= rhs,
                "bvslt" => sl < sr,
                "bvsle" => sl <= sr,
                "bvsgt" => sl > sr,
                "bvsge" => sl >= sr,
                _ => unreachable!("guarded by match arm"),
            };
            Some(EvalValue::Bool(result))
        }
        _ => eval_app_bv(terms, name, args, env),
    }
}

fn eval_app_bv(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    env: &[(TermId, EvalValue)],
) -> Option<EvalValue> {
    match name {
        "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvadd" | "bvsub"
        | "bvmul" | "bvudiv" | "bvurem"
            if args.len() == 2 =>
        {
            let (lhs, rhs, width) = eval_same_width_bv_args(terms, args, env)?;
            let value = match name {
                "bvand" => lhs & rhs,
                "bvor" => lhs | rhs,
                "bvxor" => lhs ^ rhs,
                "bvnand" => !(lhs & rhs),
                "bvnor" => !(lhs | rhs),
                "bvxnor" => !(lhs ^ rhs),
                "bvadd" => lhs.wrapping_add(rhs),
                "bvsub" => lhs.wrapping_sub(rhs),
                "bvmul" => lhs.wrapping_mul(rhs),
                // SMT-LIB makes unsigned division/remainder TOTAL: dividing by
                // zero yields all-ones (bvudiv) / the dividend (bvurem).
                "bvudiv" => lhs.checked_div(rhs).unwrap_or_else(|| bv_mask(width)),
                "bvurem" => lhs.checked_rem(rhs).unwrap_or(lhs),
                _ => unreachable!("guarded by match arm"),
            } & bv_mask(width);
            Some(EvalValue::BitVec { value, width })
        }
        "bvsdiv" | "bvsrem" | "bvsmod" if args.len() == 2 => {
            let (lhs, rhs, width) = eval_same_width_bv_args(terms, args, env)?;
            Some(EvalValue::BitVec {
                value: eval_bv_signed_divrem(name, lhs, rhs, width),
                width,
            })
        }
        "bvshl" | "bvlshr" | "bvashr" if args.len() == 2 => {
            let (lhs, rhs, width) = eval_same_width_bv_args(terms, args, env)?;
            Some(EvalValue::BitVec {
                value: eval_bv_shift(name, lhs, rhs, width),
                width,
            })
        }
        "concat" if args.len() == 2 => {
            // SMT-LIB `(concat hi lo)`: first arg is the high part, second the low.
            let (hi, hi_width) = eval_bv_arg(terms, args[0], env)?;
            let (lo, lo_width) = eval_bv_arg(terms, args[1], env)?;
            let width = hi_width.checked_add(lo_width)?;
            if hi_width == 0 || lo_width == 0 || width > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            // `hi_width >= 1` and `width <= 64` keep `lo_width < 64`, so the
            // shift never declines for an evaluated term.
            let high = hi.checked_shl(lo_width)?;
            Some(EvalValue::BitVec {
                value: (high | lo) & bv_mask(width),
                width,
            })
        }
        _ => None,
    }
}
