// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, width-modular bitvector semantics for the independent gate.
//!
//! All values are kept as non-negative `BigInt` normalized into `[0, 2^width)`.
//! Every operation matches SMT-LIB `FixedSizeBitVectors` semantics, including
//! the total division/remainder rules (no `Unevaluable` for BV div/rem — they
//! are fully defined, with `bvudiv x 0 = all-ones` and `bvurem x 0 = x`).

use crate::{pow2, ModelValue};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

/// Normalize a value into `[0, 2^width)`.
pub(crate) fn normalize(v: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::zero();
    }
    let m = pow2(width);
    let r = v % &m;
    if r.sign() == num_bigint::Sign::Minus {
        r + &m
    } else {
        r
    }
}

/// All-ones mask for `width` bits: `2^width - 1`.
fn mask(width: u32) -> BigInt {
    pow2(width) - BigInt::one()
}

/// Interpret a normalized unsigned value as a two's-complement signed integer.
fn to_signed(v: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::zero();
    }
    let half = pow2(width - 1);
    if *v >= half {
        v - pow2(width)
    } else {
        v.clone()
    }
}

/// The most-significant (sign) bit.
fn sign_bit(v: &BigInt, width: u32) -> bool {
    width > 0 && *v >= pow2(width - 1)
}

/// Decode a [`ModelValue::BitVec`] into `(value, width)`.
fn as_bv(v: &ModelValue) -> Result<(BigInt, u32), String> {
    match v {
        ModelValue::BitVec { width, value } => Ok((value.clone(), *width)),
        _ => Err("expected a bitvector operand".to_string()),
    }
}

fn bv(value: BigInt, width: u32) -> ModelValue {
    ModelValue::BitVec {
        width,
        value: normalize(&value, width),
    }
}

/// Saturating shift amount in bit units (clamped to `width`, since any shift of
/// at least `width` produces a fully-shifted result).
fn shift_amount(b: &BigInt, width: u32) -> usize {
    b.to_usize()
        .map_or(width as usize, |s| s.min(width as usize))
}

/// Evaluate a named bitvector operator (non-indexed).
pub(crate) fn eval_named(name: &str, args: &[ModelValue]) -> Result<ModelValue, String> {
    // Comparison and a few mixed-result ops are handled before the
    // "both operands same-width" binary group.
    match name {
        "bvnot" => {
            let (a, w) = as_bv(arg(args, 0)?)?;
            return Ok(bv(mask(w) - a, w));
        }
        "bvneg" => {
            let (a, w) = as_bv(arg(args, 0)?)?;
            return Ok(bv(pow2(w) - a, w));
        }
        "bv2nat" => {
            let (a, _) = as_bv(arg(args, 0)?)?;
            return Ok(ModelValue::Int(a));
        }
        "concat" => {
            // Left-to-right: high bits first.
            let mut acc = BigInt::zero();
            let mut total = 0u32;
            for a in args {
                let (v, w) = as_bv(a)?;
                acc = (acc << (w as usize)) + v;
                total += w;
            }
            return Ok(bv(acc, total));
        }
        "bvcomp" => {
            let (a, w1) = as_bv(arg(args, 0)?)?;
            let (b, w2) = as_bv(arg(args, 1)?)?;
            if w1 != w2 {
                return Err("bvcomp width mismatch".to_string());
            }
            return Ok(bv(
                if a == b {
                    BigInt::one()
                } else {
                    BigInt::zero()
                },
                1,
            ));
        }
        _ => {}
    }

    // Unsigned/signed comparison predicates → Bool.
    if let Some(pred) = compare(name) {
        let (a, w1) = as_bv(arg(args, 0)?)?;
        let (b, w2) = as_bv(arg(args, 1)?)?;
        if w1 != w2 {
            return Err("bv comparison width mismatch".to_string());
        }
        return Ok(ModelValue::Bool(pred(&a, &b, w1)));
    }

    // Binary same-width arithmetic/bitwise/shift ops.
    let (a, w1) = as_bv(arg(args, 0)?)?;
    let (b, w2) = as_bv(arg(args, 1)?)?;
    if w1 != w2 {
        return Err(format!("bv op {name} width mismatch ({w1} vs {w2})"));
    }
    let w = w1;
    let result = match name {
        "bvadd" => &a + &b,
        "bvsub" => &a - &b,
        "bvmul" => &a * &b,
        "bvand" => &a & &b,
        "bvor" => &a | &b,
        "bvxor" => &a ^ &b,
        "bvnand" => mask(w) - (&a & &b),
        "bvnor" => mask(w) - (&a | &b),
        "bvxnor" => mask(w) - (&a ^ &b),
        "bvudiv" => {
            if b.is_zero() {
                mask(w) // SMT-LIB: division by zero is all-ones.
            } else {
                &a / &b
            }
        }
        "bvurem" => {
            if b.is_zero() {
                a.clone() // SMT-LIB: remainder by zero is the dividend.
            } else {
                &a % &b
            }
        }
        "bvshl" => &a << shift_amount(&b, w),
        "bvlshr" => &a >> shift_amount(&b, w),
        "bvashr" => {
            // Arithmetic shift: BigInt `>>` on a negative value rounds toward
            // -inf, i.e. sign-extends; normalizing back gives the BV result.
            let s = to_signed(&a, w);
            s >> shift_amount(&b, w)
        }
        "bvsdiv" => return Ok(bv(bvsdiv(&a, &b, w), w)),
        "bvsrem" => return Ok(bv(bvsrem(&a, &b, w), w)),
        "bvsmod" => return Ok(bv(bvsmod(&a, &b, w), w)),
        _ => return Err(format!("unsupported bitvector operator {name}")),
    };
    Ok(bv(result, w))
}

/// Evaluate an indexed bitvector operator, e.g. `(_ extract h l)`.
pub(crate) fn eval_indexed(
    name: &str,
    indices: &[u32],
    args: &[ModelValue],
) -> Result<ModelValue, String> {
    match name {
        "extract" => {
            if indices.len() != 2 {
                return Err("extract needs 2 indices".to_string());
            }
            let (high, low) = (indices[0], indices[1]);
            if high < low {
                return Err("extract high < low".to_string());
            }
            let (a, w) = as_bv(arg(args, 0)?)?;
            if high >= w {
                return Err("extract index out of range".to_string());
            }
            let out_w = high - low + 1;
            let shifted = &a >> (low as usize);
            Ok(bv(shifted & mask(out_w), out_w))
        }
        "zero_extend" => {
            let i = idx0(indices)?;
            let (a, w) = as_bv(arg(args, 0)?)?;
            Ok(bv(a, w + i))
        }
        "sign_extend" => {
            let i = idx0(indices)?;
            let (a, w) = as_bv(arg(args, 0)?)?;
            // Sign-extend by re-normalizing the signed value at the new width.
            Ok(bv(to_signed(&a, w), w + i))
        }
        "rotate_left" => {
            let i = idx0(indices)?;
            let (a, w) = as_bv(arg(args, 0)?)?;
            Ok(rotate(&a, w, i, true))
        }
        "rotate_right" => {
            let i = idx0(indices)?;
            let (a, w) = as_bv(arg(args, 0)?)?;
            Ok(rotate(&a, w, i, false))
        }
        "repeat" => {
            let i = idx0(indices)?;
            if i == 0 {
                return Err("repeat count 0".to_string());
            }
            let (a, w) = as_bv(arg(args, 0)?)?;
            let mut acc = BigInt::zero();
            for _ in 0..i {
                acc = (acc << (w as usize)) + &a;
            }
            Ok(bv(acc, w * i))
        }
        "int2bv" => {
            let width = idx0(indices)?;
            match arg(args, 0)? {
                ModelValue::Int(n) => Ok(bv(n.clone(), width)),
                _ => Err("int2bv expects an integer operand".to_string()),
            }
        }
        _ => Err(format!("unsupported indexed bitvector operator {name}")),
    }
}

fn rotate(a: &BigInt, width: u32, by: u32, left: bool) -> ModelValue {
    if width == 0 {
        return bv(BigInt::zero(), 0);
    }
    let r = (by % width) as usize;
    if r == 0 {
        return bv(a.clone(), width);
    }
    let w = width as usize;
    let rotated = if left {
        (a << r) | (a >> (w - r))
    } else {
        (a >> r) | (a << (w - r))
    };
    bv(rotated & mask(width), width)
}

type BvPred = fn(&BigInt, &BigInt, u32) -> bool;

fn compare(name: &str) -> Option<BvPred> {
    let f: BvPred = match name {
        "bvult" => |a, b, _| a < b,
        "bvule" => |a, b, _| a <= b,
        "bvugt" => |a, b, _| a > b,
        "bvuge" => |a, b, _| a >= b,
        "bvslt" => |a, b, w| to_signed(a, w) < to_signed(b, w),
        "bvsle" => |a, b, w| to_signed(a, w) <= to_signed(b, w),
        "bvsgt" => |a, b, w| to_signed(a, w) > to_signed(b, w),
        "bvsge" => |a, b, w| to_signed(a, w) >= to_signed(b, w),
        _ => return None,
    };
    Some(f)
}

// --- signed division family (SMT-LIB definitions) -------------------------

fn bvsdiv(a: &BigInt, b: &BigInt, w: u32) -> BigInt {
    let msb_a = sign_bit(a, w);
    let msb_b = sign_bit(b, w);
    let neg = |x: &BigInt| normalize(&(pow2(w) - x), w);
    let udiv = |x: &BigInt, y: &BigInt| {
        if y.is_zero() {
            mask(w)
        } else {
            x / y
        }
    };
    match (msb_a, msb_b) {
        (false, false) => udiv(a, b),
        (true, false) => neg(&udiv(&neg(a), b)),
        (false, true) => neg(&udiv(a, &neg(b))),
        (true, true) => udiv(&neg(a), &neg(b)),
    }
}

fn bvsrem(a: &BigInt, b: &BigInt, w: u32) -> BigInt {
    let msb_a = sign_bit(a, w);
    let msb_b = sign_bit(b, w);
    let neg = |x: &BigInt| normalize(&(pow2(w) - x), w);
    let urem = |x: &BigInt, y: &BigInt| {
        if y.is_zero() {
            x.clone()
        } else {
            x % y
        }
    };
    match (msb_a, msb_b) {
        (false, false) => urem(a, b),
        (true, false) => neg(&urem(&neg(a), b)),
        (false, true) => urem(a, &neg(b)),
        (true, true) => neg(&urem(&neg(a), &neg(b))),
    }
}

fn bvsmod(a: &BigInt, b: &BigInt, w: u32) -> BigInt {
    let msb_a = sign_bit(a, w);
    let msb_b = sign_bit(b, w);
    let neg = |x: &BigInt| normalize(&(pow2(w) - x), w);
    let abs_a = if msb_a { neg(a) } else { a.clone() };
    let abs_b = if msb_b { neg(b) } else { b.clone() };
    let u = if abs_b.is_zero() {
        abs_a.clone()
    } else {
        &abs_a % &abs_b
    };
    if u.is_zero() {
        return BigInt::zero();
    }
    match (msb_a, msb_b) {
        (false, false) => u,
        (true, false) => normalize(&(neg(&u) + b), w),
        (false, true) => normalize(&(u + b), w),
        (true, true) => neg(&u),
    }
}

// --- small helpers --------------------------------------------------------

fn arg(args: &[ModelValue], i: usize) -> Result<&ModelValue, String> {
    args.get(i)
        .ok_or_else(|| "bitvector operator: missing argument".to_string())
}

fn idx0(indices: &[u32]) -> Result<u32, String> {
    indices
        .first()
        .copied()
        .ok_or_else(|| "indexed bitvector operator: missing index".to_string())
}
