// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The operations of [`super`]: arithmetic, conversions and the IEEE
//! remainder, each on exact rationals with one final rounding.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

use super::Value;
use super::{
    decode, encode, order, round, round_magnitude_to_integer, round_signed, same_format, Fmt, Val,
};
use crate::RoundingMode;

fn signed(neg: bool, q: &BigRational) -> BigRational {
    if neg {
        -q.clone()
    } else {
        q.clone()
    }
}

fn zero(neg: bool) -> Val {
    Val::Fin(neg, BigRational::zero())
}

/// The sign of an exact zero sum of two operands whose signs are `a` and `b`
/// (IEEE 754 §6.3): their common sign, else `-` only toward negative.
fn zero_sum_sign(rm: RoundingMode, a: bool, b: bool) -> bool {
    if a == b {
        a
    } else {
        rm == RoundingMode::RTN
    }
}

fn add_val(f: Fmt, rm: RoundingMode, a: &Val, b: &Val) -> Val {
    match (a, b) {
        (Val::Nan, _) | (_, Val::Nan) => Val::Nan,
        (Val::Inf(x), Val::Inf(y)) if x != y => Val::Nan,
        (Val::Inf(x), _) => Val::Inf(*x),
        (_, Val::Inf(y)) => Val::Inf(*y),
        (Val::Fin(an, aq), Val::Fin(bn, bq)) => {
            let x = signed(*an, aq) + signed(*bn, bq);
            if !x.is_zero() {
                round_signed(f, rm, &x)
            } else if aq.is_zero() && bq.is_zero() {
                zero(zero_sum_sign(rm, *an, *bn))
            } else {
                // An exact cancellation of nonzero operands.
                zero(rm == RoundingMode::RTN)
            }
        }
    }
}

fn mul_val(f: Fmt, rm: RoundingMode, a: &Val, b: &Val) -> Val {
    let (an, bn) = match (a, b) {
        (Val::Nan, _) | (_, Val::Nan) => return Val::Nan,
        (Val::Inf(an) | Val::Fin(an, _), Val::Inf(bn) | Val::Fin(bn, _)) => (*an, *bn),
    };
    let s = an ^ bn;
    match (a, b) {
        (Val::Inf(_), Val::Fin(_, q)) | (Val::Fin(_, q), Val::Inf(_)) if q.is_zero() => Val::Nan,
        (Val::Inf(_), _) | (_, Val::Inf(_)) => Val::Inf(s),
        (Val::Fin(_, aq), Val::Fin(_, bq)) => {
            let product = aq * bq;
            if product.is_zero() {
                zero(s)
            } else {
                round(f, rm, s, &product)
            }
        }
        _ => Val::Nan,
    }
}

fn div_val(f: Fmt, rm: RoundingMode, a: &Val, b: &Val) -> Val {
    let (an, bn) = match (a, b) {
        (Val::Nan, _) | (_, Val::Nan) => return Val::Nan,
        (Val::Inf(an) | Val::Fin(an, _), Val::Inf(bn) | Val::Fin(bn, _)) => (*an, *bn),
    };
    let s = an ^ bn;
    match (a, b) {
        (Val::Inf(_), Val::Inf(_)) => Val::Nan,
        (Val::Inf(_), _) => Val::Inf(s),
        (_, Val::Inf(_)) => zero(s),
        (Val::Fin(_, aq), Val::Fin(_, bq)) if bq.is_zero() => {
            if aq.is_zero() {
                Val::Nan
            } else {
                Val::Inf(s)
            }
        }
        (Val::Fin(_, aq), Val::Fin(_, bq)) => {
            if aq.is_zero() {
                zero(s)
            } else {
                round(f, rm, s, &(aq / bq))
            }
        }
        _ => Val::Nan,
    }
}

fn fma_val(f: Fmt, rm: RoundingMode, a: &Val, b: &Val, c: &Val) -> Val {
    let (an, bn, cn) = match (a, b, c) {
        (Val::Nan, _, _) | (_, Val::Nan, _) | (_, _, Val::Nan) => return Val::Nan,
        (
            Val::Inf(an) | Val::Fin(an, _),
            Val::Inf(bn) | Val::Fin(bn, _),
            Val::Inf(cn) | Val::Fin(cn, _),
        ) => (*an, *bn, *cn),
    };
    let ps = an ^ bn;
    let is_zero = |v: &Val| matches!(v, Val::Fin(_, q) if q.is_zero());
    if matches!(a, Val::Inf(_)) || matches!(b, Val::Inf(_)) {
        if is_zero(a) || is_zero(b) || matches!(c, Val::Inf(n) if *n != ps) {
            return Val::Nan;
        }
        return Val::Inf(ps);
    }
    let (Val::Fin(_, aq), Val::Fin(_, bq)) = (a, b) else {
        return Val::Nan;
    };
    let cq = match c {
        Val::Inf(n) => return Val::Inf(*n),
        Val::Fin(_, cq) => cq,
        Val::Nan => return Val::Nan,
    };
    let product = aq * bq;
    let x = signed(ps, &product) + signed(cn, cq);
    if !x.is_zero() {
        round_signed(f, rm, &x)
    } else if product.is_zero() && cq.is_zero() {
        zero(zero_sum_sign(rm, ps, cn))
    } else {
        zero(rm == RoundingMode::RTN)
    }
}

/// The correctly rounded square root of the positive FP magnitude `q`.
///
/// `q = n / d` with `d` a power of two. `t = isqrt(n d 4^k)` brackets
/// `sqrt(q)` in the cell `[t, t + 1) / (d 2^k)`. Every rounding boundary of the
/// result (a multiple of half its quantum, `2^(E - sb)` with `E >= -log2(d)/2 - 1`)
/// is a multiple of `1 / (d 2^k)` once `k >= sb + 1`, so no boundary lies inside
/// the cell: the cell's midpoint rounds exactly as `sqrt(q)` does, and an exact
/// root is found exactly.
fn sqrt_magnitude(f: Fmt, rm: RoundingMode, q: &BigRational) -> Val {
    let k = u64::from(f.sb) + 8;
    let scale = BigInt::one() << (2 * k);
    let target = q.numer() * q.denom() * scale;
    let t = target.sqrt();
    let grid = q.denom() * (BigInt::one() << k);
    let mut root = BigRational::new(t.clone(), grid.clone());
    if &t * &t != target {
        root += BigRational::new(BigInt::one(), grid * 2);
    }
    round(f, rm, false, &root)
}

fn sqrt_val(f: Fmt, rm: RoundingMode, a: &Val) -> Val {
    match a {
        Val::Nan | Val::Inf(true) => Val::Nan,
        Val::Inf(false) => Val::Inf(false),
        Val::Fin(_, q) if q.is_zero() => a.clone(),
        Val::Fin(true, _) => Val::Nan,
        Val::Fin(false, q) => sqrt_magnitude(f, rm, q),
    }
}

/// `x - y n` with `n` the integer nearest `x / y`, ties to even: exact.
fn rem_val(a: &Val, b: &Val) -> Val {
    match (a, b) {
        (Val::Nan, _) | (_, Val::Nan) | (Val::Inf(_), _) => Val::Nan,
        (_, Val::Fin(_, q)) if q.is_zero() => Val::Nan,
        (_, Val::Inf(_)) => a.clone(),
        (Val::Fin(_, q), _) if q.is_zero() => a.clone(),
        (Val::Fin(an, aq), Val::Fin(bn, bq)) => {
            let (x, y) = (signed(*an, aq), signed(*bn, bq));
            let quotient = &x / &y;
            let floor = quotient.floor().to_integer();
            let rest = &quotient - BigRational::from_integer(floor.clone());
            let half = BigRational::new(BigInt::one(), BigInt::from(2));
            // Two's complement bit 0 is the parity of a negative integer too.
            let n = if rest > half || (rest == half && floor.bit(0)) {
                floor + 1
            } else {
                floor
            };
            let r = x - y * BigRational::from_integer(n);
            if r.is_zero() {
                zero(*an)
            } else {
                Val::Fin(r.is_negative(), r.abs())
            }
        }
    }
}

fn round_to_integral_val(f: Fmt, rm: RoundingMode, a: &Val) -> Option<Val> {
    let Val::Fin(neg, q) = a else {
        return Some(a.clone());
    };
    let n = BigRational::from_integer(round_magnitude_to_integer(rm, *neg, q));
    // Only formats with emax < sb - 1 can round past their largest finite
    // value here; IEEE 754 does not define that case.
    (n <= f.max_finite()).then_some(Val::Fin(*neg, n))
}

fn min_max_val(a: &Val, b: &Val, want: Ordering) -> Option<Val> {
    match (a, b) {
        (Val::Nan, _) => return Some(b.clone()),
        (_, Val::Nan) => return Some(a.clone()),
        (Val::Fin(an, aq), Val::Fin(bn, bq)) if aq.is_zero() && bq.is_zero() && an != bn => {
            // SMT-LIB leaves fp.min/fp.max of +0 and -0 unspecified.
            return None;
        }
        _ => {}
    }
    Some(if order(a, b)? == want.reverse() {
        b.clone()
    } else {
        a.clone()
    })
}

fn binary(a: &Value, b: &Value, op: impl FnOnce(Fmt, &Val, &Val) -> Option<Val>) -> Option<Value> {
    let f = same_format(&[a, b])?;
    encode(f, &op(f, &decode(a), &decode(b))?)
}

fn unary(a: &Value, op: impl FnOnce(Fmt, &Val) -> Option<Val>) -> Option<Value> {
    let f = Fmt::of(a)?;
    encode(f, &op(f, &decode(a))?)
}

/// `(fp.add rm a b)`.
pub(crate) fn add(rm: RoundingMode, a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |f, x, y| Some(add_val(f, rm, x, y)))
}

/// `(fp.sub rm a b)`: `a + (-b)`, exactly (IEEE 754 §5.4.1).
pub(crate) fn sub(rm: RoundingMode, a: &Value, b: &Value) -> Option<Value> {
    add(rm, a, &neg(b)?)
}

/// `(fp.mul rm a b)`.
pub(crate) fn mul(rm: RoundingMode, a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |f, x, y| Some(mul_val(f, rm, x, y)))
}

/// `(fp.div rm a b)`.
pub(crate) fn div(rm: RoundingMode, a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |f, x, y| Some(div_val(f, rm, x, y)))
}

/// `(fp.fma rm a b c)`: `a * b + c` rounded once.
pub(crate) fn fma(rm: RoundingMode, a: &Value, b: &Value, c: &Value) -> Option<Value> {
    let f = same_format(&[a, b, c])?;
    encode(f, &fma_val(f, rm, &decode(a), &decode(b), &decode(c)))
}

/// `(fp.sqrt rm a)`.
pub(crate) fn sqrt(rm: RoundingMode, a: &Value) -> Option<Value> {
    unary(a, |f, x| Some(sqrt_val(f, rm, x)))
}

/// `(fp.rem a b)`, the IEEE remainder.
pub(crate) fn rem(a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |_, x, y| Some(rem_val(x, y)))
}

/// `(fp.roundToIntegral rm a)`.
pub(crate) fn round_to_integral(rm: RoundingMode, a: &Value) -> Option<Value> {
    unary(a, |f, x| round_to_integral_val(f, rm, x))
}

/// `(fp.min a b)`; `None` on `+0`/`-0`, which SMT-LIB leaves unspecified.
pub(crate) fn min(a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |_, x, y| min_max_val(x, y, Ordering::Less))
}

/// `(fp.max a b)`; `None` on `+0`/`-0`, which SMT-LIB leaves unspecified.
pub(crate) fn max(a: &Value, b: &Value) -> Option<Value> {
    binary(a, b, |_, x, y| min_max_val(x, y, Ordering::Greater))
}

/// `(fp.neg a)`; NaN stays the one NaN.
pub(crate) fn neg(a: &Value) -> Option<Value> {
    unary(a, |_, x| {
        Some(match x {
            Val::Nan => Val::Nan,
            Val::Inf(n) => Val::Inf(!n),
            Val::Fin(n, q) => Val::Fin(!n, q.clone()),
        })
    })
}

/// `(fp.abs a)`.
pub(crate) fn abs(a: &Value) -> Option<Value> {
    unary(a, |_, x| {
        Some(match x {
            Val::Nan => Val::Nan,
            Val::Inf(_) => Val::Inf(false),
            Val::Fin(_, q) => Val::Fin(false, q.clone()),
        })
    })
}

/// `((_ to_fp eb sb) rm a)` for a FloatingPoint `a` of any format.
pub(crate) fn to_fp_from_fp(rm: RoundingMode, a: &Value, eb: u32, sb: u32) -> Option<Value> {
    Fmt::of(a)?;
    let target = Fmt::checked(eb, sb)?;
    let value = match decode(a) {
        Val::Fin(n, q) if !q.is_zero() => round(target, rm, n, &q),
        other => other,
    };
    encode(target, &value)
}

/// `((_ to_fp eb sb) rm x)` for an exact Real, Int or bit-vector value `x`
/// (an exact zero is `+0`).
pub(crate) fn to_fp_from_rational(
    rm: RoundingMode,
    x: &BigRational,
    eb: u32,
    sb: u32,
) -> Option<Value> {
    let target = Fmt::checked(eb, sb)?;
    encode(target, &round_signed(target, rm, x))
}

/// `(fp.to_real a)`; `None` on NaN and the infinities (unspecified).
pub(crate) fn to_real(a: &Value) -> Option<BigRational> {
    Fmt::of(a)?;
    match decode(a) {
        Val::Fin(n, q) => Some(signed(n, &q)),
        _ => None,
    }
}

/// The integer `rm` rounds a finite `a` to.
fn to_integer(rm: RoundingMode, a: &Value) -> Option<BigInt> {
    Fmt::of(a)?;
    match decode(a) {
        Val::Fin(n, q) => {
            let magnitude = round_magnitude_to_integer(rm, n, &q);
            Some(if n { -magnitude } else { magnitude })
        }
        _ => None,
    }
}

/// `((_ fp.to_ubv w) rm a)`; `None` when unspecified (NaN, an infinity, or a
/// rounded value outside `[0, 2^w)`).
pub(crate) fn to_ubv(rm: RoundingMode, a: &Value, w: u32) -> Option<BigInt> {
    let n = to_integer(rm, a)?;
    (!n.is_negative() && n < (BigInt::one() << w)).then_some(n)
}

/// `((_ fp.to_sbv w) rm a)` as the `w`-bit two's-complement pattern; `None`
/// when unspecified (NaN, an infinity, or outside `[-2^(w-1), 2^(w-1))`).
pub(crate) fn to_sbv(rm: RoundingMode, a: &Value, w: u32) -> Option<BigInt> {
    let n = to_integer(rm, a)?;
    let half = BigInt::one() << w.checked_sub(1)?;
    if n < -half.clone() || n >= half {
        return None;
    }
    Some(if n.is_negative() {
        n + (BigInt::one() << w)
    } else {
        n
    })
}

/// Exact `2^e`, re-exported for the tests' oracle.
#[cfg(test)]
pub(in crate::exact) fn two_to(e: i64) -> BigRational {
    super::pow2(e)
}
