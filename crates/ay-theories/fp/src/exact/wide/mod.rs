// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact SMT-LIB FloatingPoint operations on concrete values: the arithmetic
//! the FP rewriter folds constants with.
//!
//! Every operation computes the exact rational result and rounds it once,
//! following IEEE 754-2008 (§4.3 rounding-direction attributes, §6.3 the sign
//! of an exact zero, §7.4 overflow) and the SMT-LIB FloatingPoints theory.
//! Nothing here reads the bit-blaster or the independent model checker
//! (`ay-model-check/src/fp.rs`): the three agree because each follows the
//! standard, and the tests compare this module with the circuits exhaustively
//! on small formats.
//!
//! A function returns `None` when SMT-LIB leaves the result unspecified
//! (`fp.to_ubv` of NaN, `fp.min` of two opposite zeros, ...), when the operand
//! formats differ, or when a format is outside what this module computes with
//! (the bounded private carrier, and at most [`MAX_EXPONENT_BITS`] exponent bits so
//! that no exact intermediate is astronomically large). The rewriter then
//! leaves the term alone.

pub(super) mod ops;
mod truncating;
mod value;
pub(crate) use value::Value;

pub use truncating::truncating_rem;

pub use ops::{
    abs, add, div, fma, max, min, mul, neg, rem, round_to_integral, sqrt, sub, to_fp_from_fp,
    to_fp_from_rational, to_real, to_sbv, to_ubv,
};

use crate::RoundingMode;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

/// Formats with more exponent bits are never folded: `2^emax` alone would have
/// `2^(eb-1)` binary digits.
pub const MAX_EXPONENT_BITS: u32 = 20;

// A bounded first precision extension, including binary256. Keep the structural
// million-bit encoding envelope separate from exact arithmetic's work bound.
const MAX_SIGNIFICAND_BITS: u32 = 256;

/// An SMT-LIB FloatingPoint value as exact arithmetic sees it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Val {
    /// The single NaN of the sort.
    Nan,
    /// An infinity; `true` is negative.
    Inf(bool),
    /// A finite value: sign (`true` negative) and magnitude `>= 0`. A zero
    /// magnitude is the signed zero.
    Fin(bool, BigRational),
}

/// A format `(eb, sb)`, `sb` counting the hidden bit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Fmt {
    eb: u32,
    sb: u32,
}

impl Fmt {
    /// The format of `v`, when this module computes with it.
    fn of(v: &Value) -> Option<Self> {
        Self::checked(v.eb(), v.sb())
    }

    pub(super) fn checked(eb: u32, sb: u32) -> Option<Self> {
        // Closed arithmetic has a bounded private carrier; structural encoding
        // and symbolic model admission retain their separate limits.
        ((2..=MAX_EXPONENT_BITS).contains(&eb)
            && (2..=MAX_SIGNIFICAND_BITS).contains(&sb)
            && eb <= crate::MAX_ENCODING_EXPONENT_BITS
            && sb <= crate::MAX_ENCODING_SIGNIFICAND_BITS)
            .then_some(Self { eb, sb })
    }

    fn bias(self) -> i64 {
        (1i64 << (self.eb - 1)) - 1
    }

    /// The smallest normal exponent.
    fn emin(self) -> i64 {
        1 - self.bias()
    }

    /// The largest finite value, `(2 - 2^(1-sb)) * 2^emax`.
    fn max_finite(self) -> BigRational {
        let two = BigRational::from_integer(BigInt::from(2));
        (two - pow2(1 - i64::from(self.sb))) * pow2(self.bias())
    }
}

/// `2^e` as an exact rational.
fn pow2(e: i64) -> BigRational {
    let magnitude = BigInt::one() << e.unsigned_abs();
    if e >= 0 {
        BigRational::from_integer(magnitude)
    } else {
        BigRational::new(BigInt::one(), magnitude)
    }
}

/// `floor(log2(q))` for `q > 0`.
fn ilog2(q: &BigRational) -> i64 {
    let bits = |n: &BigInt| i64::try_from(n.bits()).unwrap_or(i64::MAX);
    let mut e = bits(q.numer()) - bits(q.denom());
    while pow2(e) > *q {
        e -= 1;
    }
    while pow2(e + 1) <= *q {
        e += 1;
    }
    e
}

/// The integer `rm` rounds the magnitude `q >= 0` of a value with sign `neg`
/// to (the integral rounding of IEEE 754 §5.9 and of `fp.to_ubv`/`fp.to_sbv`).
fn round_magnitude_to_integer(rm: RoundingMode, neg: bool, q: &BigRational) -> BigInt {
    let floor = q.floor().to_integer();
    let rest = q - BigRational::from_integer(floor.clone());
    if rest.is_zero() {
        return floor;
    }
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    let up = match rm {
        RoundingMode::RNE => rest > half || (rest == half && floor.bit(0)),
        RoundingMode::RNA => rest >= half,
        RoundingMode::RTZ => false,
        RoundingMode::RTP => !neg,
        RoundingMode::RTN => neg,
    };
    if up {
        floor + 1
    } else {
        floor
    }
}

/// Round the exact nonzero real `(-1)^neg * q` into `f` under `rm`.
fn round(f: Fmt, rm: RoundingMode, neg: bool, q: &BigRational) -> Val {
    debug_assert!(q.is_positive());
    // The quantum of the binade q lies in, never finer than the subnormal one.
    let e = ilog2(q).max(f.emin());
    let quantum = pow2(e - i64::from(f.sb) + 1);
    let steps = round_magnitude_to_integer(rm, neg, &(q / &quantum));
    let rounded = BigRational::from_integer(steps) * quantum;
    if rounded > f.max_finite() {
        // IEEE 754 §7.4: the result rounded with an unbounded exponent is
        // beyond the largest finite value.
        let to_infinity = match rm {
            RoundingMode::RNE | RoundingMode::RNA => true,
            RoundingMode::RTZ => false,
            RoundingMode::RTP => !neg,
            RoundingMode::RTN => neg,
        };
        return if to_infinity {
            Val::Inf(neg)
        } else {
            Val::Fin(neg, f.max_finite())
        };
    }
    Val::Fin(neg, rounded)
}

/// Round an exact signed rational; an exact zero is `+0` (the caller supplies
/// any other zero sign).
fn round_signed(f: Fmt, rm: RoundingMode, x: &BigRational) -> Val {
    if x.is_zero() {
        Val::Fin(false, BigRational::zero())
    } else {
        round(f, rm, x.is_negative(), &x.abs())
    }
}

fn decode(v: &Value) -> Val {
    v.decode()
}

/// The value `v` as an element of `f`; `None` when it is not representable
/// there (never the case for a result of [`round`]).
fn encode(f: Fmt, v: &Val) -> Option<Value> {
    let (eb, sb) = (f.eb, f.sb);
    let (neg, q) = match v {
        Val::Nan => return Value::from_fields(false, (1u64 << eb) - 1, BigInt::one(), eb, sb),
        Val::Inf(true) => {
            return Value::from_fields(true, (1u64 << eb) - 1, BigInt::zero(), eb, sb)
        }
        Val::Inf(false) => {
            return Value::from_fields(false, (1u64 << eb) - 1, BigInt::zero(), eb, sb)
        }
        Val::Fin(neg, q) => (*neg, q),
    };
    if q.is_zero() {
        return Value::from_fields(neg, 0, BigInt::zero(), eb, sb);
    }
    let precision = i64::from(sb) - 1;
    let (biased, stored) = if *q < pow2(f.emin()) {
        (0, q / pow2(f.emin() - precision))
    } else {
        let e = ilog2(q);
        let scaled = q / pow2(e - precision) - pow2(precision);
        (e + f.bias(), scaled)
    };
    if !stored.is_integer() || !(0..(1i64 << f.eb) - 1).contains(&biased) {
        return None;
    }
    let significand = stored.to_integer();
    Value::from_fields(neg, u64::try_from(biased).ok()?, significand, eb, sb)
}

/// The shared format of `values`, when there is one this module computes with.
fn same_format(values: &[&Value]) -> Option<Fmt> {
    let (first, rest) = values.split_first()?;
    let f = Fmt::of(first)?;
    rest.iter()
        .all(|v| (v.eb(), v.sb()) == (f.eb, f.sb))
        .then_some(f)
}

/// The order of two non-NaN values (`-0 == +0`).
fn order(a: &Val, b: &Val) -> Option<Ordering> {
    let key = |v: &Val| -> Option<(i8, BigRational)> {
        match v {
            Val::Nan => None,
            Val::Inf(neg) => Some((if *neg { -1 } else { 1 }, BigRational::zero())),
            Val::Fin(neg, q) => Some((0, if *neg { -q.clone() } else { q.clone() })),
        }
    };
    Some(key(a)?.cmp(&key(b)?))
}

/// `fp.eq`: IEEE equality, false on NaN, `-0 == +0`.
pub fn fp_eq(a: &Value, b: &Value) -> Option<bool> {
    same_format(&[a, b])?;
    Some(order(&decode(a), &decode(b)) == Some(Ordering::Equal))
}

/// `fp.lt`, false on NaN.
pub fn fp_lt(a: &Value, b: &Value) -> Option<bool> {
    same_format(&[a, b])?;
    Some(order(&decode(a), &decode(b)) == Some(Ordering::Less))
}

/// `fp.leq`, false on NaN.
pub fn fp_leq(a: &Value, b: &Value) -> Option<bool> {
    same_format(&[a, b])?;
    Some(matches!(
        order(&decode(a), &decode(b)),
        Some(Ordering::Less | Ordering::Equal)
    ))
}

/// SMT-LIB `=` on two FloatingPoint values: identity of the sort's elements
/// (one NaN; `-0` and `+0` distinct).
pub fn same_element(a: &Value, b: &Value) -> Option<bool> {
    same_format(&[a, b])?;
    Some(decode(a) == decode(b))
}

/// One of the seven classification predicates, by SMT-LIB name.
pub fn classify(name: &str, v: &Value) -> Option<bool> {
    let f = Fmt::of(v)?;
    let x = decode(v);
    let normal_bound = pow2(f.emin());
    Some(match (name, &x) {
        ("fp.isNaN", _) => x == Val::Nan,
        ("fp.isInfinite", _) => matches!(x, Val::Inf(_)),
        ("fp.isZero", Val::Fin(_, q)) => q.is_zero(),
        ("fp.isNormal", Val::Fin(_, q)) => *q >= normal_bound,
        ("fp.isSubnormal", Val::Fin(_, q)) => q.is_positive() && *q < normal_bound,
        ("fp.isZero" | "fp.isNormal" | "fp.isSubnormal", _) => false,
        ("fp.isNegative", Val::Fin(neg, _) | Val::Inf(neg)) => *neg,
        ("fp.isPositive", Val::Fin(neg, _) | Val::Inf(neg)) => !*neg,
        ("fp.isNegative" | "fp.isPositive", Val::Nan) => false,
        _ => return None,
    })
}

/// Decode `(eb, sb)` IEEE fields given as integers: the value of the `fp`
/// constructor and of the one-argument `to_fp` over a bit pattern.
pub fn from_ieee_bits(bits: &BigInt, eb: u32, sb: u32) -> Option<Value> {
    Fmt::checked(eb, sb)?;
    Value::from_ieee_bv(bits, eb, sb)
}
