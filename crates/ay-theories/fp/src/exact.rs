// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact concrete FP arithmetic with the public model carrier's admission.
//!
//! Compatibility wrappers share the private closed rewriter's rational core.
//! They do not widen symbolic model/checker admission or the public value API.

#[cfg(test)]
mod tests;
pub(crate) mod wide;
#[cfg(test)]
use wide::{ops, Fmt};

use crate::{FpModelValue, RoundingMode};
use num_bigint::BigInt;
use num_rational::BigRational;
use wide::Value;
pub use wide::MAX_EXPONENT_BITS;

/// Correctly rounded `fp.add` within the model carrier's envelope.
pub fn add(rm: RoundingMode, a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::add(rm, &Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Correctly rounded `fp.sub` within the model carrier's envelope.
pub fn sub(rm: RoundingMode, a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::sub(rm, &Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Correctly rounded `fp.mul` within the model carrier's envelope.
pub fn mul(rm: RoundingMode, a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::mul(rm, &Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Correctly rounded `fp.div` within the model carrier's envelope.
pub fn div(rm: RoundingMode, a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::div(rm, &Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Correctly rounded concrete FP operation within the model envelope.
pub fn sqrt(rm: RoundingMode, a: &FpModelValue) -> Option<FpModelValue> {
    wide::sqrt(rm, &Value::from_model(a)?)?.into_model()
}

/// Correctly rounded concrete FP operation within the model envelope.
pub fn round_to_integral(rm: RoundingMode, a: &FpModelValue) -> Option<FpModelValue> {
    wide::round_to_integral(rm, &Value::from_model(a)?)?.into_model()
}

/// `(fp.rem a b)`, the IEEE remainder.
pub fn rem(a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::rem(&Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// `(fp.min a b)`; `None` on `+0`/`-0`, which SMT-LIB leaves unspecified.
pub fn min(a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::min(&Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// `(fp.max a b)`; `None` on `+0`/`-0`, which SMT-LIB leaves unspecified.
pub fn max(a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::max(&Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Exact remainder with quotient rounded toward zero, independent of FP mode.
///
/// Defined on the existing exact evaluator's admitted formats. Rejects
/// mismatched/unrepresentable formats. NaN, infinite dividend, or zero divisor
/// produce logical NaN; a finite dividend modulo infinity is unchanged.
/// Signed zero and every finite nonzero result keep the dividend's sign.
pub fn truncating_rem(a: &FpModelValue, b: &FpModelValue) -> Option<FpModelValue> {
    wide::truncating_rem(&Value::from_model(a)?, &Value::from_model(b)?)?.into_model()
}

/// Concrete FP sign operation within the model envelope.
pub fn neg(a: &FpModelValue) -> Option<FpModelValue> {
    wide::neg(&Value::from_model(a)?)?.into_model()
}

/// Concrete FP sign operation within the model envelope.
pub fn abs(a: &FpModelValue) -> Option<FpModelValue> {
    wide::abs(&Value::from_model(a)?)?.into_model()
}

/// `fp.eq`: IEEE equality, false on NaN, `-0 == +0`.
pub fn fp_eq(a: &FpModelValue, b: &FpModelValue) -> Option<bool> {
    wide::fp_eq(&Value::from_model(a)?, &Value::from_model(b)?)
}

/// `fp.lt`, false on NaN.
pub fn fp_lt(a: &FpModelValue, b: &FpModelValue) -> Option<bool> {
    wide::fp_lt(&Value::from_model(a)?, &Value::from_model(b)?)
}

/// `fp.leq`, false on NaN.
pub fn fp_leq(a: &FpModelValue, b: &FpModelValue) -> Option<bool> {
    wide::fp_leq(&Value::from_model(a)?, &Value::from_model(b)?)
}

/// SMT-LIB `=` on two FloatingPoint values: identity of the sort's elements
/// (one NaN; `-0` and `+0` distinct).
pub fn same_element(a: &FpModelValue, b: &FpModelValue) -> Option<bool> {
    wide::same_element(&Value::from_model(a)?, &Value::from_model(b)?)
}

/// `((_ fp.to_ubv w) rm a)`; `None` when unspecified (NaN, an infinity, or a
/// rounded value outside `[0, 2^w)`).
pub fn to_ubv(rm: RoundingMode, a: &FpModelValue, w: u32) -> Option<BigInt> {
    wide::to_ubv(rm, &Value::from_model(a)?, w)
}

/// `((_ fp.to_sbv w) rm a)` as the `w`-bit two's-complement pattern; `None`
/// when unspecified (NaN, an infinity, or outside `[-2^(w-1), 2^(w-1))`).
pub fn to_sbv(rm: RoundingMode, a: &FpModelValue, w: u32) -> Option<BigInt> {
    wide::to_sbv(rm, &Value::from_model(a)?, w)
}

/// Fused multiply-add, rounded once.
pub fn fma(
    rm: RoundingMode,
    a: &FpModelValue,
    b: &FpModelValue,
    c: &FpModelValue,
) -> Option<FpModelValue> {
    wide::fma(
        rm,
        &Value::from_model(a)?,
        &Value::from_model(b)?,
        &Value::from_model(c)?,
    )?
    .into_model()
}

/// Round an FP value into another admitted model format.
pub fn to_fp_from_fp(rm: RoundingMode, a: &FpModelValue, eb: u32, sb: u32) -> Option<FpModelValue> {
    wide::to_fp_from_fp(rm, &Value::from_model(a)?, eb, sb)?.into_model()
}

/// Round an exact rational into an admitted model format.
pub fn to_fp_from_rational(
    rm: RoundingMode,
    x: &BigRational,
    eb: u32,
    sb: u32,
) -> Option<FpModelValue> {
    wide::to_fp_from_rational(rm, x, eb, sb)?.into_model()
}

/// `(fp.to_real a)`; `None` on NaN and the infinities (unspecified).
pub fn to_real(a: &FpModelValue) -> Option<BigRational> {
    wide::to_real(&Value::from_model(a)?)
}

/// One of the SMT-LIB FP classification predicates.
pub fn classify(name: &str, v: &FpModelValue) -> Option<bool> {
    wide::classify(name, &Value::from_model(v)?)
}

/// Strict unsigned IEEE decoding within the closed arithmetic work envelope.
pub fn from_ieee_bits(bits: &BigInt, eb: u32, sb: u32) -> Option<FpModelValue> {
    wide::from_ieee_bits(bits, eb, sb)?.into_model()
}
