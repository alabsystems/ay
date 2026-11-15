// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact-rational truncating remainder, not SMT fp.rem.
//!
//! This operates on logical FP values. A canonical logical NaN is not a
//! contract for an observable Rust NaN sign/payload bit pattern.

use num_rational::BigRational;
use num_traits::Zero;

use super::Value;
use super::{decode, encode, same_format, Val};

/// Exact remainder with quotient rounded toward zero, independent of FP mode.
///
/// Defined on the existing exact evaluator's admitted formats. Rejects
/// mismatched/unrepresentable formats. NaN, infinite dividend, or zero divisor
/// produce logical NaN; a finite dividend modulo infinity is unchanged.
/// Signed zero and every finite nonzero result keep the dividend's sign.
pub fn truncating_rem(a: &Value, b: &Value) -> Option<Value> {
    let format = same_format(&[a, b])?;
    let value = match (decode(a), decode(b)) {
        (Val::Nan, _) | (_, Val::Nan) | (Val::Inf(_), _) => Val::Nan,
        (_, Val::Fin(_, q)) if q.is_zero() => Val::Nan,
        (x, Val::Inf(_)) => x,
        (Val::Fin(sign, magnitude), Val::Fin(_, divisor)) => {
            // Work only on magnitudes: floor(|a|/|b|) is the absolute value
            // of trunc(a/b), regardless of either operand's sign. No FP
            // division or intermediate rounding is performed.
            let quotient = (&magnitude / &divisor).floor().to_integer();
            let remainder = magnitude - divisor * BigRational::from_integer(quotient);
            Val::Fin(sign, remainder)
        }
    };
    // A floating remainder is exactly representable in the same format.
    // encode requires that exact representation; it does not silently round.
    encode(format, &value)
}
