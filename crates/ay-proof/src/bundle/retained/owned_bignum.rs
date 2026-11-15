// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed legacy number leaves, not a complete owning bundle reader.
//!
//! Input admission and returned-owner accounting belong to the caller. The
//! same control charges temporary limbs and the private bigint construction;
//! no allowance is renewed or refunded when temporary limbs are dropped.
//! num-bigint construction is an INFALLIBLE opaque leaf. Its private capacity
//! is not observable: the charge below is the requested allocation derived
//! from the pinned implementation, not measured capacity or an RSS/OOM bound.
//!
//! Compatibility is accepted-value and re-encoded-byte parity, not diagnostic
//! wording or fault order. Input syntax was already admitted as RawValue, and
//! the typed tuple shape prepass can reject extra elements before a bad sign
//! or rational numerator. Public ay-core serde keeps its streaming fault order.

use super::{
    control::Control,
    owned_values::{i64_value, i8_value, tuple, u32_value, vector, RawSlice},
    TransportError,
};
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::{BigRational, Rational64};
use num_traits::Zero;

pub(super) fn bigint(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<BigInt, TransportError> {
    let [Some(sign), Some(words)] = tuple::<2>(raw, control)? else {
        return control.fail(TransportError::InvalidShape("expected bigint pair"));
    };
    // Match ay-core::serde_bignum: reject the sign before decoding any limb.
    let sign = match i8_value(sign, control)? {
        -1 => Sign::Minus,
        0 => Sign::NoSign,
        1 => Sign::Plus,
        _ => return control.fail(TransportError::InvalidShape("invalid bigint sign")),
    };
    // A valid array cannot contain more elements than its encoded byte length.
    // Even NoSign must validate EVERY limb before its magnitude is discarded.
    let limbs = vector(words, words.as_str().len(), control, u32_value)?;
    let mut count = limbs.len();
    while count != 0 {
        control.charge(1, 0)?;
        if limbs[count - 1] != 0 {
            break;
        }
        count -= 1;
    }
    let value = if sign == Sign::NoSign || count == 0 {
        BigInt::ZERO
    } else {
        let (work, bytes) = construction_charge(count, control)?;
        control.charge(work, bytes)?;
        BigInt::from_biguint(sign, BigUint::from_slice(&limbs[..count]))
    };
    // Both temporary limb storage and the result coexist during construction.
    // No hidden Vec shrink is requested; final cancellation follows cleanup.
    drop(limbs);
    control.charge(0, 0)?;
    Ok(value)
}

/// Requested buffer and logical copy visits for a NONEMPTY trimmed magnitude.
fn construction_charge(
    words: usize,
    control: &mut Control<'_>,
) -> Result<(usize, usize), TransportError> {
    // num-bigint 0.4.6 macros.rs selects u64 exactly on pointer-width 64,
    // otherwise u32. biguint.rs::assign_from_slice extends a fresh empty Vec:
    // chunks(2).map(...) is TrustedLen; the u32 path extends from a slice.
    // Trust 5f8066c410 library/alloc vec::{extend_trusted,append_elements}
    // both reserve once. raw_vec::grow_amortized requests max(4, digits)
    // for 4/8-byte elements. Re-audit this bound if either implementation changes.
    #[cfg(target_pointer_width = "64")]
    let (digits, digit_bytes) = (control.add(words / 2, words % 2)?, size_of::<u64>());
    #[cfg(not(target_pointer_width = "64"))]
    let (digits, digit_bytes) = (words, size_of::<u32>());
    let bytes = control.product(digits.max(4), digit_bytes)?;
    // Price each source word, each destination digit, and the two constant
    // normalize/is_zero tail checks before entering the opaque construction.
    let visits = control.add(words, digits)?;
    let work = control.add(visits, 2)?;
    // The last input word is nonzero, so normalize neither truncates nor
    // shrinks: digits >= 1 and digits >= max(4, digits) / 4. This relies on the
    // pinned requested capacity above, not a public BigUint capacity promise.
    Ok((work, bytes))
}

pub(super) fn big_rational(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<BigRational, TransportError> {
    let [Some(numer), Some(denom)] = tuple::<2>(raw, control)? else {
        return control.fail(TransportError::InvalidShape("expected rational pair"));
    };
    let numer = bigint(numer, control)?;
    let denom = bigint(denom, control)?;
    control.charge(1, 0)?;
    if denom.is_zero() {
        return control.fail(TransportError::InvalidShape("zero rational denominator"));
    }
    // Keep unreduced magnitudes and denominator sign, just like the incumbent.
    let value = BigRational::new_raw(numer, denom);
    control.charge(0, 0)?;
    Ok(value)
}

pub(super) fn rational64(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<Rational64, TransportError> {
    let [Some(numer), Some(denom)] = tuple::<2>(raw, control)? else {
        return control.fail(TransportError::InvalidShape("expected rational pair"));
    };
    let numer = i64_value(numer, control)?;
    let denom = i64_value(denom, control)?;
    control.charge(1, 0)?;
    if denom == 0 {
        return control.fail(TransportError::InvalidShape("zero rational denominator"));
    }
    let value = Rational64::new_raw(numer, denom);
    control.charge(0, 0)?;
    Ok(value)
}

#[cfg(test)]
mod tests;
