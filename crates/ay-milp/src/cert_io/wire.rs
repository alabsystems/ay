// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// Exact rationals on the wire
// ---------------------------------------------------------------------------

/// Canonical decimal `numer/denom`, reduced, `denom >= 1`, `denom == 1` elided.
pub(super) fn fmt_rat(r: &BigRational) -> String {
    if r.denom().is_one() {
        r.numer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// A rational as an APPROXIMATE decimal, for a human reading a check report.
///
/// Never written to a certificate and never compared against anything: an
/// exactified `f64` dual can carry a denominator around `2^90`, and a reader
/// handed `105177991209283667304698998625037/4951760157141521099596496896`
/// cannot tell at a glance whether the bound is close to the claimed optimum
/// or nowhere near it. The exact value is always printed beside this, and the
/// `~` prefix says which of the two is the certificate's.
pub(super) fn approx_decimal(r: &BigRational) -> String {
    use num_traits::ToPrimitive as _;
    r.to_f64()
        .filter(|value| value.is_finite())
        .map_or_else(|| "~?".to_owned(), |value| format!("~{value}"))
}

/// Parse a wire rational. Rejects a zero/negative denominator and a
/// non-reduced fraction: the wire form is CANONICAL, so `2/4` is malformed
/// rather than silently normalised. That keeps the `%END` digest a function of
/// the value.
pub(super) fn parse_rat(s: &str) -> Option<BigRational> {
    let s = s.trim();
    match s.split_once('/') {
        Some((n, d)) => {
            let n: BigInt = n.parse().ok()?;
            let d: BigInt = d.parse().ok()?;
            if !d.is_positive() || d.is_one() {
                return None;
            }
            if n.gcd(&d) != BigInt::one() {
                return None;
            }
            Some(BigRational::new_raw(n, d))
        }
        None => Some(BigRational::from_integer(s.parse().ok()?)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BoundedRatParseError {
    Malformed,
    BitLimit,
}

/// Maximum decimal digits needed to spell any integer whose magnitude uses at
/// most `bit_cap` bits.  `30103 / 100000` is a strict upper bound on
/// `log10(2)`, so this preflight never rejects an integer that satisfies the
/// binary cap.  The exact `BigInt::bits` check below rejects the few values
/// admitted by the rational approximation but lying just above the cap.
pub(super) fn max_decimal_digits_for_bits(bit_cap: usize) -> Option<usize> {
    const LOG10_2_UPPER_NUMERATOR: usize = 30_103;
    const LOG10_2_UPPER_DENOMINATOR: usize = 100_000;

    if bit_cap == 0 {
        return Some(1);
    }
    bit_cap
        .checked_mul(LOG10_2_UPPER_NUMERATOR)?
        .checked_add(LOG10_2_UPPER_DENOMINATOR - 1)
        .map(|scaled| scaled / LOG10_2_UPPER_DENOMINATOR)
}

/// Parse one integer without ever constructing a value materially larger than
/// `bit_cap`.  Length is checked before digit validation and `BigInt` parsing,
/// so an adversarial megabyte-scale token remains a borrowed string plus a
/// typed rejection rather than a megabyte-scale bignum.
pub(super) fn parse_bigint_bounded(
    s: &str,
    bit_cap: usize,
) -> Result<BigInt, BoundedRatParseError> {
    let digits = s
        .strip_prefix('-')
        .or_else(|| s.strip_prefix('+'))
        .unwrap_or(s);
    let digit_cap = max_decimal_digits_for_bits(bit_cap).ok_or(BoundedRatParseError::BitLimit)?;
    if digits.is_empty() || digits.len() > digit_cap {
        return Err(if digits.is_empty() {
            BoundedRatParseError::Malformed
        } else {
            BoundedRatParseError::BitLimit
        });
    }
    if !digits.bytes().all(|digit| digit.is_ascii_digit()) {
        return Err(BoundedRatParseError::Malformed);
    }
    let value = s
        .parse::<BigInt>()
        .map_err(|_| BoundedRatParseError::Malformed)?;
    if value.bits() > bit_cap as u64 {
        return Err(BoundedRatParseError::BitLimit);
    }
    Ok(value)
}

/// Bounded counterpart of [`parse_rat`] for proof formats whose verifier has
/// an explicit exact-value ceiling.  Both operands are bounded before the gcd,
/// and the canonical wire rules remain identical to the unbounded parser.
pub(super) fn parse_rat_bounded(
    s: &str,
    bit_cap: usize,
) -> Result<BigRational, BoundedRatParseError> {
    let s = s.trim();
    match s.split_once('/') {
        Some((n, d)) => {
            let n = parse_bigint_bounded(n, bit_cap)?;
            let d = parse_bigint_bounded(d, bit_cap)?;
            if !d.is_positive() || d.is_one() || n.gcd(&d) != BigInt::one() {
                return Err(BoundedRatParseError::Malformed);
            }
            Ok(BigRational::new_raw(n, d))
        }
        None => Ok(BigRational::from_integer(parse_bigint_bounded(s, bit_cap)?)),
    }
}

pub(super) fn sense_token(s: Sense) -> &'static str {
    match s {
        Sense::Minimize => "min",
        Sense::Maximize => "max",
    }
}

pub(super) fn parse_sense(t: &str) -> Option<Sense> {
    match t {
        "min" => Some(Sense::Minimize),
        "max" => Some(Sense::Maximize),
        _ => None,
    }
}

pub(super) fn side_token(s: BoundSide) -> &'static str {
    match s {
        BoundSide::Lower => "lower",
        BoundSide::Upper => "upper",
    }
}

pub(super) fn parse_side(t: &str) -> Option<BoundSide> {
    match t {
        "lower" => Some(BoundSide::Lower),
        "upper" => Some(BoundSide::Upper),
        _ => None,
    }
}

/// An optional exact bound on the wire: `-inf` / `+inf` for an absent side.
pub(super) fn fmt_bound(v: Option<&BigRational>, upper: bool) -> String {
    v.map_or_else(
        || if upper { "+inf".into() } else { "-inf".into() },
        fmt_rat,
    )
}
