// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Decimal numbers as exact rationals: reading a number of an MPS file, and
//! writing a value the MIPLIB solution checker reads back.
//!
//! # The numbers ay reads
//!
//! `[+-]? (digits [. digits?] | . digits) ([eE] [+-]? digits)?`, nothing else:
//! no `inf`, no `1/3`, no hexadecimal, no Fortran `D` exponent. The checker
//! (`Rational::fromString` of the organizers' `miplib2017-checker`) reads every
//! number of this grammar as the same rational; it silently skips characters
//! outside it, so a file that uses them means one thing to it and another to
//! other readers, and ay refuses it. A value whose magnitude is above
//! `f64::MAX`, or nonzero and below `f64::MIN_POSITIVE`, is refused too: the
//! engines' floating-point lanes could not even hold an approximation of it.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The decimal exponent beyond which a number is refused before it is built
/// (no `f64` reaches `1e±400`; this keeps `10^e` from being computed for an
/// absurd `e`).
const MAX_DECIMAL_EXPONENT: i64 = 400;

/// The longest number text the MIPLIB checker reads (`assert(strlen(num) <
/// 32)` in `Rational::fromString`); [`write_value`] never writes a longer one.
pub const MAX_CHECKER_NUMBER_LEN: usize = 31;

/// Reads `text` as the exact rational it denotes, or `None` when it is not a
/// number of the grammar in the module docs or is out of range.
#[must_use]
pub fn parse_decimal(text: &str) -> Option<BigRational> {
    let bytes = text.as_bytes();
    // Most numbers of an MPS file are small integers: no BigInt text parse.
    let unsigned = text.strip_prefix(['+', '-']).unwrap_or(text);
    if (1..=18).contains(&unsigned.len()) && unsigned.bytes().all(|b| b.is_ascii_digit()) {
        return text
            .parse::<i64>()
            .ok()
            .map(|v| BigRational::from_integer(BigInt::from(v)));
    }
    let mut pos = 0;
    let negative = match bytes.first() {
        Some(b'-') => {
            pos = 1;
            true
        }
        Some(b'+') => {
            pos = 1;
            false
        }
        _ => false,
    };
    let int_start = pos;
    while bytes.get(pos).is_some_and(u8::is_ascii_digit) {
        pos += 1;
    }
    let int_digits = &text[int_start..pos];
    let mut frac_digits = "";
    if bytes.get(pos) == Some(&b'.') {
        pos += 1;
        let frac_start = pos;
        while bytes.get(pos).is_some_and(u8::is_ascii_digit) {
            pos += 1;
        }
        frac_digits = &text[frac_start..pos];
    }
    if int_digits.is_empty() && frac_digits.is_empty() {
        return None;
    }
    let mut exponent: i64 = 0;
    if matches!(bytes.get(pos), Some(b'e' | b'E')) {
        pos += 1;
        let exp_negative = match bytes.get(pos) {
            Some(b'-') => {
                pos += 1;
                true
            }
            Some(b'+') => {
                pos += 1;
                false
            }
            _ => false,
        };
        let exp_start = pos;
        while bytes.get(pos).is_some_and(u8::is_ascii_digit) {
            pos += 1;
        }
        let exp_digits = text[exp_start..pos].trim_start_matches('0');
        if pos == exp_start {
            return None;
        }
        if exp_digits.len() > 6 {
            return None;
        }
        let magnitude: i64 = if exp_digits.is_empty() {
            0
        } else {
            exp_digits.parse().ok()?
        };
        if magnitude > 2 * MAX_DECIMAL_EXPONENT {
            return None;
        }
        exponent = if exp_negative { -magnitude } else { magnitude };
    }
    if pos != bytes.len() {
        return None;
    }
    let digits = format!("{int_digits}{frac_digits}");
    let significant = digits.trim_start_matches('0');
    if significant.is_empty() {
        return Some(BigRational::zero());
    }
    let frac_len = i64::try_from(frac_digits.len()).ok()?;
    let power = exponent.checked_sub(frac_len)?;
    // The value is significant * 10^power; its decimal magnitude is about
    // len(significant) + power.
    let magnitude = i64::try_from(significant.len()).ok()?.checked_add(power)?;
    if !(-MAX_DECIMAL_EXPONENT..=MAX_DECIMAL_EXPONENT).contains(&magnitude) {
        return None;
    }
    let mut numer: BigInt = significant.parse().ok()?;
    if negative {
        numer = -numer;
    }
    let ten = BigInt::from(10u8);
    let value = if power >= 0 {
        BigRational::from_integer(numer * ten.pow(u32::try_from(power).ok()?))
    } else {
        BigRational::new(numer, ten.pow(u32::try_from(-power).ok()?))
    };
    in_f64_range(&value).then_some(value)
}

/// Whether an `f64` can approximate `value` without overflow or underflow to
/// zero.
#[must_use]
pub fn in_f64_range(value: &BigRational) -> bool {
    if value.is_zero() {
        return true;
    }
    match value.abs().to_f64() {
        Some(f) => f.is_finite() && f >= f64::MIN_POSITIVE,
        None => false,
    }
}

/// The text ay writes for `value`: the exact integer or terminating decimal
/// when it fits [`MAX_CHECKER_NUMBER_LEN`] characters, otherwise the shortest
/// text that reads back as the nearest `f64` (plain or with an exponent,
/// whichever is shorter). `None` when no text of that length exists.
///
/// The text may differ from `value`; [`crate::ExactProblem::check_written`]
/// checks the texts themselves, read back with [`parse_decimal`].
#[must_use]
pub fn write_value(value: &BigRational) -> Option<String> {
    if let Some(text) = exact_decimal(value) {
        if text.len() <= MAX_CHECKER_NUMBER_LEN {
            return Some(text);
        }
    }
    let f = value.to_f64()?;
    if !f.is_finite() {
        return None;
    }
    let plain = format!("{f}");
    let scientific = format!("{f:e}");
    let text = if scientific.len() < plain.len() {
        scientific
    } else {
        plain
    };
    (text.len() <= MAX_CHECKER_NUMBER_LEN).then_some(text)
}

/// The exact decimal expansion of `value` when its denominator divides a
/// power of ten, `None` otherwise or when it would be long.
fn exact_decimal(value: &BigRational) -> Option<String> {
    let mut denom = value.denom().clone();
    let two = BigInt::from(2u8);
    let five = BigInt::from(5u8);
    let mut twos: u32 = 0;
    let mut fives: u32 = 0;
    while denom.is_even() {
        denom /= &two;
        twos += 1;
        if twos > 64 {
            return None;
        }
    }
    while (&denom % &five).is_zero() {
        denom /= &five;
        fives += 1;
        if fives > 64 {
            return None;
        }
    }
    if !denom.is_one() {
        return None;
    }
    let places = twos.max(fives);
    let scaled = value * BigRational::from_integer(BigInt::from(10u8).pow(places));
    let scaled = scaled.to_integer();
    let negative = scaled.is_negative();
    let digits = scaled.abs().to_string();
    let places = usize::try_from(places).ok()?;
    let text = if places == 0 {
        digits
    } else if digits.len() > places {
        let (int, frac) = digits.split_at(digits.len() - places);
        format!("{int}.{frac}")
    } else {
        format!("0.{}{digits}", "0".repeat(places - digits.len()))
    };
    let text = if text.contains('.') {
        text.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        text
    };
    Some(if negative { format!("-{text}") } else { text })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn reads_the_rational_a_decimal_denotes() {
        assert_eq!(parse_decimal("0.1"), Some(rat(1, 10)));
        assert_eq!(parse_decimal("-.5"), Some(rat(-1, 2)));
        assert_eq!(parse_decimal("+5."), Some(rat(5, 1)));
        assert_eq!(parse_decimal("1E+03"), Some(rat(1000, 1)));
        assert_eq!(parse_decimal("25e-3"), Some(rat(1, 40)));
        assert_eq!(parse_decimal("-0"), Some(rat(0, 1)));
        assert_eq!(
            parse_decimal("9007199254740993"),
            Some(BigRational::from_integer(BigInt::from(
                9_007_199_254_740_993_i64
            )))
        );
        assert_eq!(
            parse_decimal("9.007199254740993e15"),
            Some(BigRational::from_integer(BigInt::from(
                9_007_199_254_740_993_i64
            )))
        );
    }

    #[test]
    fn refuses_what_the_checker_reads_differently_or_out_of_range() {
        for bad in [
            "", "+", "-", ".", "e5", "1e", "1e+", "1/3", "inf", "Infinity", "NaN", "0x10", "1.5D3",
            "1.2.3", " 1", "1 ", "1e5x", "1e999", "1e-999", "1e400", "--1",
        ] {
            assert_eq!(parse_decimal(bad), None, "{bad:?}");
        }
        assert!(parse_decimal("1e308").is_some());
        assert!(parse_decimal("0e999999").is_none());
    }

    #[test]
    fn writes_exact_decimals_and_short_approximations() {
        assert_eq!(write_value(&rat(1, 40)).as_deref(), Some("0.025"));
        assert_eq!(write_value(&rat(-3, 1)).as_deref(), Some("-3"));
        assert_eq!(write_value(&rat(0, 1)).as_deref(), Some("0"));
        assert_eq!(
            write_value(&BigRational::from_integer(BigInt::from(
                9_007_199_254_740_993_i64
            )))
            .as_deref(),
            Some("9007199254740993")
        );
        // 1/3 has no terminating decimal: the nearest f64's shortest text.
        assert_eq!(
            write_value(&rat(1, 3)).as_deref(),
            Some("0.3333333333333333")
        );
        for v in [rat(1, 3), rat(2, 7), rat(-123_456_789, 1000)] {
            let text = write_value(&v).expect("text");
            assert!(text.len() <= MAX_CHECKER_NUMBER_LEN);
            assert!(parse_decimal(&text).is_some(), "{text}");
        }
    }
}
