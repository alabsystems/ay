// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `indexed.rs` to keep indexed pseudo-Boolean
// parameter parsing in the elaborator's private namespace.

/// Parse the sole `at-most` / `at-least` parameter exactly as Z3 5.0.0 does.
/// Its declaration plugin requires a non-negative machine `int`; decimals,
/// negative values, and values above `INT_MAX` are rejected.
fn parse_cardinality_index(index: &ParsedIndex, op: &str) -> Result<BigInt> {
    let value = parse_unsigned_index_value(index).ok_or_else(|| {
        ElaborateError::InvalidConstant(format!(
            "{op}: expected one non-negative integer parameter, got '{}'",
            index.text()
        ))
    })?;
    if value > BigInt::from(i32::MAX) {
        return Err(ElaborateError::InvalidConstant(format!(
            "{op}: parameter '{}' does not fit Z3's non-negative machine int",
            index.text()
        )));
    }
    Ok(value)
}

/// Parse one `pble` / `pbge` / `pbeq` parameter as the rational value produced
/// by Z3 5.0.0's SMT2 indexed-identifier parser. Unsigned numeral/bitvector
/// indices that fit `unsigned` are first stored in a signed `int` parameter,
/// including the 2^31..2^32-1 wraparound of that exact release. Larger values,
/// decimals, and negative numeric tokens remain exact rationals.
fn parse_pb_rational_index(index: &ParsedIndex, op: &str) -> Result<BigRational> {
    if let Some(value) = parse_unsigned_index_value(index) {
        if value <= BigInt::from(u32::MAX) {
            let unsigned = value.to_u32_digits().1.first().copied().unwrap_or(0);
            return Ok(BigRational::from_integer(BigInt::from(unsigned as i32)));
        }
        return Ok(BigRational::from_integer(value));
    }

    let text = match index {
        ParsedIndex::Decimal(text) => text.as_str(),
        ParsedIndex::Symbol(text) if is_negative_decimal_text(text) => text.as_str(),
        _ => {
            return Err(ElaborateError::InvalidConstant(format!(
                "{op}: expected a rational parameter, got '{}'",
                index.text()
            )));
        }
    };
    parse_decimal_rational(text).ok_or_else(|| {
        ElaborateError::InvalidConstant(format!("{op}: invalid rational parameter '{text}'"))
    })
}

fn parse_unsigned_index_value(index: &ParsedIndex) -> Option<BigInt> {
    match index {
        ParsedIndex::Numeral(text) => text.parse().ok(),
        ParsedIndex::Hexadecimal(text) => {
            BigInt::parse_bytes(text.strip_prefix("#x")?.as_bytes(), 16)
        }
        ParsedIndex::Binary(text) => BigInt::parse_bytes(text.strip_prefix("#b")?.as_bytes(), 2),
        _ => None,
    }
}

fn is_negative_decimal_text(text: &str) -> bool {
    let Some(magnitude) = text.strip_prefix('-') else {
        return false;
    };
    let mut parts = magnitude.split('.');
    let Some(integer) = parts.next() else {
        return false;
    };
    let fraction = parts.next();
    parts.next().is_none()
        && !integer.is_empty()
        && integer.bytes().all(|byte| byte.is_ascii_digit())
        && fraction.is_none_or(|digits| {
            !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn parse_decimal_rational(text: &str) -> Option<BigRational> {
    let (negative, magnitude) = text
        .strip_prefix('-')
        .map_or((false, text), |magnitude| (true, magnitude));
    let (integer, fraction) = magnitude.split_once('.').unwrap_or((magnitude, ""));
    let integer = integer.parse::<BigInt>().ok()?;
    let denominator = BigInt::from(10).pow(u32::try_from(fraction.len()).ok()?);
    let fraction = if fraction.is_empty() {
        BigInt::from(0)
    } else {
        fraction.parse::<BigInt>().ok()?
    };
    let numerator = integer * &denominator + fraction;
    Some(BigRational::new(
        if negative { -numerator } else { numerator },
        denominator,
    ))
}
