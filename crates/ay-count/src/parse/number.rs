// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `parse` so the public functions retain their DefPaths.

/// Parse an exact rational from decimal (`0.4`, `-12`, `.5`), scientific
/// (`1.23e+4`), or fraction (`3/10`) notation.
///
/// # Errors
///
/// Returns [`ParseError`] when the token is empty, malformed, has a zero
/// denominator, or requires a decimal exponent outside the supported bound.
pub fn parse_rational(s: &str) -> Result<BigRational, ParseError> {
    let s = s.trim();
    if s.is_empty() {
        return err("empty number");
    }
    if let Some(slash) = s.find('/') {
        let (num_str, den_str) = (&s[..slash], &s[slash + 1..]);
        let num = BigInt::from_str(num_str.trim())
            .map_err(|_| ParseError(format!("invalid fraction numerator `{num_str}`")))?;
        let den = BigInt::from_str(den_str.trim())
            .map_err(|_| ParseError(format!("invalid fraction denominator `{den_str}`")))?;
        if den.is_zero() {
            return err(format!("zero denominator in fraction `{s}`"));
        }
        return Ok(BigRational::new(num, den));
    }

    // Decimal, possibly with exponent: [-+]?digits[.digits][eE[-+]?digits]
    let (mantissa, exp10) = match s.find(['e', 'E']) {
        Some(epos) => {
            let exp_str = &s[epos + 1..];
            let exp: i64 = exp_str
                .parse()
                .map_err(|_| ParseError(format!("invalid exponent `{exp_str}`")))?;
            (&s[..epos], exp)
        }
        None => (s, 0i64),
    };
    let (int_part, frac_part) = match mantissa.find('.') {
        Some(dot) => (&mantissa[..dot], &mantissa[dot + 1..]),
        None => (mantissa, ""),
    };
    let (negative, int_digits) = match int_part.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, int_part.strip_prefix('+').unwrap_or(int_part)),
    };
    if int_digits.is_empty() && frac_part.is_empty() {
        return err(format!("invalid number `{s}`"));
    }
    if !int_digits.chars().all(|c| c.is_ascii_digit())
        || !frac_part.chars().all(|c| c.is_ascii_digit())
    {
        return err(format!("invalid number `{s}`"));
    }

    let scale = i64::try_from(frac_part.len())
        .map_err(|_| ParseError(format!("decimal scale is too large in `{s}`")))?;
    let net_exp = exp10
        .checked_sub(scale)
        .ok_or_else(|| ParseError(format!("decimal exponent overflows in `{s}`")))?;
    let exponent = net_exp.unsigned_abs();
    if exponent > MAX_DECIMAL_EXPONENT_ABS {
        return err(format!(
            "decimal exponent magnitude {exponent} exceeds the supported maximum {MAX_DECIMAL_EXPONENT_ABS}"
        ));
    }
    let exponent = u32::try_from(exponent)
        .map_err(|_| ParseError(format!("decimal exponent is too large in `{s}`")))?;

    let digits = format!("{int_digits}{frac_part}");
    let mut num = BigInt::from(
        BigUint::from_str(&digits).map_err(|_| ParseError(format!("invalid number `{s}`")))?,
    );
    if num.is_zero() {
        // Avoid constructing 10^exponent for compact spellings such as
        // `0e1000000`; every signed/scaled representation of zero is exact 0.
        return Ok(BigRational::zero());
    }
    if negative {
        num = -num;
    }
    let ten = BigInt::from(10u32);
    Ok(if net_exp >= 0 {
        BigRational::from_integer(num * ten.pow(exponent))
    } else {
        BigRational::new(num, ten.pow(exponent))
    })
}

/// Parse a weight token as a real rational or complex `a+bi` / `a-bi` value.
/// A rational coefficient followed by `i` (for example, `0.5i`) is accepted as
/// an unambiguous pure-imaginary extension.
///
/// # Errors
///
/// Returns [`ParseError`] when the real token or either complex component is
/// not accepted by [`parse_rational`].
pub fn parse_weight(s: &str) -> Result<RawWeight, ParseError> {
    let s = s.trim();
    if let Some(body) = s.strip_suffix(['i', 'I']) {
        // Find the split sign: last '+'/'-' not at position 0 and not directly
        // after an exponent marker (so `1.2e+3+0.5i` splits at the second '+').
        let bytes = body.as_bytes();
        let mut split = None;
        for idx in (1..bytes.len()).rev() {
            let b = bytes[idx];
            if (b == b'+' || b == b'-') && !matches!(bytes[idx - 1], b'e' | b'E') {
                split = Some(idx);
                break;
            }
        }
        let Some(idx) = split else {
            return Ok(RawWeight::Complex(
                BigRational::zero(),
                parse_rational(body)?,
            ));
        };
        let re = parse_rational(&body[..idx])?;
        let im_str = &body[idx..];
        let im = if im_str == "+" {
            BigRational::one()
        } else if im_str == "-" {
            -BigRational::one()
        } else {
            parse_rational(im_str)?
        };
        Ok(RawWeight::Complex(re, im))
    } else {
        Ok(RawWeight::Rat(parse_rational(s)?))
    }
}

fn rational_expanded_bits(value: &BigRational) -> Result<u64, ParseError> {
    value
        .numer()
        .bits()
        .checked_add(value.denom().bits())
        .ok_or_else(|| ParseError("expanded rational bit count overflows".into()))
}

fn raw_weight_expanded_bits(weight: &RawWeight) -> Result<u64, ParseError> {
    match weight {
        RawWeight::Rat(value) => rational_expanded_bits(value),
        RawWeight::Complex(real, imaginary) => rational_expanded_bits(real)?
            .checked_add(rational_expanded_bits(imaginary)?)
            .ok_or_else(|| ParseError("expanded complex-weight bit count overflows".into())),
    }
}

fn checked_total_weight_bits(current: u64, additional: u64) -> Result<u64, ParseError> {
    let total = current
        .checked_add(additional)
        .ok_or_else(|| ParseError("aggregate expanded-weight bit count overflows".into()))?;
    if total > MAX_TOTAL_WEIGHT_BITS {
        return err(format!(
            "aggregate expanded weights require {total} bits, exceeding the supported maximum {MAX_TOTAL_WEIGHT_BITS}"
        ));
    }
    Ok(total)
}

fn validate_total_weight_bits(raw: &[(i32, RawWeight)]) -> Result<u64, ParseError> {
    raw.iter().try_fold(0, |total, (_, weight)| {
        checked_total_weight_bits(total, raw_weight_expanded_bits(weight)?)
    })
}

fn charge_parsed_weight(
    current: u64,
    token_len: usize,
    weight: &RawWeight,
) -> Result<u64, ParseError> {
    let token_len = u64::try_from(token_len)
        .map_err(|_| ParseError("weight token length does not fit the parser budget".into()))?;
    let proportional_limit = token_len
        .checked_mul(WEIGHT_EXPANSION_BITS_PER_INPUT_BYTE)
        .ok_or_else(|| ParseError("weight token expansion limit overflows".into()))?;
    let expanded_bits = raw_weight_expanded_bits(weight)?;
    if expanded_bits > proportional_limit {
        return err(format!(
            "expanded weight requires {expanded_bits} bits, exceeding the {proportional_limit}-bit limit for its {token_len}-byte token"
        ));
    }
    checked_total_weight_bits(current, expanded_bits)
}
