// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use num_traits::Zero;

impl Decoder<'_> {
    fn digits(&mut self, text: &str, radix: u32) -> Option<BigInt> {
        self.charge(text.len().checked_add(1)?)?;
        if text.is_empty()
            || !text.bytes().all(|byte| match radix {
                2 => matches!(byte, b'0' | b'1'),
                10 => byte.is_ascii_digit(),
                16 => byte.is_ascii_hexdigit(),
                _ => false,
            })
        {
            return None;
        }
        self.copy(text.len().checked_mul(4)?.checked_add(64)?)?;
        BigInt::parse_bytes(text.as_bytes(), radix)
    }

    pub(super) fn integer(&mut self, value: &SExpr, depth: usize) -> Option<BigInt> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match value {
            SExpr::Numeral(text) => self.digits(text, 10),
            SExpr::List(items) => {
                let [head, inner] = items.as_slice() else {
                    return None;
                };
                head.is_symbol("-").then_some(())?;
                Some(-self.integer(inner, depth + 1)?)
            }
            _ => None,
        }
    }

    pub(super) fn real(&mut self, value: &SExpr, depth: usize) -> Option<BigRational> {
        self.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        match value {
            SExpr::Numeral(text) => Some(BigRational::from_integer(self.digits(text, 10)?)),
            SExpr::Decimal(text) => {
                let (whole, fraction) = text.split_once('.')?;
                let left = self.digits(whole, 10)?;
                let right = self.digits(fraction, 10)?;
                self.copy(text.len().checked_mul(16)?.checked_add(256)?)?;
                let power = u32::try_from(fraction.len()).ok()?;
                let denominator = BigInt::from(10).pow(power);
                Some(BigRational::new(left * &denominator + right, denominator))
            }
            SExpr::List(items) => match items.as_slice() {
                [head, inner] if head.is_symbol("-") => Some(-self.real(inner, depth + 1)?),
                [head, numerator, denominator] if head.is_symbol("/") => {
                    let numerator = self.real(numerator, depth + 1)?;
                    let denominator = self.real(denominator, depth + 1)?;
                    if denominator.is_zero() {
                        return None;
                    }
                    let bits = numerator
                        .numer()
                        .bits()
                        .checked_add(numerator.denom().bits())?
                        .checked_add(denominator.numer().bits())?
                        .checked_add(denominator.denom().bits())?;
                    self.copy(
                        usize::try_from(bits)
                            .ok()?
                            .checked_mul(8)?
                            .checked_add(256)?,
                    )?;
                    Some(numerator / denominator)
                }
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn bitvector(&mut self, value: &SExpr, width: u32) -> Option<ModelValue> {
        if width == 0 {
            return None;
        }
        let (number, printed_width) = match value {
            SExpr::Hexadecimal(text) => {
                let digits = text.strip_prefix("#x").unwrap_or(text);
                (
                    self.digits(digits, 16)?,
                    u32::try_from(digits.len()).ok()?.checked_mul(4)?,
                )
            }
            SExpr::Binary(text) => {
                let digits = text.strip_prefix("#b").unwrap_or(text);
                (self.digits(digits, 2)?, u32::try_from(digits.len()).ok()?)
            }
            SExpr::List(items) => {
                let [head, digits, size] = items.as_slice() else {
                    return None;
                };
                if !head.is_symbol("_") {
                    return None;
                }
                let digits = digits.as_symbol()?.strip_prefix("bv")?;
                (self.digits(digits, 10)?, sorts::numeral(size)?)
            }
            _ => return None,
        };
        if printed_width != width
            || number.sign() == Sign::Minus
            || number.bits() > u64::from(width)
        {
            return None;
        }
        Some(ModelValue::BitVec {
            value: number,
            width,
        })
    }
}
