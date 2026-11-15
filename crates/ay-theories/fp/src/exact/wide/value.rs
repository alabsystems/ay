// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked IEEE fields used only by bounded closed arithmetic.

use super::{pow2, Fmt, Val};
use crate::FpModelValue;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Fields are private: every constructor checks the format before shifting,
/// rejects out-of-width integers, and canonicalizes the single logical NaN.
#[derive(Clone, Debug)]
pub(crate) struct Value {
    format: Fmt,
    sign: bool,
    exponent: u64,
    fraction: BigInt,
}

impl Value {
    pub(crate) fn checked_format(eb: u32, sb: u32) -> bool {
        Fmt::checked(eb, sb).is_some()
    }

    pub(crate) fn eb(&self) -> u32 {
        self.format.eb
    }

    pub(crate) fn sb(&self) -> u32 {
        self.format.sb
    }

    pub(super) fn from_fields(
        sign: bool,
        exponent: u64,
        fraction: BigInt,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        let format = Fmt::checked(eb, sb)?;
        if exponent >= (1u64 << eb)
            || fraction.sign() == num_bigint::Sign::Minus
            || fraction.bits() > u64::from(sb - 1)
        {
            return None;
        }
        let nan = exponent == (1u64 << eb) - 1 && !fraction.is_zero();
        Some(Self {
            format,
            sign: !nan && sign,
            exponent,
            fraction: if nan { BigInt::one() } else { fraction },
        })
    }

    pub(super) fn from_ieee_bv(bits: &BigInt, eb: u32, sb: u32) -> Option<Self> {
        Fmt::checked(eb, sb)?;
        let width = eb.checked_add(sb)?;
        if bits.sign() == num_bigint::Sign::Minus || bits.bits() > u64::from(width) {
            return None;
        }
        let exponent = u64::try_from((bits >> (sb - 1)) & ((BigInt::one() << eb) - 1)).ok()?;
        let fraction = bits & ((BigInt::one() << (sb - 1)) - 1);
        Self::from_fields(bits.bit(u64::from(width - 1)), exponent, fraction, eb, sb)
    }

    pub(crate) fn to_ieee_bv(&self) -> (BigInt, u32) {
        let width = self.eb() + self.sb();
        let bits = (BigInt::from(u8::from(self.sign)) << (width - 1))
            | (BigInt::from(self.exponent) << (self.sb() - 1))
            | &self.fraction;
        (bits, width)
    }

    pub(super) fn decode(&self) -> Val {
        if self.exponent == (1u64 << self.eb()) - 1 {
            return if self.fraction.is_zero() {
                Val::Inf(self.sign)
            } else {
                Val::Nan
            };
        }
        if self.exponent == 0 && self.fraction.is_zero() {
            return Val::Fin(self.sign, BigRational::zero());
        }
        let (significand, exponent) = if self.exponent == 0 {
            (self.fraction.clone(), self.format.emin())
        } else {
            (
                (BigInt::one() << (self.sb() - 1)) + &self.fraction,
                self.exponent as i64 - self.format.bias(),
            )
        };
        let magnitude =
            BigRational::from_integer(significand) * pow2(exponent - i64::from(self.sb()) + 1);
        Val::Fin(self.sign, magnitude)
    }

    /// Decode model data under this kernel's independent arithmetic work bounds.
    pub(crate) fn from_model(value: &FpModelValue) -> Option<Self> {
        let (eb, sb) = (value.eb(), value.sb());
        Fmt::checked(eb, sb)?;
        let max_exp = (1u64 << eb) - 1;
        let (sign, exponent, fraction) = match value {
            FpModelValue::Exact(fields) => (
                fields.sign(),
                u64::try_from(fields.exponent()).ok()?,
                BigInt::from(fields.significand().clone()),
            ),
            FpModelValue::PosZero { .. } => (false, 0, BigInt::zero()),
            FpModelValue::NegZero { .. } => (true, 0, BigInt::zero()),
            FpModelValue::PosInf { .. } => (false, max_exp, BigInt::zero()),
            FpModelValue::NegInf { .. } => (true, max_exp, BigInt::zero()),
            FpModelValue::NaN { .. } => (false, max_exp, BigInt::one()),
            FpModelValue::Fp {
                sign,
                exponent,
                significand,
                ..
            } => {
                FpModelValue::from_fields(*sign, *exponent, *significand, eb, sb)?;
                // The public enum is constructible without from_fields. Its
                // finite arm must not gain zero/Inf/NaN authority by decoding
                // a non-finite or non-canonical field encoding here.
                if *exponent >= max_exp || (*exponent == 0 && *significand == 0) {
                    return None;
                }
                (*sign, *exponent, BigInt::from(*significand))
            }
        };
        Self::from_fields(sign, exponent, fraction, eb, sb)
    }

    pub(crate) fn into_model(self) -> Option<FpModelValue> {
        FpModelValue::from_exact_fields(
            self.sign,
            self.exponent.into(),
            self.fraction.to_biguint()?,
            self.eb(),
            self.sb(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_fields_refuse_before_decoding_or_shifting() {
        for (eb, sb) in [(0, 0), (u32::MAX, u32::MAX), (21, 130), (3, 257)] {
            assert!(Value::from_ieee_bv(&BigInt::zero(), eb, sb).is_none());
        }
        assert!(Value::from_ieee_bv(&BigInt::from(-1), 3, 130).is_none());
        assert!(Value::from_ieee_bv(&(BigInt::one() << 133u32), 3, 130).is_none());
        assert!(Value::from_fields(false, 8, BigInt::zero(), 3, 130).is_none());
        assert!(Value::from_fields(false, 0, BigInt::one() << 129u32, 3, 130).is_none());
        let malformed = FpModelValue::Fp {
            sign: false,
            exponent: 8,
            significand: 0,
            eb: 3,
            sb: 64,
        };
        assert!(crate::exact::to_real(&malformed).is_none());
        assert!(crate::exact::add(crate::RoundingMode::RNE, &malformed, &malformed).is_none());
    }

    #[test]
    fn malformed_finite_discriminants_cannot_acquire_special_value_authority() {
        for (exponent, significand) in [(7, 0), (7, 1), (0, 0)] {
            let malformed = FpModelValue::Fp {
                sign: false,
                exponent,
                significand,
                eb: 3,
                sb: 64,
            };
            assert!(crate::exact::classify("fp.isInfinite", &malformed).is_none());
            assert!(crate::exact::classify("fp.isNaN", &malformed).is_none());
            assert!(crate::exact::classify("fp.isZero", &malformed).is_none());
            assert!(crate::exact::neg(&malformed).is_none());
        }
        let inf = FpModelValue::PosInf { eb: 3, sb: 64 };
        let nan = FpModelValue::NaN { eb: 3, sb: 64 };
        let zero = FpModelValue::PosZero { eb: 3, sb: 64 };
        assert_eq!(crate::exact::classify("fp.isInfinite", &inf), Some(true));
        assert_eq!(crate::exact::classify("fp.isNaN", &nan), Some(true));
        assert_eq!(crate::exact::classify("fp.isZero", &zero), Some(true));
    }
}
