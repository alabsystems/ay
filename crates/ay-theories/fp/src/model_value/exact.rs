// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact field admission for the model's u64 exponent / u128 fraction carrier.

use super::FpModelValue;
use crate::RoundingMode;
use num_bigint::{BigInt, BigUint};
use std::cmp::Ordering;

fn supported_fields(eb: u32, sb: u32) -> bool {
    (2..=63).contains(&eb) && (2..=129).contains(&sb)
}

fn fraction_fits(significand: u128, sb: u32) -> bool {
    u128::BITS - significand.leading_zeros() <= sb - 1
}

impl FpModelValue {
    /// Construct exact owned fields, retaining every occupied bit.
    ///
    /// Native formats keep their existing representation. Wider fields share
    /// immutable storage; accepting data does not authorize rational arithmetic.
    pub fn from_exact_fields(
        sign: bool,
        exponent: BigUint,
        significand: BigUint,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        let fields = super::fields::Fields::new(sign, exponent, significand, eb, sb)?;
        if supported_fields(eb, sb) {
            let (sign, exponent, significand, _, _) = fields.native()?;
            Self::from_fields(sign, exponent, significand, eb, sb)
        } else {
            Some(Self::Exact(fields))
        }
    }

    pub(crate) fn exact_fields(&self) -> Option<super::FpFields> {
        if let Self::Exact(fields) = self {
            return Some(fields.clone());
        }
        if let Self::Fp {
            sign,
            exponent,
            significand,
            eb,
            sb,
        } = self
        {
            return super::fields::Fields::new(
                *sign,
                (*exponent).into(),
                (*significand).into(),
                *eb,
                *sb,
            );
        }
        if let Self::PosZero { eb, sb } | Self::NegZero { eb, sb } = self {
            return super::fields::Fields::new(
                self.is_negative(),
                0u32.into(),
                0u32.into(),
                *eb,
                *sb,
            );
        }
        if !supported_fields(self.eb(), self.sb()) {
            return None;
        }
        super::fields::Fields::decode(&self.to_ieee_bv().0, self.eb(), self.sb())
    }

    /// Construct an exact value from unsigned IEEE fields, without truncation.
    ///
    /// Every format whose individual fields fit the model carrier is accepted. Field
    /// overflow and other formats return `None`; zero and special encodings are
    /// canonicalized. NaN payloads are deliberately not retained (SMT-LIB has
    /// one NaN value). Callers decoding typed bitvectors must also check their
    /// declared widths against `1`, `eb`, and `sb - 1` respectively.
    pub fn from_fields(
        sign: bool,
        exponent: u64,
        significand: u128,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        if !supported_fields(eb, sb) {
            return None;
        }
        let max_exp = (1u64 << eb) - 1;
        if exponent > max_exp || !fraction_fits(significand, sb) {
            return None;
        }
        Some(if exponent == max_exp {
            if significand != 0 {
                Self::NaN { eb, sb }
            } else if sign {
                Self::NegInf { eb, sb }
            } else {
                Self::PosInf { eb, sb }
            }
        } else if exponent == 0 && significand == 0 {
            if sign {
                Self::NegZero { eb, sb }
            } else {
                Self::PosZero { eb, sb }
            }
        } else {
            Self::Fp {
                sign,
                exponent,
                significand,
                eb,
                sb,
            }
        })
    }

    /// Decode a non-negative `eb + sb`-bit IEEE encoding exactly.
    ///
    /// Rejects negative/out-of-width values rather than reducing modulo the
    /// width. A typed-bitvector caller must separately check its declared width.
    /// NaN encodings normalize to the single SMT-LIB NaN value.
    pub fn from_ieee_bv(bits: &BigInt, eb: u32, sb: u32) -> Option<Self> {
        let fields = super::fields::Fields::decode(bits, eb, sb)?;
        if supported_fields(eb, sb) {
            let (sign, exponent, significand, _, _) = fields.native()?;
            Self::from_fields(sign, exponent, significand, eb, sb)
        } else {
            Some(Self::Exact(fields))
        }
    }

    pub(crate) fn numeric_order(&self, other: &Self) -> Option<Ordering> {
        if matches!(self, Self::Exact(_)) || matches!(other, Self::Exact(_)) {
            if (self.eb(), self.sb()) != (other.eb(), other.sb()) || self.is_nan() || other.is_nan()
            {
                return None;
            }
            if self.is_infinite() {
                return Some(
                    if other.is_infinite() && self.is_negative() == other.is_negative() {
                        Ordering::Equal
                    } else if self.is_negative() {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    },
                );
            }
            if other.is_infinite() {
                return Some(if other.is_negative() {
                    Ordering::Greater
                } else {
                    Ordering::Less
                });
            }
            return self.exact_fields()?.numeric_order(&other.exact_fields()?);
        }
        if (self.eb(), self.sb()) != (other.eb(), other.sb()) {
            // Preserve the old cross-format behavior where f64 is exact.
            return self.to_f64()?.partial_cmp(&other.to_f64()?);
        }
        let (a_sign, a_exp, a_sig) = self.ordered_fields()?;
        let (b_sign, b_exp, b_sig) = other.ordered_fields()?;
        if (a_exp, a_sig) == (0, 0) && (b_exp, b_sig) == (0, 0) {
            return Some(Ordering::Equal);
        }
        if a_sign != b_sign {
            return Some(if a_sign {
                Ordering::Less
            } else {
                Ordering::Greater
            });
        }
        let order = (a_exp, a_sig).cmp(&(b_exp, b_sig));
        Some(if a_sign { order.reverse() } else { order })
    }

    fn ordered_fields(&self) -> Option<(bool, u64, u128)> {
        if !supported_fields(self.eb(), self.sb()) {
            return None;
        }
        let max_exp = (1u64 << self.eb()) - 1;
        match *self {
            Self::Exact(_) => None,
            Self::NaN { .. } => None,
            Self::PosZero { .. } => Some((false, 0, 0)),
            Self::NegZero { .. } => Some((true, 0, 0)),
            Self::PosInf { .. } => Some((false, max_exp, 0)),
            Self::NegInf { .. } => Some((true, max_exp, 0)),
            Self::Fp {
                sign,
                exponent,
                significand,
                sb,
                ..
            } if exponent < max_exp && fraction_fits(significand, sb) => {
                Some((sign, exponent, significand))
            }
            Self::Fp { .. } => None,
        }
    }

    pub(crate) fn rounded_overflow(sign: bool, eb: u32, sb: u32, rm: RoundingMode) -> Self {
        // Same directed-overflow rule as this crate's exact round_const path.
        let infinity = match rm {
            RoundingMode::RNE | RoundingMode::RNA => true,
            RoundingMode::RTZ => false,
            RoundingMode::RTP => !sign,
            RoundingMode::RTN => sign,
        };
        if infinity {
            if sign {
                Self::NegInf { eb, sb }
            } else {
                Self::PosInf { eb, sb }
            }
        } else {
            Self::Fp {
                sign,
                exponent: (1u64 << eb) - 2,
                significand: u128::MAX >> (129 - sb),
                eb,
                sb,
            }
        }
    }
}

#[cfg(test)]
mod tests;
