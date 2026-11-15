// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact, width-checked IEEE fields. Arithmetic admission belongs to callers.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::sync::Arc;

/// An SMT-LIB FP value without a machine-integer field-size restriction.
///
/// NaNs normalize to the single abstract SMT-LIB NaN. Zero keeps its sign.
/// The fields are private so width checks cannot be lost between decoding,
/// comparison and publication. No constructor rounds or truncates a field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fields {
    sign: bool,
    exponent: Arc<BigUint>,
    fraction: Arc<BigUint>,
    eb: u32,
    sb: u32,
}

impl Fields {
    /// Validate unsigned raw fields without rounding or truncation.
    /// NaNs canonicalize only after both fields pass their declared widths.
    /// This admits data; callers retain their own work and allocation limits.
    pub fn new(sign: bool, exponent: BigUint, fraction: BigUint, eb: u32, sb: u32) -> Option<Self> {
        Self::from_shared(sign, Arc::new(exponent), Arc::new(fraction), eb, sb)
    }

    /// Validate immutable shared raw fields without copying either payload.
    /// This transfers data only, with the same width checks as `new`.
    pub fn from_shared(
        sign: bool,
        exponent: Arc<BigUint>,
        fraction: Arc<BigUint>,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        if eb < 2
            || sb < 2
            || eb.checked_add(sb).is_none()
            || exponent.bits() > u64::from(eb)
            || fraction.bits() > u64::from(sb - 1)
        {
            return None;
        }
        let mut result = Self {
            sign,
            exponent,
            fraction,
            eb,
            sb,
        };
        if result.is_nan() {
            result.sign = false;
            result.fraction = Arc::new(BigUint::one());
        }
        Some(result)
    }

    pub(crate) fn decode(bits: &BigInt, eb: u32, sb: u32) -> Option<Self> {
        if eb < 2 || sb < 2 {
            return None;
        }
        eb.checked_add(sb)?;
        let width = u64::from(eb) + u64::from(sb);
        if bits.bits() > width {
            return None;
        }
        let payload = bits.to_biguint()?;
        let sign = payload.bit(width - 1);
        let payload = if sign {
            payload ^ (BigUint::one() << usize::try_from(width - 1).ok()?)
        } else {
            payload
        };
        let stored = usize::try_from(sb - 1).ok()?;
        let exponent = &payload >> stored;
        // Split at the actual occupied bits. A mask of the declared precision
        // could allocate gigabytes even for a tiny zero-valued input.
        let fraction = payload - (&exponent << stored);
        Self::new(sign, exponent, fraction, eb, sb)
    }

    pub(crate) fn native(&self) -> Option<(bool, u64, u128, u32, u32)> {
        Some((
            self.sign,
            u64::try_from(self.exponent.as_ref()).ok()?,
            u128::try_from(self.fraction.as_ref()).ok()?,
            self.eb,
            self.sb,
        ))
    }

    /// Sign bit; abstract NaN has the canonical nonnegative representation.
    pub const fn sign(&self) -> bool {
        self.sign
    }

    /// Exact biased exponent, borrowed without copying its variable-sized data.
    pub fn exponent(&self) -> &BigUint {
        &self.exponent
    }

    /// Exact stored fraction, excluding the implicit leading bit.
    pub fn significand(&self) -> &BigUint {
        &self.fraction
    }

    /// Share the immutable unsigned fields without copying their payloads.
    /// Recipients must perform their own type, work and arithmetic admission.
    pub fn shared_fields(&self) -> (Arc<BigUint>, Arc<BigUint>) {
        (Arc::clone(&self.exponent), Arc::clone(&self.fraction))
    }

    /// Declared exponent width.
    pub const fn exponent_bits(&self) -> u32 {
        self.eb
    }

    /// Declared precision, including the implicit leading bit.
    pub const fn significand_bits(&self) -> u32 {
        self.sb
    }

    pub(crate) fn with_sign(&self, sign: bool) -> Self {
        let mut result = self.clone();
        result.sign = sign && !result.is_nan();
        result
    }

    pub(crate) fn encode(&self) -> (BigInt, u32) {
        let stored = (self.sb - 1) as usize;
        let payload = (self.exponent.as_ref() << stored) | self.fraction.as_ref();
        let width = self.eb + self.sb;
        let payload = if self.sign {
            payload | (BigUint::one() << (width - 1) as usize)
        } else {
            payload
        };
        (BigInt::from(payload), width)
    }

    pub(crate) fn is_nan(&self) -> bool {
        self.exponent_all_ones() && !self.fraction.is_zero()
    }

    pub(crate) fn is_infinite(&self) -> bool {
        self.exponent_all_ones() && self.fraction.is_zero()
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.exponent.is_zero() && self.fraction.is_zero()
    }

    fn exponent_all_ones(&self) -> bool {
        // No allocation proportional to an unoccupied declared exponent width.
        self.exponent.bits() == u64::from(self.eb)
            && self.exponent.trailing_ones() == u64::from(self.eb)
    }

    pub(crate) fn numeric_order(&self, other: &Self) -> Option<Ordering> {
        if (self.eb, self.sb) != (other.eb, other.sb) || self.is_nan() || other.is_nan() {
            return None;
        }
        if self.is_zero() && other.is_zero() {
            return Some(Ordering::Equal);
        }
        if self.sign != other.sign {
            return Some(if self.sign {
                Ordering::Less
            } else {
                Ordering::Greater
            });
        }
        let order = (&self.exponent, &self.fraction).cmp(&(&other.exponent, &other.fraction));
        Some(if self.sign { order.reverse() } else { order })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decoding_keeps_both_ends_of_a_199_bit_fraction() {
        let fraction = (BigUint::one() << 198usize) | BigUint::one();
        let packed = (BigUint::from(127u32) << 199usize) | &fraction;
        let value = Fields::decode(&BigInt::from(packed), 8, 200).unwrap();
        assert_eq!(value.exponent(), &BigUint::from(127u32));
        assert_eq!(value.significand(), &fraction);
        assert!(!value.sign);
        assert!(value.native().is_none());
        let truncated = Fields::new(false, 127u32.into(), BigUint::one(), 8, 200).unwrap();
        assert_ne!(value, truncated);
        assert_eq!(value.numeric_order(&truncated), Some(Ordering::Greater));
    }

    #[test]
    fn invalid_fields_are_rejected_before_nan_normalization() {
        assert!(Fields::new(false, 256u32.into(), 1u32.into(), 8, 200).is_none());
        assert!(Fields::new(false, 255u32.into(), BigUint::one() << 199usize, 8, 200).is_none());
        assert!(Fields::decode(&BigInt::from(-1), 8, 200).is_none());
        assert!(Fields::decode(&(BigInt::one() << 208usize), 8, 200).is_none());
        for (eb, sb) in [(0, 200), (1, 200), (8, 0), (8, 1)] {
            assert!(Fields::decode(&BigInt::zero(), eb, sb).is_none());
        }
    }

    #[test]
    fn nan_identity_and_numeric_zero_follow_distinct_smt_relations() {
        let exponent = (BigUint::one() << 80usize) - BigUint::one();
        let a = Fields::new(false, exponent.clone(), 1u32.into(), 80, 200).unwrap();
        let b = Fields::new(true, exponent.clone(), BigUint::one() << 198usize, 80, 200).unwrap();
        assert_eq!(a, b);
        assert!(a.is_nan());
        assert_eq!(a.numeric_order(&b), None);
        let infinity = Fields::new(false, exponent, BigUint::zero(), 80, 200).unwrap();
        assert!(infinity.is_infinite());
        assert_ne!(a, infinity);
        let pos = Fields::new(false, BigUint::zero(), BigUint::zero(), 8, 200).unwrap();
        let neg = Fields::new(true, BigUint::zero(), BigUint::zero(), 8, 200).unwrap();
        assert_ne!(pos, neg);
        assert_eq!(pos.numeric_order(&neg), Some(Ordering::Equal));
    }

    #[test]
    fn sparse_declared_formats_do_not_allocate_their_unoccupied_widths() {
        let value = Fields::decode(&BigInt::one(), 2, u32::MAX - 2).unwrap();
        assert_eq!(value.significand(), &BigUint::one());
        assert_eq!(value.exponent(), &BigUint::zero());
        assert!(!value.is_nan());
        assert!(Fields::decode(&BigInt::one(), u32::MAX, u32::MAX).is_none());
    }
}
