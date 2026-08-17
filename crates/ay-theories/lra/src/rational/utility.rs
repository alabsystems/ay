// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Utility operations and standard conversions for [`Rational`].

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::cmp::Ordering;

use super::{try_shrink_num, Rational};

// --- Utility methods --------------------------------------------------------

impl Rational {
    /// Absolute value.
    #[inline]
    pub fn abs(&self) -> Self {
        match self {
            Self::Small(n, d) => {
                if *n >= 0 {
                    self.clone()
                } else if let Some(abs_n) = n.checked_neg() {
                    Self::Small(abs_n, *d)
                } else {
                    {
                        Self::from_rug(num_traits::Signed::abs(&self.to_rug()))
                    }
                }
            }
            Self::Big(br) => Self::from_rug(num_traits::Signed::abs(&**br)),
        }
    }

    /// Signum: 1 for positive, 0 for zero, -1 for negative.
    #[inline]
    pub fn signum(&self) -> Self {
        match self.cmp(&Self::zero()) {
            Ordering::Greater => Self::one(),
            Ordering::Equal => Self::zero(),
            Ordering::Less => Self::Small(-1, 1),
        }
    }

    /// True if strictly positive.
    #[inline]
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Small(n, _) => *n > 0,
            Self::Big(br) => num_traits::Signed::is_positive(&**br),
        }
    }

    /// True if strictly negative.
    #[inline]
    pub fn is_negative(&self) -> bool {
        match self {
            Self::Small(n, _) => *n < 0,
            Self::Big(br) => num_traits::Signed::is_negative(&**br),
        }
    }

    /// Check if the rational is an integer (denominator == 1).
    #[inline]
    pub fn is_integer(&self) -> bool {
        match self {
            Self::Small(_, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => br.is_integer(),
        }
    }

    /// Extract the integer value as i64, if this rational is an integer that
    /// fits in i64. Returns `None` for non-integers or values outside i64 range.
    #[inline]
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            Self::Small(n, 1) => Some(*n),
            Self::Small(_, _) => None,
            Self::Big(br) => {
                if br.is_integer() {
                    {
                        num_traits::ToPrimitive::to_i64(br.numer())
                    }
                } else {
                    None
                }
            }
        }
    }

    /// Try to extract as an `(i64, i64)` pair (numerator, denominator).
    ///
    /// Returns `Some((n, d))` for `Small(n, d)`, `None` for `Big`.
    /// Used by adaptive-precision pivot paths to determine if a coefficient
    /// fits in hardware arithmetic (#8185).
    #[inline]
    pub fn try_as_i64(&self) -> Option<(i64, i64)> {
        match self {
            Self::Small(n, d) => Some((*n, *d)),
            Self::Big(_) => None,
        }
    }

    /// Try to extract as an `(i128, i128)` pair (numerator, denominator).
    ///
    /// Always succeeds for `Small` (widened to i128). For `Big`, attempts
    /// conversion via the bignum `to_i128()`. Returns `None` only when the Big
    /// value exceeds i128 range.
    ///
    /// Used by adaptive-precision pivot paths for intermediate-precision
    /// arithmetic that avoids full BigInt allocation (#8185).
    #[inline]
    pub fn try_as_i128(&self) -> Option<(i128, i128)> {
        match self {
            Self::Small(n, d) => Some((i128::from(*n), i128::from(*d))),
            Self::Big(br) => {
                let n = num_traits::ToPrimitive::to_i128(br.numer())?;
                let d = num_traits::ToPrimitive::to_i128(br.denom())?;
                Some((n, d))
            }
        }
    }

    /// Returns `true` when this rational is an integer that fits in i64.
    #[inline]
    pub fn is_integer_i64(&self) -> bool {
        match self {
            Self::Small(_, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => {
                br.is_integer() && num_traits::ToPrimitive::to_i64(br.numer()).is_some()
            }
        }
    }

    /// Create a Rational from an i128 integer value.
    #[inline]
    pub(crate) fn from_i128(val: i128) -> Self {
        if let Ok(n) = i64::try_from(val) {
            Self::Small(n, 1)
        } else {
            {
                Self::Big(Box::new(BigRational::from(BigInt::from(val))))
            }
        }
    }

    /// Approximate as f64.
    #[inline]
    pub fn approx_f64(&self) -> f64 {
        match self {
            Self::Small(n, d) => *n as f64 / *d as f64,
            Self::Big(br) => num_traits::ToPrimitive::to_f64(&**br).unwrap_or(f64::NAN),
        }
    }

    /// Floor: largest integer <= self.
    pub fn floor(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                if r < 0 {
                    BigInt::from(q - 1)
                } else {
                    BigInt::from(q)
                }
            }
            Self::Big(br) => br.floor().to_integer(),
        }
    }

    /// Floor as `i64`: largest integer <= self, when inline (#C4).
    ///
    /// Returns `None` for the `Big` variant — callers fall back to the
    /// allocating [`Self::floor`]. Exact for every `Small` value: with the
    /// invariant `d > 0`, truncating division adjusted by the remainder sign
    /// is the mathematical floor, and `|n/d| < |n|` for `d > 1` means the
    /// `q - 1` adjustment can never overflow (for `d == 1` the remainder is
    /// zero and no adjustment happens).
    #[inline]
    pub fn floor_int(&self) -> Option<i64> {
        match self {
            Self::Small(n, 1) => Some(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                Some(if r < 0 { q - 1 } else { q })
            }
            Self::Big(_) => None,
        }
    }

    /// Ceil as `i64`: smallest integer >= self, when inline (#C4).
    ///
    /// Returns `None` for the `Big` variant — callers fall back to the
    /// allocating [`Self::ceil`]. Exact for every `Small` value (see
    /// [`Self::floor_int`] for the overflow argument; the `q + 1` adjustment
    /// only fires for `d > 1`).
    #[inline]
    pub fn ceil_int(&self) -> Option<i64> {
        match self {
            Self::Small(n, 1) => Some(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                Some(if r > 0 { q + 1 } else { q })
            }
            Self::Big(_) => None,
        }
    }

    /// Ceil: smallest integer >= self.
    pub fn ceil(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                if r > 0 {
                    BigInt::from(q + 1)
                } else {
                    BigInt::from(q)
                }
            }
            Self::Big(br) => br.ceil().to_integer(),
        }
    }

    /// Reciprocal: 1/self. Panics if zero.
    pub fn recip(&self) -> Self {
        assert!(!self.is_zero(), "Rational: reciprocal of zero");
        match self {
            Self::Small(n, d) => {
                if *n > 0 {
                    Self::Small(*d, *n)
                } else if let (Some(neg_d), Some(neg_n)) = (d.checked_neg(), n.checked_neg()) {
                    Self::Small(neg_d, neg_n)
                } else {
                    Self::from_rug(self.to_rug().recip())
                }
            }
            Self::Big(br) => Self::from_rug(br.recip()),
        }
    }
}

// --- Conversions ------------------------------------------------------------

impl From<i32> for Rational {
    #[inline]
    fn from(n: i32) -> Self {
        Self::Small(i64::from(n), 1)
    }
}

impl From<i64> for Rational {
    #[inline]
    fn from(n: i64) -> Self {
        Self::Small(n, 1)
    }
}

impl From<BigInt> for Rational {
    fn from(n: BigInt) -> Self {
        if let Ok(small) = i64::try_from(&n) {
            Self::Small(small, 1)
        } else {
            {
                Self::Big(Box::new(BigRational::from(n)))
            }
        }
    }
}

impl From<BigRational> for Rational {
    #[inline]
    fn from(br: BigRational) -> Self {
        Self::from_big(br)
    }
}

impl From<&BigRational> for Rational {
    #[inline]
    fn from(br: &BigRational) -> Self {
        // Inspect the borrowed limbs before cloning: exact solver witnesses are
        // stored as `BigRational` even when almost every value fits inline.
        // Cloning first paid two BigInt allocations merely to discard them
        // while shrinking to `Small`.
        try_shrink_num(br).unwrap_or_else(|| Self::Big(Box::new(br.clone())))
    }
}
