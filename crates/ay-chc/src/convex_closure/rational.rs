// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rational number type for convex closure computation.
//!
//! Uses i128 for extended precision during intermediate calculations.
//! Overflow-safe: degrades gracefully to zero on overflow (#1713, #5339).

use num_bigint::BigInt;

/// A rational number represented as numerator/denominator
/// Using i128 for extended precision during intermediate calculations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Rational {
    pub(super) num: i128,
    pub(super) den: i128,
}

impl Rational {
    /// Create a rational from numerator and denominator (used in tests)
    #[cfg(test)]
    pub(crate) fn new(num: i64, den: i64) -> Self {
        let (n, d) = Self::normalize(i128::from(num), i128::from(den));
        Self { num: n, den: d }
    }

    pub(crate) fn from_int(n: i64) -> Self {
        Self {
            num: i128::from(n),
            den: 1,
        }
    }

    pub(crate) fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    /// Return zero as overflow fallback. Logs in debug builds to flag silent
    /// degradation during development. In all builds, gracefully returns zero
    /// to avoid panicking on degenerate Farkas coefficients (#1713, #5339).
    fn overflow_zero(_context: &str) -> Self {
        #[cfg(debug_assertions)]
        eprintln!("Rational i128 overflow in {_context}: returning zero fallback — see #5339");
        Self::zero()
    }

    pub(crate) fn one() -> Self {
        Self { num: 1, den: 1 }
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.num == 0
    }

    /// Check if value is one (used in Gaussian elimination)
    #[cfg(test)]
    pub(crate) fn is_one(&self) -> bool {
        self.num == 1 && self.den == 1
    }

    /// Convert to i64 if possible (integer with value in range).
    pub(crate) fn to_i64(self) -> Option<i64> {
        if self.den == 1 && self.num >= i128::from(i64::MIN) && self.num <= i128::from(i64::MAX) {
            Some(self.num as i64)
        } else {
            None
        }
    }

    /// Absolute value (used in Gaussian elimination pivot selection)
    #[cfg(test)]
    pub(crate) fn abs(&self) -> Self {
        // i128::MIN cannot be abs()'d; degrade gracefully instead of panicking (#1713).
        match self.num.checked_abs() {
            Some(abs_num) => Self {
                num: abs_num,
                den: self.den,
            },
            None => Self::overflow_zero("abs(i128::MIN)"),
        }
    }

    /// Greatest common divisor (GCD). Returns None on overflow (#1713).
    fn gcd(a: i128, b: i128) -> Option<i128> {
        // Operate on unsigned to avoid i128::MIN overflow (#1713).
        let g = num_integer::gcd(a.unsigned_abs(), b.unsigned_abs());
        if g <= i128::MAX as u128 {
            Some(g as i128)
        } else {
            None
        }
    }

    /// Least common multiple (LCM). Returns None on overflow (#1713).
    pub(super) fn lcm(a: i128, b: i128) -> Option<i128> {
        if a == 0 || b == 0 {
            Some(0)
        } else {
            let gcd = Self::gcd(a, b)?;
            let quot = a.checked_abs()? / gcd;
            let b_abs = b.checked_abs()?;
            quot.checked_mul(b_abs)
        }
    }

    /// Normalize numerator/denominator, returning None on degenerate input (div by zero).
    /// Callers should check for None and handle gracefully (e.g., skip computation).
    pub(super) fn try_normalize(num: i128, den: i128) -> Option<(i128, i128)> {
        if den == 0 {
            // Degenerate case - return None instead of panicking (#1715)
            return None;
        }
        if num == 0 {
            return Some((0, 1));
        }
        let g = Self::gcd(num, den)?;
        let sign = if den < 0 { -1i128 } else { 1i128 };
        // Use checked arithmetic to detect overflow (#1602)
        let normalized_num = (num / g).checked_mul(sign)?;
        let normalized_den = (den / g).checked_abs()?;
        Some((normalized_num, normalized_den))
    }

    pub(super) fn normalize(num: i128, den: i128) -> (i128, i128) {
        // Gracefully handle zero denominator - return zero fallback (#1715).
        // This can occur with degenerate Farkas coefficients during interpolation.
        match Self::try_normalize(num, den) {
            Some(result) => result,
            None => {
                #[cfg(debug_assertions)]
                eprintln!("Rational::normalize overflow (num={num}, den={den}) — see #5339");
                (0, 1)
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn negate(&self) -> Self {
        // i128::MIN cannot be negated; degrade gracefully instead of panicking (#1713).
        match self.num.checked_neg() {
            Some(neg_num) => Self {
                num: neg_num,
                den: self.den,
            },
            None => Self::overflow_zero("negate(i128::MIN)"),
        }
    }
}

impl std::ops::Add for Rational {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        // Avoid panics on corrupted/degenerate rationals (#1713).
        if self.den == 0 || other.den == 0 {
            return Self::overflow_zero("add: zero denominator input");
        }

        let lcm = match Self::lcm(self.den, other.den) {
            Some(lcm) => lcm,
            None => return Self::overflow_zero("add: lcm overflow"),
        };

        let n1 = match self.num.checked_mul(lcm / self.den) {
            Some(n) => n,
            None => return Self::overflow_zero("add: n1 multiply overflow"),
        };
        let n2 = match other.num.checked_mul(lcm / other.den) {
            Some(n) => n,
            None => return Self::overflow_zero("add: n2 multiply overflow"),
        };
        let sum = match n1.checked_add(n2) {
            Some(s) => s,
            None => return Self::overflow_zero("add: sum overflow"),
        };

        let (num, den) = Self::normalize(sum, lcm);
        Self { num, den }
    }
}

impl std::ops::Sub for Rational {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        if self.den == 0 || other.den == 0 {
            return Self::overflow_zero("sub: zero denominator input");
        }
        let lcm = match Self::lcm(self.den, other.den) {
            Some(lcm) => lcm,
            None => return Self::overflow_zero("sub: lcm overflow"),
        };
        let n1 = match self.num.checked_mul(lcm / self.den) {
            Some(n) => n,
            None => return Self::overflow_zero("sub: n1 multiply overflow"),
        };
        let n2 = match other.num.checked_mul(lcm / other.den) {
            Some(n) => n,
            None => return Self::overflow_zero("sub: n2 multiply overflow"),
        };
        let diff = match n1.checked_sub(n2) {
            Some(d) => d,
            None => return Self::overflow_zero("sub: diff overflow"),
        };
        let (num, den) = Self::normalize(diff, lcm);
        Self { num, den }
    }
}

impl std::ops::Mul for Rational {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        // Avoid panicking on overflow; degrade gracefully (#1713).
        let num = match self.num.checked_mul(other.num) {
            Some(n) => n,
            None => return Self::overflow_zero("mul: numerator overflow"),
        };
        let den = match self.den.checked_mul(other.den) {
            Some(d) => d,
            None => return Self::overflow_zero("mul: denominator overflow"),
        };
        let (num, den) = Self::normalize(num, den);
        Self { num, den }
    }
}

impl std::ops::Div for Rational {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        // Gracefully handle division by zero - return zero fallback (#1715).
        // This can occur with degenerate Farkas coefficients during interpolation.
        if other.is_zero() {
            return Self::overflow_zero("div: division by zero");
        }
        // Use checked arithmetic to detect overflow (#1602)
        let num = match self.num.checked_mul(other.den) {
            Some(n) => n,
            None => return Self::overflow_zero("div: numerator overflow"),
        };
        let den = match self.den.checked_mul(other.num) {
            Some(d) => d,
            None => return Self::overflow_zero("div: denominator overflow"),
        };
        let (num, den) = Self::normalize(num, den);
        Self { num, den }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Avoid i128 overflow; fall back to BigInt compare if needed (#1713).
        match (
            self.num.checked_mul(other.den),
            other.num.checked_mul(self.den),
        ) {
            (Some(lhs), Some(rhs)) => lhs.cmp(&rhs),
            _ => {
                let lhs = BigInt::from(self.num) * BigInt::from(other.den);
                let rhs = BigInt::from(other.num) * BigInt::from(self.den);
                lhs.cmp(&rhs)
            }
        }
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}
