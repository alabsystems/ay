// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fast rational arithmetic with inline i64/i64 representation.
//!
//! Almost every LRA simplex coefficient fits in a machine word, so this module
//! provides `Rational`: an inline `(i64, i64)` for small values with a
//! pure-Rust arbitrary-precision fallback ([`num_rational::BigRational`]) for
//! the rare overflow case. Benchmarks show QF_LRA problems have coefficients
//! like 1, 2, 3, 15, 30 -- all fit in i64, and the inline i64/i128 fast path
//! handles ~100% of operations (the `Big` overflow path is essentially never
//! reached on the CHC/SMT corpus).
//!
//! AY is pure Rust and links no external C libraries: the historical GMP
//! (`rug`/`gmp-mpfr-sys`) overflow backend was removed (#chc25-drop-gmp) after
//! profiling showed it was never exercised. `num_rational::BigRational` is the
//! sole arbitrary-precision backend and is exact.
//!
//! Reference: Z3 `src/util/mpq.h`, OpenSMT2 `src/common/FastRational.h`.

mod utility;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// Backing type for the arbitrary-precision overflow fallback of [`Rational`].
///
/// The small/inline `(i64, i64)` fast path handles the overwhelming majority of
/// operations; this pure-Rust [`num_rational::BigRational`] is the exact
/// overflow backend for the `Big` variant. (Alias retained for readability and
/// so the `to_rug`/`from_rug` interop helper names stay stable.)
pub(crate) type BigBacking = BigRational;

/// A rational number optimized for small values.
///
/// Most LRA simplex coefficients fit in 64-bit integers. This type avoids
/// heap allocation for the common case while preserving exact arithmetic
/// via fallback to an arbitrary-precision [`BigBacking`] rational for overflow.
///
/// The `Big` variant is the pure-Rust `num_rational::BigRational`; results are
/// exact. AY uses pure-Rust arbitrary precision (no external C library).
#[derive(Clone)]
pub enum Rational {
    /// Inline representation: numerator / denominator.
    /// Invariants: denom > 0, gcd(|numer|, denom) == 1, denom != 0.
    /// Zero is represented as Small(0, 1).
    Small(i64, i64),
    /// Heap-allocated arbitrary-precision fallback ([`BigBacking`]).
    Big(Box<BigBacking>),
}

/// Binary GCD for u64 (no allocation, no division).
#[inline]
pub(crate) fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// Normalize a (numer, denom) pair: positive denom, reduced by GCD.
/// Returns None if overflow would occur during normalization.
#[inline]
pub(crate) fn normalize_small(mut n: i64, mut d: i64) -> Option<(i64, i64)> {
    if d == 0 {
        return None;
    }
    if n == 0 {
        return Some((0, 1));
    }
    if d < 0 {
        n = n.checked_neg()?;
        d = d.checked_neg()?;
    }
    let g = gcd_u64(n.unsigned_abs(), d.unsigned_abs());
    if g > 1 {
        Some((n / g as i64, d / g as i64))
    } else {
        Some((n, d))
    }
}

/// Try to shrink a [`BigBacking`] rational back to Small.
pub(crate) fn try_shrink(br: &BigBacking) -> Option<Rational> {
    // num_rational::BigRational is always normalized to a positive denominator,
    // so the sign-fixup branch can never fire; it is kept defensively in case
    // that invariant ever changes.
    let n: i64 = br.numer().try_into().ok()?;
    let d: i64 = br.denom().try_into().ok()?;
    if d > 0 {
        Some(Rational::Small(n, d))
    } else if d < 0 {
        Some(Rational::Small(n.checked_neg()?, d.checked_neg()?))
    } else {
        None
    }
}

/// Try to shrink a num_rational::BigRational back to Small.
fn try_shrink_num(br: &BigRational) -> Option<Rational> {
    let n: i64 = br.numer().try_into().ok()?;
    let d: i64 = br.denom().try_into().ok()?;
    if d > 0 {
        Some(Rational::Small(n, d))
    } else if d < 0 {
        Some(Rational::Small(n.checked_neg()?, d.checked_neg()?))
    } else {
        None
    }
}

// --- Construction -----------------------------------------------------------

impl Rational {
    /// Create from numerator and denominator. Panics if denom == 0.
    #[inline]
    pub fn new(numer: i64, denom: i64) -> Self {
        assert!(denom != 0, "Rational: zero denominator");
        match normalize_small(numer, denom) {
            Some((n, d)) => Self::Small(n, d),
            None => Self::from_big(BigRational::new(BigInt::from(numer), BigInt::from(denom))),
        }
    }

    /// Wrap a [`BigBacking`] rational, shrinking to Small if possible.
    ///
    /// `from_rug` is the historical interop name; it wraps a pure-Rust
    /// [`num_rational::BigRational`] ([`BigBacking`]).
    #[inline]
    pub fn from_rug(gr: BigBacking) -> Self {
        try_shrink(&gr).unwrap_or_else(|| Self::Big(Box::new(gr)))
    }

    /// Wrap a num_rational::BigRational, shrinking to Small if possible.
    /// The pure-Rust backend stores `BigRational` directly (no conversion).
    #[inline]
    pub fn from_big(br: BigRational) -> Self {
        try_shrink_num(&br).unwrap_or_else(|| Self::Big(Box::new(br)))
    }

    /// Convert to the pure-Rust [`BigBacking`] rational (always succeeds).
    ///
    /// `to_rug` is the historical interop name; it returns a
    /// `num_rational::BigRational`.
    #[inline]
    pub fn to_rug(&self) -> BigBacking {
        match self {
            Self::Small(n, d) => BigRational::new(BigInt::from(*n), BigInt::from(*d)),
            Self::Big(br) => (**br).clone(),
        }
    }

    /// Convert to num_rational::BigRational (backward compatibility).
    /// For the Big variant, converts from the active backend when needed.
    #[inline]
    pub fn to_big(&self) -> BigRational {
        match self {
            Self::Small(n, d) => BigRational::new(BigInt::from(*n), BigInt::from(*d)),
            Self::Big(br) => (**br).clone(),
        }
    }

    /// Compare `self` against a `BigRational` without allocating.
    ///
    /// For `Small(n, d)` vs `p/q`: compares `n*q` vs `p*d` using mixed-precision
    /// integer multiplication (BigInt x i64 -> BigInt), which avoids the full
    /// `to_big()` allocation path.
    ///
    /// Hot path: called per-atom in `bound_is_interesting` (#6615).
    #[inline]
    pub fn cmp_big(&self, other: &BigRational) -> Ordering {
        match self {
            Self::Small(n, d) => {
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    let lhs = i128::from(*n) * i128::from(q);
                    let rhs = i128::from(p) * i128::from(*d);
                    return lhs.cmp(&rhs);
                }
                let lhs = other.denom() * *n;
                let rhs = other.numer() * *d;
                lhs.cmp(&rhs)
            }
            Self::Big(br) => (**br).cmp(other),
        }
    }

    /// Multiply a `&BigRational` by this `Rational`, returning a `BigRational`.
    #[inline]
    pub fn mul_bigrational(&self, other: &BigRational) -> BigRational {
        match self {
            Self::Small(n, d) => {
                let numer = BigInt::from(*n) * other.numer();
                let denom = BigInt::from(*d) * other.denom();
                BigRational::new(numer, denom)
            }
            Self::Big(br) => (**br).clone() * other,
        }
    }

    /// Multiply this `Rational` by a `&BigRational`, returning `Rational`.
    #[inline]
    pub fn mul_bigrational_to_rat(&self, other: &BigRational) -> Self {
        match self {
            Self::Small(n, d) => {
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    let g1 = gcd_u64(n.unsigned_abs(), q.unsigned_abs());
                    let g2 = gcd_u64(p.unsigned_abs(), d.unsigned_abs());
                    let nr = *n / g1 as i64;
                    let qr = q / g1 as i64;
                    let pr = p / g2 as i64;
                    let dr = *d / g2 as i64;
                    if let (Some(num), Some(den)) = (nr.checked_mul(pr), dr.checked_mul(qr)) {
                        if let Some((rn, rd)) = normalize_small(num, den) {
                            return Self::Small(rn, rd);
                        }
                    }
                }
                Self::from_big(self.mul_bigrational(other))
            }
            Self::Big(br) => Self::from_big((**br).clone() * other),
        }
    }

    /// Compute the absolute value of this `Rational`, returning a `BigRational`.
    #[inline]
    pub fn abs_bigrational(&self) -> BigRational {
        match self {
            Self::Small(n, d) => BigRational::new(BigInt::from(n.unsigned_abs()), BigInt::from(*d)),
            Self::Big(br) => num_traits::Signed::abs(&**br),
        }
    }

    /// Borrow as BigRational (allocates -- use sparingly).
    #[inline]
    pub fn as_big(&self) -> std::borrow::Cow<'_, BigRational> {
        std::borrow::Cow::Owned(self.to_big())
    }

    /// Check if this is the inline representation.
    #[inline]
    pub fn is_small(&self) -> bool {
        matches!(self, Self::Small(_, _))
    }

    /// Extract numerator as BigInt.
    pub fn numer_big(&self) -> BigInt {
        match self {
            Self::Small(n, _) => BigInt::from(*n),
            Self::Big(br) => br.numer().clone(),
        }
    }

    /// Alias for `numer_big()`.
    #[inline]
    pub fn numer(&self) -> BigInt {
        self.numer_big()
    }

    /// Extract denominator as BigInt.
    pub fn denom_big(&self) -> BigInt {
        match self {
            Self::Small(_, d) => BigInt::from(*d),
            Self::Big(br) => br.denom().clone(),
        }
    }

    /// Alias for `denom_big()`.
    #[inline]
    pub fn denom(&self) -> BigInt {
        self.denom_big()
    }

    /// Create from integer value (alias for `From<BigInt>`).
    #[inline]
    pub fn from_integer(n: BigInt) -> Self {
        Self::from(n)
    }

    /// Create from BigInt numerator and denominator.
    pub fn new_big(numer: BigInt, denom: BigInt) -> Self {
        Self::from_big(BigRational::new(numer, denom))
    }

    /// Convert to BigInt by truncation (floor for non-negative, ceil for negative).
    pub fn to_integer(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => BigInt::from(*n / *d),
            Self::Big(br) => br.to_integer(),
        }
    }
}

// --- Standard trait impls ---------------------------------------------------

impl Default for Rational {
    #[inline]
    fn default() -> Self {
        Self::Small(0, 1)
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Small(n, 1) => write!(f, "{n}"),
            Self::Small(n, d) => write!(f, "{n}/{d}"),
            Self::Big(br) => write!(f, "Big({br})"),
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Small(n, 1) => write!(f, "{n}"),
            Self::Small(n, d) => write!(f, "{n}/{d}"),
            Self::Big(br) => write!(f, "{br}"),
        }
    }
}

impl PartialEq for Rational {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Small(n1, d1), Self::Small(n2, d2)) => n1 == n2 && d1 == d2,
            _ => self.to_rug() == other.to_rug(),
        }
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Small(n1, d1), Self::Small(n2, d2)) => {
                let lhs = i128::from(*n1) * i128::from(*d2);
                let rhs = i128::from(*n2) * i128::from(*d1);
                lhs.cmp(&rhs)
            }
            _ => self.to_rug().cmp(&other.to_rug()),
        }
    }
}

impl Hash for Rational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Small(n, d) => {
                0u8.hash(state);
                n.hash(state);
                d.hash(state);
            }
            Self::Big(br) => {
                if let Some(Self::Small(n, d)) = try_shrink(br) {
                    0u8.hash(state);
                    n.hash(state);
                    d.hash(state);
                } else {
                    1u8.hash(state);
                    let n_str = br.numer().to_string();
                    let d_str = br.denom().to_string();
                    n_str.hash(state);
                    d_str.hash(state);
                }
            }
        }
    }
}

// --- Zero / One -------------------------------------------------------------

impl Zero for Rational {
    #[inline]
    fn zero() -> Self {
        Self::Small(0, 1)
    }
    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            Self::Small(0, _) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => Zero::is_zero(&**br),
        }
    }
}

impl One for Rational {
    #[inline]
    fn one() -> Self {
        Self::Small(1, 1)
    }
    #[inline]
    fn is_one(&self) -> bool {
        match self {
            Self::Small(1, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => One::is_one(&**br),
        }
    }
}

impl Rational {
    /// Returns true when this rational is exactly `-1`.
    #[inline]
    pub fn is_neg_one(&self) -> bool {
        match self {
            Self::Small(-1, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => {
                num_traits::ToPrimitive::to_i64(br.numer()) == Some(-1)
                    && num_traits::ToPrimitive::to_i64(br.denom()) == Some(1)
            }
        }
    }
}

/// Clone-based `From` for `&Rational` -> `Rational`.
impl From<&Self> for Rational {
    #[inline]
    fn from(r: &Self) -> Self {
        r.clone()
    }
}

// BigRational interop traits (PartialEq, PartialOrd, mul_big_to_rational)
// are in rational_ops.rs to keep this file under 500 lines.
