// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Count value semirings.
//!
//! The counting engine is generic over the value domain: natural numbers for
//! unweighted counting (`mc`/`pmc`), exact rationals for weighted counting
//! (`wmc`/`pwmc`, including zero and negative weights), and complex rationals
//! for algebraic counting (`amc-complex`). All arithmetic is exact and
//! arbitrary-precision; there is no floating point anywhere in a count.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Zero};

/// A commutative-semiring value the counting engine can accumulate.
///
/// `add` combines the two branches of a decision; `mul` combines independent
/// subcomponents and literal weights. Both must be exact.
pub trait CountValue: Clone + PartialEq + Send + 'static {
    /// Additive identity (the count of an unsatisfiable residual).
    fn zero() -> Self;
    /// Multiplicative identity (the count of an empty residual).
    fn one() -> Self;
    /// Exact zero test (used only for the sound short-circuit `0 * x = 0`).
    fn is_zero(&self) -> bool;
    /// `self += other`.
    fn add_assign(&mut self, other: &Self);
    /// `self *= other`.
    fn mul_assign(&mut self, other: &Self);
    /// Approximate heap footprint in bytes, for cache accounting.
    fn approx_bytes(&self) -> usize;
}

impl CountValue for BigUint {
    fn zero() -> Self {
        <BigUint as Zero>::zero()
    }
    fn one() -> Self {
        <BigUint as One>::one()
    }
    fn is_zero(&self) -> bool {
        <BigUint as Zero>::is_zero(self)
    }
    fn add_assign(&mut self, other: &Self) {
        *self += other;
    }
    fn mul_assign(&mut self, other: &Self) {
        *self *= other;
    }
    fn approx_bytes(&self) -> usize {
        // 32-bit digits internally; count whole words.
        self.to_u32_digits().len() * 4 + 24
    }
}

impl CountValue for BigRational {
    fn zero() -> Self {
        <BigRational as Zero>::zero()
    }
    fn one() -> Self {
        <BigRational as One>::one()
    }
    fn is_zero(&self) -> bool {
        <BigRational as Zero>::is_zero(self)
    }
    fn add_assign(&mut self, other: &Self) {
        *self += other;
    }
    fn mul_assign(&mut self, other: &Self) {
        *self *= other;
    }
    fn approx_bytes(&self) -> usize {
        bigint_bytes(self.numer()) + bigint_bytes(self.denom()) + 16
    }
}

fn bigint_bytes(x: &BigInt) -> usize {
    x.magnitude().to_u32_digits().len() * 4 + 24
}

/// A complex number with exact rational real and imaginary parts.
///
/// This is the value domain of the algebraic model counting track
/// (`amc-complex`). Field arithmetic is exact; only the final log10 estimate
/// lines are rendered in floating point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComplexRat {
    /// Real part.
    pub re: BigRational,
    /// Imaginary part.
    pub im: BigRational,
}

impl ComplexRat {
    /// Construct from real and imaginary parts.
    pub fn new(re: BigRational, im: BigRational) -> Self {
        Self { re, im }
    }

    /// Construct a purely real value.
    pub fn from_real(re: BigRational) -> Self {
        Self {
            re,
            im: <BigRational as Zero>::zero(),
        }
    }
}

impl CountValue for ComplexRat {
    fn zero() -> Self {
        Self {
            re: <BigRational as Zero>::zero(),
            im: <BigRational as Zero>::zero(),
        }
    }
    fn one() -> Self {
        Self {
            re: <BigRational as One>::one(),
            im: <BigRational as Zero>::zero(),
        }
    }
    fn is_zero(&self) -> bool {
        <BigRational as Zero>::is_zero(&self.re) && <BigRational as Zero>::is_zero(&self.im)
    }
    fn add_assign(&mut self, other: &Self) {
        self.re += &other.re;
        self.im += &other.im;
    }
    fn mul_assign(&mut self, other: &Self) {
        // (a+bi)(c+di) = (ac - bd) + (ad + bc)i
        let ac = &self.re * &other.re;
        let bd = &self.im * &other.im;
        let ad = &self.re * &other.im;
        let bc = &self.im * &other.re;
        self.re = ac - bd;
        self.im = ad + bc;
    }
    fn approx_bytes(&self) -> usize {
        CountValue::approx_bytes(&self.re) + CountValue::approx_bytes(&self.im)
    }
}

impl CountValue for BigInt {
    fn zero() -> Self {
        <BigInt as Zero>::zero()
    }
    fn one() -> Self {
        <BigInt as One>::one()
    }
    fn is_zero(&self) -> bool {
        <BigInt as Zero>::is_zero(self)
    }
    fn add_assign(&mut self, other: &Self) {
        *self += other;
    }
    fn mul_assign(&mut self, other: &Self) {
        *self *= other;
    }
    fn approx_bytes(&self) -> usize {
        bigint_bytes(self)
    }
}

/// A Gaussian integer (complex number with integer parts) — the scaled value
/// domain for algebraic counting: weights are pre-scaled to integer parts
/// over one global denominator, so counting needs no per-operation
/// normalization (no gcd), and the single division happens at the end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GaussInt {
    /// Real part.
    pub re: BigInt,
    /// Imaginary part.
    pub im: BigInt,
}

impl GaussInt {
    /// Construct from parts.
    pub fn new(re: BigInt, im: BigInt) -> Self {
        Self { re, im }
    }
}

impl CountValue for GaussInt {
    fn zero() -> Self {
        Self {
            re: <BigInt as Zero>::zero(),
            im: <BigInt as Zero>::zero(),
        }
    }
    fn one() -> Self {
        Self {
            re: <BigInt as One>::one(),
            im: <BigInt as Zero>::zero(),
        }
    }
    fn is_zero(&self) -> bool {
        <BigInt as Zero>::is_zero(&self.re) && <BigInt as Zero>::is_zero(&self.im)
    }
    fn add_assign(&mut self, other: &Self) {
        self.re += &other.re;
        self.im += &other.im;
    }
    fn mul_assign(&mut self, other: &Self) {
        // (a+bi)(c+di) = (ac - bd) + (ad + bc)i
        let ac = &self.re * &other.re;
        let bd = &self.im * &other.im;
        let ad = &self.re * &other.im;
        let bc = &self.im * &other.re;
        self.re = ac - bd;
        self.im = ad + bc;
    }
    fn approx_bytes(&self) -> usize {
        bigint_bytes(&self.re) + bigint_bytes(&self.im)
    }
}

/// Literal weight table used by the engine.
///
/// `None` means "every literal has weight 1" (pure unweighted counting); the
/// engine then never multiplies per-literal weights and uses a free-variable
/// factor of 2. When present, the table is indexed by literal code
/// (`var * 2 + negated`) and the free-variable factor for `v` is
/// `w(v) + w(-v)`.
#[derive(Clone)]
pub struct WeightTable<W> {
    /// Per-literal weights, indexed by literal code; `None` = all ones.
    lit_weight: Option<Vec<W>>,
    /// Cached per-variable free factors `w(v) + w(-v)`; parallel to vars.
    free_factor: Option<Vec<W>>,
    two: W,
}

impl<W: CountValue> WeightTable<W> {
    /// Unweighted table (all literal weights are 1, free factor 2).
    pub fn unweighted() -> Self {
        let mut two = W::one();
        two.add_assign(&W::one());
        Self {
            lit_weight: None,
            free_factor: None,
            two,
        }
    }

    /// Weighted table from per-literal weights (`weights.len() == 2 * num_vars`,
    /// indexed by literal code `var * 2 + negated`).
    pub fn weighted(weights: Vec<W>) -> Self {
        assert!(
            weights.len().is_multiple_of(2),
            "weight table must cover both polarities"
        );
        let mut two = W::one();
        two.add_assign(&W::one());
        let free: Vec<W> = (0..weights.len() / 2)
            .map(|v| {
                let mut f = weights[v * 2].clone();
                f.add_assign(&weights[v * 2 + 1]);
                f
            })
            .collect();
        Self {
            lit_weight: Some(weights),
            free_factor: Some(free),
            two,
        }
    }

    /// Weight of a literal by code, or `None` when all weights are 1.
    #[inline]
    pub fn lit_weight(&self, lit_code: usize) -> Option<&W> {
        self.lit_weight.as_ref().map(|t| &t[lit_code])
    }

    /// Free-variable factor `w(v) + w(-v)` (2 in the unweighted case).
    #[inline]
    pub fn free_factor(&self, var: usize) -> &W {
        match &self.free_factor {
            Some(t) => &t[var],
            None => &self.two,
        }
    }

    /// True when a weight table is present (weighted semantics).
    pub fn is_weighted(&self) -> bool {
        self.lit_weight.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn biguint_semiring_basics() {
        let mut x = <BigUint as CountValue>::one();
        x.add_assign(&CountValue::one());
        let mut y = x.clone();
        y.mul_assign(&x);
        assert_eq!(y, BigUint::from(4u32));
        assert!(CountValue::is_zero(&<BigUint as CountValue>::zero()));
    }

    #[test]
    fn complex_mul_matches_field_rules() {
        let i = ComplexRat::new(<BigRational as Zero>::zero(), <BigRational as One>::one());
        let mut x = i.clone();
        x.mul_assign(&i);
        // i^2 = -1
        assert_eq!(x.re, -<BigRational as One>::one());
        assert!(<BigRational as Zero>::is_zero(&x.im));
    }

    #[test]
    fn unweighted_free_factor_is_two() {
        let t: WeightTable<BigUint> = WeightTable::unweighted();
        assert_eq!(*t.free_factor(3), BigUint::from(2u32));
        assert!(t.lit_weight(6).is_none());
    }
}
