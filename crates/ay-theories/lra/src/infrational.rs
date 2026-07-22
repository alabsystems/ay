// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Infinitesimal-extended rational numbers for strict bound handling.
//!
//! Implements the `x + y*ε` representation from Dutertre & de Moura (CAV 2006).
//! Strict inequality `v > c` becomes non-strict `v >= (c, +1)`, eliminating
//! simplex cycling from degenerate strict bounds.
//!
//! Uses `Rational` (i64/i64 fast path) internally instead of `BigRational`
//! to avoid heap allocation in the common case.

use crate::rational::{gcd_u64, Rational};
use crate::types::BoundType;
use num_rational::BigRational;
use num_traits::Zero;
use std::cmp::Ordering;

/// Multiply two rationals given as (n1/d1) * (n2/d2) using pure i128 arithmetic.
/// Returns `Some(Rational::Small(rn, rd))` if the result fits in i64, `None` otherwise.
///
/// Pre-reduces cross-GCD to minimize overflow risk. Same algorithm as
/// `try_mul_small` in rational_ops.rs but inlined for the InfRational hot path
/// to avoid function-call overhead (#8406).
#[inline]
fn mul_rational_i64(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    let g1 = gcd_u64(n1.unsigned_abs(), d2.unsigned_abs());
    let g2 = gcd_u64(n2.unsigned_abs(), d1.unsigned_abs());
    let n1r = n1 / g1 as i64;
    let d2r = d2 / g1 as i64;
    let n2r = n2 / g2 as i64;
    let d1r = d1 / g2 as i64;
    if let (Some(num), Some(den)) = (n1r.checked_mul(n2r), d1r.checked_mul(d2r)) {
        let (num, den) = if den < 0 {
            match (num.checked_neg(), den.checked_neg()) {
                (Some(n), Some(d)) => (n, d),
                _ => return None,
            }
        } else {
            (num, den)
        };
        if num == 0 {
            return Some(Rational::Small(0, 1));
        }
        let g = gcd_u64(num.unsigned_abs(), den.unsigned_abs());
        return Some(Rational::Small(num / g as i64, den / g as i64));
    }
    let num128 = i128::from(n1r) * i128::from(n2r);
    let den128 = i128::from(d1r) * i128::from(d2r);
    if den128 == 0 {
        return None;
    }
    let (num128, den128) = if den128 < 0 {
        (-num128, -den128)
    } else {
        (num128, den128)
    };
    if num128 == 0 {
        return Some(Rational::Small(0, 1));
    }
    let g = gcd_u128(num128.unsigned_abs(), den128.unsigned_abs());
    let rn = num128 / g as i128;
    let rd = den128 / g as i128;
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

/// Binary GCD for u128 (no allocation, no division).
#[inline]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
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

/// Infinitesimal-extended rational: x + y*ε
///
/// Ordered lexicographically: `(x1, y1) < (x2, y2)` iff `x1 < x2` or
/// `(x1 == x2 && y1 < y2)`. This captures the semantics of ε being
/// infinitesimally small but positive.
#[derive(Clone, Default)]
pub(crate) struct InfRational {
    x: Rational,
    y: Rational,
}

impl InfRational {
    /// Backward-compatible constructor from BigRational values.
    pub(crate) fn new(x: BigRational, y: BigRational) -> Self {
        Self {
            x: Rational::from(x),
            y: Rational::from(y),
        }
    }
    /// Backward-compatible: construct from BigRational (epsilon = 0).
    pub(crate) fn from_rational(x: BigRational) -> Self {
        Self {
            x: Rational::from(x),
            y: Rational::zero(),
        }
    }
    /// Construct from Rational without BigRational allocation.
    #[inline]
    pub(crate) fn from_rat(x: Rational) -> Self {
        Self {
            x,
            y: Rational::zero(),
        }
    }
    /// Construct from Rational with epsilon component.
    #[inline]
    pub(crate) fn new_rat(x: Rational, y: Rational) -> Self {
        Self { x, y }
    }
    /// Backward-compatible: get rational part as BigRational (allocates).
    pub(crate) fn rational(&self) -> BigRational {
        self.x.to_big()
    }
    /// Get the rational part as a `Rational` (no BigRational allocation) (#8064).
    #[inline]
    pub(crate) fn x_rational(&self) -> Rational {
        self.x.clone()
    }
    /// Return both finite and infinitesimal parts as inline i64 rationals.
    ///
    /// This is a no-allocation guard for prospective JIT lowering: callers
    /// must fail closed when either side has already escaped to the bignum
    /// representation.
    #[inline]
    pub(crate) fn try_as_i64_parts(&self) -> Option<((i64, i64), (i64, i64))> {
        match (&self.x, &self.y) {
            (Rational::Small(xn, xd), Rational::Small(yn, yd)) => Some(((*xn, *xd), (*yn, *yd))),
            _ => None,
        }
    }
    /// Backward-compatible: get epsilon as BigRational (allocates).
    pub(crate) fn epsilon(&self) -> BigRational {
        self.y.to_big()
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y.is_zero()
    }
    /// True when the infinitesimal component is zero, i.e. `materialize(δ)`
    /// returns the rational part unchanged for EVERY δ. Callers use this to
    /// skip the O(#vars) `compute_materialization_delta` scan entirely
    /// (#certora-materialization-delta). No allocation (cf. `epsilon()`).
    #[inline]
    pub(crate) fn epsilon_is_zero(&self) -> bool {
        self.y.is_zero()
    }
    pub(crate) fn is_integer(&self) -> bool {
        self.y.is_zero() && self.x.is_integer()
    }
    /// Multiply by a Rational coefficient (hot-path version).
    #[inline]
    pub(crate) fn mul_rat(&self, c: &Rational) -> Self {
        // Fast path: when epsilon component is zero (common for non-strict bounds),
        // skip the second multiply entirely.
        if self.y.is_zero() {
            Self {
                x: &self.x * c,
                y: Rational::zero(),
            }
        } else {
            Self {
                x: &self.x * c,
                y: &self.y * c,
            }
        }
    }
    /// Multiply by a coefficient given as raw (numerator, denominator) i64 pair.
    ///
    /// Bypasses Rational enum matching entirely -- pure i128 arithmetic when the
    /// InfRational's components are also Small. Falls back to `mul_rat` on overflow.
    ///
    /// Hot path: called by `update_nonbasic` when the coefficient is `Small(n, d)`,
    /// which is the case for 100% of QF_LRA benchmarks (#8406).
    #[inline]
    pub(crate) fn mul_rat_i64(&self, cn: i64, cd: i64) -> Self {
        if let Rational::Small(xn, xd) = &self.x {
            if self.y.is_zero() {
                if let Some(x_new) = mul_rational_i64(*xn, *xd, cn, cd) {
                    return Self {
                        x: x_new,
                        y: Rational::zero(),
                    };
                }
            } else if let Rational::Small(yn, yd) = &self.y {
                if let Some(x_new) = mul_rational_i64(*xn, *xd, cn, cd) {
                    if let Some(y_new) = mul_rational_i64(*yn, *yd, cn, cd) {
                        return Self { x: x_new, y: y_new };
                    }
                }
            }
        }
        self.mul_rat(&Rational::Small(cn, cd))
    }

    /// Fused add-assign of `delta * (cn/cd)` where (cn, cd) is a raw i64 rational.
    ///
    /// Equivalent to `*self += &delta.mul_rat_i64(cn, cd)` but skips the
    /// intermediate InfRational allocation when the multiply produces a Small
    /// result. The addition uses Rational's existing optimized `try_add_small` path.
    ///
    /// Hot path: called per-row in `update_nonbasic` (#8406).
    #[inline]
    pub(crate) fn add_assign_mul_i64(&mut self, delta: &Self, cn: i64, cd: i64) {
        if let Rational::Small(dx_n, dx_d) = &delta.x {
            if let Some(product) = mul_rational_i64(*dx_n, *dx_d, cn, cd) {
                self.x += &product;
                if !delta.y.is_zero() {
                    if let Rational::Small(dy_n, dy_d) = &delta.y {
                        if let Some(y_product) = mul_rational_i64(*dy_n, *dy_d, cn, cd) {
                            self.y += &y_product;
                            return;
                        }
                    }
                    self.y += &(&delta.y * &Rational::Small(cn, cd));
                }
                return;
            }
        }
        let adj = delta.mul_rat(&Rational::Small(cn, cd));
        *self += &adj;
    }

    /// Backward-compatible: multiply by BigRational coefficient.
    #[allow(dead_code)]
    pub(crate) fn mul_rational(&self, c: &BigRational) -> Self {
        let c_rat = Rational::from(c.clone());
        self.mul_rat(&c_rat)
    }
    /// Materialize to concrete Rational: `x + y*δ`
    pub(crate) fn materialize_rat(&self, delta: &Rational) -> Rational {
        if self.y.is_zero() {
            self.x.clone()
        } else {
            &self.x + &(&self.y * delta)
        }
    }
    /// Backward-compatible: materialize to BigRational.
    pub(crate) fn materialize(&self, delta: &BigRational) -> BigRational {
        let delta_rat = Rational::from(delta.clone());
        self.materialize_rat(&delta_rat).to_big()
    }

    /// Compare `self` against a bound without allocating an `InfRational`.
    ///
    /// A bound `(value, strict, bound_type)` maps to the InfRational:
    /// - Lower strict:  `(value, +1ε)`
    /// - Upper strict:  `(value, -1ε)`
    /// - Non-strict:    `(value,  0ε)`
    ///
    /// This avoids the heap allocation in `Bound::as_inf()` which clones
    /// `BigRational`. Hot path: called per-variable in `violates_bounds`.
    #[inline]
    pub(crate) fn cmp_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> Ordering {
        // First compare the rational parts
        let x_ord = self.x.cmp(bound_value);
        if x_ord != Ordering::Equal {
            return x_ord;
        }
        // Rational parts are equal; compare epsilon parts.
        // Bound epsilon is: strict lower → +1, strict upper → -1, non-strict → 0
        if !strict {
            // Bound epsilon = 0, so compare self.y vs 0
            if self.y.is_positive() {
                Ordering::Greater
            } else if self.y.is_negative() {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        } else {
            // Strict bound: epsilon is +1 (lower) or -1 (upper).
            // These are Small(1,1) and Small(-1,1) — always the fast i128 path.
            match bound_type {
                BoundType::Lower => self.y.cmp(&Rational::Small(1, 1)),
                BoundType::Upper => self.y.cmp(&Rational::Small(-1, 1)),
            }
        }
    }

    /// Check if `self < bound` without allocating.
    #[inline]
    pub(crate) fn lt_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> bool {
        self.cmp_bound(bound_value, strict, bound_type) == Ordering::Less
    }

    /// Check if `self > bound` without allocating.
    #[inline]
    pub(crate) fn gt_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> bool {
        self.cmp_bound(bound_value, strict, bound_type) == Ordering::Greater
    }

    /// Approximate the rational (x) component as f64, no allocation for Small.
    /// Used for heuristic violation magnitudes in heap key computation.
    #[inline]
    pub(crate) fn x_approx_f64(&self) -> f64 {
        self.x.approx_f64()
    }
}

impl std::fmt::Debug for InfRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.y.is_zero() {
            write!(f, "{}", self.x)
        } else if self.x.is_zero() {
            write!(f, "{}*e", self.y)
        } else {
            write!(f, "{} + {}*e", self.x, self.y)
        }
    }
}

impl std::fmt::Display for InfRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl PartialEq for InfRational {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for InfRational {}

impl PartialOrd for InfRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for InfRational {
    fn cmp(&self, other: &Self) -> Ordering {
        self.x.cmp(&other.x).then_with(|| self.y.cmp(&other.y))
    }
}

impl std::ops::Add for &InfRational {
    type Output = InfRational;
    #[inline]
    fn add(self, rhs: Self) -> InfRational {
        let y = if self.y.is_zero() && rhs.y.is_zero() {
            Rational::zero()
        } else {
            &self.y + &rhs.y
        };
        InfRational {
            x: &self.x + &rhs.x,
            y,
        }
    }
}

impl std::ops::Sub for &InfRational {
    type Output = InfRational;
    #[inline]
    fn sub(self, rhs: Self) -> InfRational {
        let y = if self.y.is_zero() && rhs.y.is_zero() {
            Rational::zero()
        } else {
            &self.y - &rhs.y
        };
        InfRational {
            x: &self.x - &rhs.x,
            y,
        }
    }
}

impl std::ops::Neg for InfRational {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
        }
    }
}

impl std::ops::AddAssign<&Self> for InfRational {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        self.x += &rhs.x;
        // Skip epsilon add when RHS has no epsilon component (common case:
        // non-strict bounds produce zero epsilon in mul_rat results).
        if !rhs.y.is_zero() {
            self.y += &rhs.y;
        }
    }
}

impl std::ops::SubAssign<&Self> for InfRational {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        self.x -= &rhs.x;
        if !rhs.y.is_zero() {
            self.y -= &rhs.y;
        }
    }
}

impl std::ops::AddAssign<BigRational> for InfRational {
    fn add_assign(&mut self, rhs: BigRational) {
        self.x += &Rational::from(rhs);
    }
}
