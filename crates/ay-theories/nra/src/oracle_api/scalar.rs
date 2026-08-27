// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A real root as AY reports it: an exact rational, or an open isolating
/// interval with non-root rational endpoints containing exactly one root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ORoot {
    /// Exact rational root.
    Rational(BigRational),
    /// Open isolating interval `(lo, hi)` containing exactly one real root.
    Interval(BigRational, BigRational),
}

/// Dense univariate polynomial over the rationals, low-to-high coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OPoly(UniPoly);

impl OPoly {
    /// Build from low-to-high rational coefficients (trailing zeros trimmed).
    #[must_use]
    pub fn from_coeffs(coeffs: Vec<BigRational>) -> Self {
        Self(UniPoly::from_coeffs(coeffs))
    }

    /// Low-to-high rational coefficients (empty for the zero polynomial).
    #[must_use]
    pub fn coeffs(&self) -> Vec<BigRational> {
        self.0.coeffs().to_vec()
    }

    /// Degree, or `None` for the zero polynomial.
    #[must_use]
    pub fn degree(&self) -> Option<usize> {
        self.0.degree()
    }

    /// Is this the zero polynomial?
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// Exact evaluation at a rational point.
    #[must_use]
    pub fn eval(&self, x: &BigRational) -> BigRational {
        self.0.eval(x)
    }

    /// Formal derivative.
    #[must_use]
    pub fn derivative(&self) -> Self {
        Self(self.0.derivative())
    }

    /// Product.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        Self(self.0.mul(&other.0))
    }

    /// Remainder `self mod other` (`other` must be non-zero).
    #[must_use]
    pub fn rem(&self, other: &Self) -> Self {
        Self(self.0.rem(&other.0))
    }

    /// Scale by a rational.
    #[must_use]
    pub fn scale(&self, s: &BigRational) -> Self {
        Self(self.0.scale(s))
    }

    /// `p / gcd(p, p')` — the square-free part.
    #[must_use]
    pub fn square_free_part(&self) -> Option<Self> {
        square_free_part(&self.0).map(Self)
    }

    /// Monic Euclidean GCD over the rationals.
    #[must_use]
    pub fn gcd(&self, other: &Self) -> Self {
        Self(poly_gcd(&self.0, &other.0))
    }

    /// Isolate the real roots of a SQUARE-FREE polynomial into ordered,
    /// mutually disjoint markers. `None` when AY declines (budget / fail-closed).
    #[must_use]
    pub fn isolate_roots(&self) -> Option<Vec<ORoot>> {
        isolate_roots(&self.0).map(|ms| {
            ms.into_iter()
                .map(|m| match m {
                    RootMarker::Rational(r) => ORoot::Rational(r),
                    RootMarker::Interval(lo, hi) => ORoot::Interval(lo, hi),
                })
                .collect()
        })
    }

    /// Number of distinct real roots in the half-open interval `(a, b]`,
    /// by Sturm's theorem on this polynomial's own Sturm sequence.
    #[must_use]
    pub fn sturm_count_in(&self, a: &BigRational, b: &BigRational) -> usize {
        let seq = sturm_sequence(&self.0);
        sturm_count(&seq, a, b)
    }
}

/// Resultant of two univariate polynomials at their nominal degrees, via the
/// exact Sylvester determinant AY uses today.
#[must_use]
pub fn resultant(f: &OPoly, g: &OPoly) -> Option<BigRational> {
    sylvester_det_fixed(f.0.coeffs(), g.0.coeffs())
}

/// Sign of a rational: -1, 0 or +1.
#[must_use]
pub fn sign_of(r: &BigRational) -> i32 {
    rational_sign(r)
}

/// A real algebraic number: the k-th real root of a square-free integer
/// polynomial, pinned by an isolating interval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OAlg(RealAlgebraic);

impl OAlg {
    /// Build from a defining polynomial and an open isolating interval.
    /// `None` unless the interval isolates exactly one real root.
    #[must_use]
    pub fn new(p: &OPoly, lo: &BigRational, hi: &BigRational) -> Option<Self> {
        RealAlgebraic::from_isolating_interval(&p.0, lo, hi).map(Self)
    }

    /// Exact sign of `q` at this algebraic number.
    #[must_use]
    pub fn sign_of_poly(&self, q: &OPoly) -> Option<i32> {
        self.0.sign_of_poly(&q.0)
    }

    /// 1-based index among the ascending real roots of the defining polynomial.
    #[must_use]
    pub fn root_index(&self) -> usize {
        self.0.root_index()
    }

    /// Exact comparison against a rational.
    #[must_use]
    pub fn cmp_rational(&self, r: &BigRational) -> Option<Ordering> {
        self.0.cmp_rational(r)
    }

    /// Exact comparison against another algebraic number.
    #[must_use]
    pub fn cmp_number(&self, other: &Self) -> Option<Ordering> {
        self.0.cmp_number(&other.0)
    }

    /// Exact sum with another algebraic number, as a [`OScalar`].
    #[must_use]
    pub fn add(&self, other: &Self) -> Option<OScalar> {
        RealScalar::Algebraic(self.0.as_value())
            .add(&RealScalar::Algebraic(other.0.as_value()))
            .map(OScalar)
    }

    /// Exact product with another algebraic number, as a [`OScalar`].
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<OScalar> {
        RealScalar::Algebraic(self.0.as_value())
            .mul(&RealScalar::Algebraic(other.0.as_value()))
            .map(OScalar)
    }

    /// This number as an exact scalar.
    #[must_use]
    pub fn to_scalar(&self) -> OScalar {
        OScalar(RealScalar::Algebraic(self.0.as_value()))
    }
}

/// An exact real scalar (rational or real algebraic).
#[derive(Clone, Debug)]
pub struct OScalar(RealScalar);

impl OScalar {
    /// Exact comparison against a rational; `None` when AY declines.
    #[must_use]
    pub fn cmp_rational(&self, r: &BigRational) -> Option<Ordering> {
        self.0.cmp_exact(&RealScalar::Rational(r.clone()))
    }
}
