// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact arithmetic on real algebraic numbers, for confirming NRA models.
//!
//! # Why this exists
//!
//! [`ModelValue::Real`](crate::ModelValue::Real) holds a `BigRational`, so an
//! irrational witness cannot be represented at all — a model whose value is
//! `sqrt(2)` reaches the independent gate as an unpinned leaf and the verdict
//! fails closed. z3 publishes such witnesses as root objects
//! (`(root-obj (+ (^ x 2) (- 2)) 2)`), and confirming them needs arithmetic
//! that is EXACT.
//!
//! Floating point is not an option here. This crate is the independent checker
//! that guards every public `sat`; an approximate evaluator can confirm a
//! WRONG model, which is the one failure the whole subsystem exists to prevent.
//!
//! # Representation
//!
//! An [`Algebraic`] is `repr(α)`, where `α` is a real root of `minpoly`. Both
//! polynomials are dense, little-endian (`coeffs[i]` multiplies `x^i`), over
//! `BigRational`, and `repr` is always reduced to degree `< deg(minpoly)`.
//!
//! # Soundness of the arithmetic
//!
//! Reduction modulo `minpoly` is valid for EVERY root of `minpoly`, not just
//! the isolated one. So `add`, `mul`, `neg`, and [`Algebraic::as_rational`] are
//! sound knowing only that `α` is *some* root — the isolating interval is not
//! load-bearing for them. `(sqrt(2))^2 = 2` holds for both `+sqrt(2)` and
//! `-sqrt(2)`, which is exactly why an equality conclusion does not depend on
//! resolving which root was meant.
//!
//! ORDER comparisons are different: `α > 0` is true for one root of `x^2 - 2`
//! and false for the other, so they need the isolating interval and sign
//! refinement. Those are deliberately NOT implemented here yet, and no API in
//! this module lets a caller conclude an ordering. See the module TODO.
//!
//! Construction still validates the interval (`lo < hi` with a strict sign
//! change), so a stored root object is well-formed when ordering support
//! lands.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// A dense polynomial over `BigRational`, little-endian: `coeffs[i]` is the
/// coefficient of `x^i`. The zero polynomial is the empty vector.
type Poly = Vec<BigRational>;

/// Drop trailing zero coefficients so the degree is exact.
fn trim(mut p: Poly) -> Poly {
    while p.last().is_some_and(Zero::is_zero) {
        p.pop();
    }
    p
}

/// Degree, or `None` for the zero polynomial.
fn degree(p: &[BigRational]) -> Option<usize> {
    p.iter().rposition(|c| !c.is_zero())
}

fn poly_add(a: &[BigRational], b: &[BigRational]) -> Poly {
    let mut out = vec![BigRational::zero(); a.len().max(b.len())];
    for (i, c) in a.iter().enumerate() {
        out[i] += c;
    }
    for (i, c) in b.iter().enumerate() {
        out[i] += c;
    }
    trim(out)
}

fn poly_neg(a: &[BigRational]) -> Poly {
    trim(a.iter().map(|c| -c).collect())
}

fn poly_mul(a: &[BigRational], b: &[BigRational]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    trim(out)
}

/// Remainder of `a` modulo `m`, by long division. `m` must be non-zero.
///
/// Exact throughout: every coefficient operation is on `BigRational`, so no
/// rounding enters the reduction.
fn poly_rem(a: &[BigRational], m: &[BigRational]) -> Poly {
    let Some(m_deg) = degree(m) else {
        return Vec::new();
    };
    let mut r = trim(a.to_vec());
    let lead_inv = BigRational::one() / &m[m_deg];
    while let Some(r_deg) = degree(&r) {
        if r_deg < m_deg {
            break;
        }
        let shift = r_deg - m_deg;
        let factor = &r[r_deg] * &lead_inv;
        for (i, c) in m.iter().enumerate().take(m_deg + 1) {
            let idx = i + shift;
            let delta = &factor * c;
            r[idx] -= delta;
        }
        // The leading term cancels exactly; force it so the loop terminates
        // even if a rational subtraction leaves a representation artifact.
        r[r_deg] = BigRational::zero();
        r = trim(r);
    }
    r
}

/// Evaluate a polynomial at a rational point (Horner).
fn poly_eval(p: &[BigRational], at: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * at + c;
    }
    acc
}

/// Quotient and remainder of `a` divided by `m`, exact over `BigRational`.
fn poly_div_rem(a: &[BigRational], m: &[BigRational]) -> (Poly, Poly) {
    let Some(m_deg) = degree(m) else {
        return (Vec::new(), Vec::new());
    };
    let mut r = trim(a.to_vec());
    let lead_inv = BigRational::one() / &m[m_deg];
    let mut q = vec![BigRational::zero(); r.len().saturating_sub(m_deg).max(1)];
    while let Some(r_deg) = degree(&r) {
        if r_deg < m_deg {
            break;
        }
        let shift = r_deg - m_deg;
        let factor = &r[r_deg] * &lead_inv;
        if shift < q.len() {
            q[shift] = factor.clone();
        }
        for (i, c) in m.iter().enumerate().take(m_deg + 1) {
            r[i + shift] -= &factor * c;
        }
        r[r_deg] = BigRational::zero();
        r = trim(r);
    }
    (trim(q), r)
}

/// Formal derivative.
fn poly_derivative(p: &[BigRational]) -> Poly {
    if p.len() <= 1 {
        return Vec::new();
    }
    trim(
        p.iter()
            .enumerate()
            .skip(1)
            .map(|(i, c)| c * BigRational::from(BigInt::from(i as i64)))
            .collect(),
    )
}

/// Monic GCD by the Euclidean algorithm.
///
/// Load-bearing for equality: `α` is a root of `d` exactly when
/// `gcd(minpoly, d)` has a root in the isolating interval, which is how
/// [`Algebraic::is_zero_at_root`] decides whether two elements denote the same
/// value without assuming `minpoly` is minimal.
fn poly_gcd(a: &[BigRational], b: &[BigRational]) -> Poly {
    let mut x = trim(a.to_vec());
    let mut y = trim(b.to_vec());
    while degree(&y).is_some() {
        let (_, r) = poly_div_rem(&x, &y);
        x = y;
        y = r;
    }
    match degree(&x) {
        None => Vec::new(),
        Some(d) => {
            let inv = BigRational::one() / &x[d];
            trim(x.iter().map(|c| c * &inv).collect())
        }
    }
}

/// The Sturm chain of `p`: `p0 = p`, `p1 = p'`, `p_{i+1} = -rem(p_{i-1}, p_i)`.
///
/// No square-free reduction. The chain terminates at `gcd(p, p')`, and the
/// generalized theorem counts DISTINCT roots even when `p` has repeated
/// factors — `(x-1)^2 (x+1)` counts two, not three. A `p / gcd(p, p')` step was
/// written first and then removed: mutation testing showed no case where it
/// changed an answer, and unexercised code in the checker that guards every
/// public `sat` is a liability, not insurance.
fn sturm_chain(p: &[BigRational]) -> Vec<Poly> {
    let p = trim(p.to_vec());
    if degree(&p).is_none() {
        return Vec::new();
    }
    let mut chain = vec![p.clone(), poly_derivative(&p)];
    while degree(&chain[chain.len() - 1]).is_some() {
        let n = chain.len();
        let (_, r) = poly_div_rem(&chain[n - 2], &chain[n - 1]);
        if degree(&r).is_none() {
            break;
        }
        chain.push(poly_neg(&r));
    }
    chain
}

/// Sign variations of the chain evaluated at a point (zeros skipped).
fn sign_variations_at(chain: &[Poly], at: &BigRational) -> usize {
    let mut last = 0i8;
    let mut changes = 0usize;
    for poly in chain {
        let v = poly_eval(poly, at);
        let sign = if v.is_zero() {
            0
        } else if v.is_negative() {
            -1
        } else {
            1
        };
        if sign != 0 {
            if last != 0 && sign != last {
                changes += 1;
            }
            last = sign;
        }
    }
    changes
}

/// A bound `B` with every real root of `p` strictly inside `(-B, B)`
/// (Cauchy's bound).
fn root_bound(p: &[BigRational]) -> BigRational {
    let Some(d) = degree(p) else {
        return BigRational::one();
    };
    let lead = p[d].abs();
    let mut max_ratio = BigRational::zero();
    for c in p.iter().take(d) {
        let ratio = c.abs() / &lead;
        if ratio > max_ratio {
            max_ratio = ratio;
        }
    }
    max_ratio + BigRational::one() + BigRational::one()
}

/// Product of two rational intervals: the extremes of the four corner
/// products. Sound for any signs.
fn mul_interval(
    (a, b): (&BigRational, &BigRational),
    (c, d): (&BigRational, &BigRational),
) -> (BigRational, BigRational) {
    let corners = [a * c, a * d, b * c, b * d];
    let mut lo = corners[0].clone();
    let mut hi = corners[0].clone();
    for v in &corners[1..] {
        if *v < lo {
            lo = v.clone();
        }
        if *v > hi {
            hi = v.clone();
        }
    }
    (lo, hi)
}

/// A sound enclosure of `p([lo, hi])`, by Horner over intervals.
///
/// The result CONTAINS `p(x)` for every `x` in the interval; it is not tight.
/// That is all the sign test needs: an enclosure clear of zero settles the
/// sign, and one straddling zero just means refine further.
fn eval_interval(
    p: &[BigRational],
    lo: &BigRational,
    hi: &BigRational,
) -> (BigRational, BigRational) {
    let mut acc = (BigRational::zero(), BigRational::zero());
    for c in p.iter().rev() {
        let scaled = mul_interval((&acc.0, &acc.1), (lo, hi));
        acc = (scaled.0 + c, scaled.1 + c);
    }
    acc
}

/// How many bisections the sign test will spend before giving up.
///
/// Termination is guaranteed once the value is known non-zero — the enclosure
/// shrinks toward it — so the cap only bounds pathological work. Exhausting it
/// yields `None`, and every caller treats `None` as "cannot decide", so the
/// gate fails closed rather than guessing a sign.
const SIGN_REFINEMENT_STEPS: usize = 256;

/// Why a root object was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlgebraicError {
    /// `minpoly` is constant or zero, so it defines no algebraic number.
    DegenerateMinimalPolynomial,
    /// The isolating interval is empty or inverted.
    EmptyInterval,
    /// `minpoly` does not change sign across the interval, so the interval is
    /// not known to contain a root. Rejected rather than assumed.
    NoSignChange,
    /// Two values were combined over different minimal polynomials. Doing that
    /// correctly needs resultants; it is refused rather than approximated.
    DifferentExtension,
    /// The interval contains zero roots, or more than one. A root object whose
    /// interval does not ISOLATE a root does not name a value, so it is
    /// rejected rather than resolved arbitrarily.
    IntervalDoesNotIsolate {
        /// How many distinct real roots the interval actually contains.
        roots: usize,
    },
}

/// A real algebraic number: `repr(α)` for a root `α` of `minpoly` lying in the
/// open interval `(lo, hi)`.
#[derive(Debug, Clone)]
pub struct Algebraic {
    minpoly: Poly,
    lo: BigRational,
    hi: BigRational,
    repr: Poly,
}

impl Algebraic {
    /// The generator `α` itself: the root of `minpoly` isolated by `(lo, hi)`.
    ///
    /// Validates that the interval is non-empty and that `minpoly` strictly
    /// changes sign across it, which guarantees a root is present. Uniqueness
    /// within the interval is NOT checked here — nothing in this module draws
    /// a conclusion that depends on it (see the module docs).
    pub fn root_of(
        minpoly: Vec<BigRational>,
        lo: BigRational,
        hi: BigRational,
    ) -> Result<Self, AlgebraicError> {
        let minpoly = trim(minpoly);
        let Some(deg) = degree(&minpoly) else {
            return Err(AlgebraicError::DegenerateMinimalPolynomial);
        };
        if deg == 0 {
            return Err(AlgebraicError::DegenerateMinimalPolynomial);
        }
        if lo >= hi {
            return Err(AlgebraicError::EmptyInterval);
        }
        // EXACT isolation, via Sturm. A sign change alone only proves an ODD
        // number of roots; three roots in the interval would pass it and leave
        // the value ambiguous. Counting distinct roots over [lo, hi] and
        // demanding exactly one is what makes the object name a single value.
        let chain = sturm_chain(&minpoly);
        let roots = count_roots_in_closed(&chain, &minpoly, &lo, &hi);
        if roots != 1 {
            if roots == 0 {
                return Err(AlgebraicError::NoSignChange);
            }
            return Err(AlgebraicError::IntervalDoesNotIsolate { roots });
        }
        let repr = poly_rem(&[BigRational::zero(), BigRational::one()], &minpoly);
        Ok(Self {
            minpoly,
            lo,
            hi,
            repr,
        })
    }

    /// A rational, carried in the same extension as `self`.
    #[must_use]
    pub fn with_rational(&self, value: BigRational) -> Self {
        Self {
            minpoly: self.minpoly.clone(),
            lo: self.lo.clone(),
            hi: self.hi.clone(),
            repr: trim(vec![value]),
        }
    }

    /// The value as a rational, when it happens to be one.
    ///
    /// This is the equality workhorse: `(* x x)` over `x^2 - 2` reduces to the
    /// constant `2`, and the constraint `(= (* x x) 2.0)` is then confirmed by
    /// exact rational comparison.
    #[must_use]
    pub fn as_rational(&self) -> Option<BigRational> {
        match degree(&self.repr) {
            None => Some(BigRational::zero()),
            Some(0) => Some(self.repr[0].clone()),
            Some(_) => None,
        }
    }

    /// Whether two values live in the same extension and so may be combined.
    fn same_extension(&self, other: &Self) -> bool {
        self.minpoly == other.minpoly && self.lo == other.lo && self.hi == other.hi
    }

    /// Sum, within one extension.
    pub fn add(&self, other: &Self) -> Result<Self, AlgebraicError> {
        if !self.same_extension(other) {
            return Err(AlgebraicError::DifferentExtension);
        }
        Ok(Self {
            repr: poly_rem(&poly_add(&self.repr, &other.repr), &self.minpoly),
            ..self.clone()
        })
    }

    /// Negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self {
            repr: poly_neg(&self.repr),
            ..self.clone()
        }
    }

    /// Product, within one extension. The reduction modulo `minpoly` is what
    /// collapses `α^2` to `2` for `x^2 - 2`.
    pub fn mul(&self, other: &Self) -> Result<Self, AlgebraicError> {
        if !self.same_extension(other) {
            return Err(AlgebraicError::DifferentExtension);
        }
        Ok(Self {
            repr: poly_rem(&poly_mul(&self.repr, &other.repr), &self.minpoly),
            ..self.clone()
        })
    }

    /// Whether the element `poly(α)` is exactly zero.
    ///
    /// Equal representations obviously agree, but UNEQUAL ones need not
    /// differ: nothing here requires `minpoly` to be MINIMAL, and over
    /// `(x-1)(x-2)` with `α = 1` the elements `x` and `1` are the same value.
    /// So the test is semantic, not structural: `α` is a root of `poly`
    /// exactly when `gcd(minpoly, poly)` has a root in the isolating interval,
    /// and Sturm counts that exactly.
    ///
    /// Getting this wrong is not merely incomplete. A spurious "these differ"
    /// makes `(not (= a b))` evaluate TRUE, which lets the gate CONFIRM a
    /// model it should have rejected.
    fn is_zero_at_root(&self, poly: &[BigRational]) -> bool {
        match degree(poly) {
            None => true,
            Some(0) => poly[0].is_zero(),
            Some(_) => {
                let shared = poly_gcd(&self.minpoly, poly);
                degree(&shared).is_some_and(|d| d > 0)
                    && count_roots_in_closed(&sturm_chain(&shared), &shared, &self.lo, &self.hi)
                        >= 1
            }
        }
    }

    /// Exact equality with a rational.
    #[must_use]
    pub fn equals_rational(&self, value: &BigRational) -> bool {
        self.is_zero_at_root(&poly_add(&self.repr, &[-value.clone()]))
    }

    /// Equality within one extension, decided semantically (see
    /// [`Self::is_zero_at_root`]). Values in DIFFERENT extensions return
    /// `None` — deciding those needs resultants, and guessing would be
    /// unsound.
    #[must_use]
    pub fn equals(&self, other: &Self) -> Option<bool> {
        self.same_extension(other)
            .then(|| self.is_zero_at_root(&poly_add(&self.repr, &poly_neg(&other.repr))))
    }

    /// The defining polynomial, little-endian.
    #[must_use]
    pub fn minimal_polynomial(&self) -> &[BigRational] {
        &self.minpoly
    }

    /// Halve the isolating interval, keeping the half that still contains the
    /// root. Exact: the half is chosen by Sturm's count, not by a sign guess.
    fn bisect(&mut self) {
        let mid = (&self.lo + &self.hi) / BigRational::from(BigInt::from(2));
        let chain = sturm_chain(&self.minpoly);
        if count_roots_in_closed(&chain, &self.minpoly, &self.lo, &mid) == 1 {
            self.hi = mid;
        } else {
            self.lo = mid;
        }
    }

    /// The sign of this value: `-1`, `0`, or `1`; `None` when undecided.
    ///
    /// Zero is settled exactly by [`Self::is_zero_at_root`]. A non-zero value
    /// is settled by refining the isolating interval until the enclosure of
    /// `repr` over it is clear of zero. `None` means the refinement budget ran
    /// out — callers must treat that as "cannot decide", never as a sign.
    #[must_use]
    pub fn sign(&self) -> Option<i8> {
        if self.is_zero_at_root(&self.repr) {
            return Some(0);
        }
        let mut window = self.clone();
        for _ in 0..SIGN_REFINEMENT_STEPS {
            let (lo, hi) = eval_interval(&window.repr, &window.lo, &window.hi);
            if lo.is_positive() {
                return Some(1);
            }
            if hi.is_negative() {
                return Some(-1);
            }
            window.bisect();
        }
        None
    }

    /// Compare against a rational. `None` when undecided.
    #[must_use]
    pub fn compare_to_rational(&self, value: &BigRational) -> Option<core::cmp::Ordering> {
        use core::cmp::Ordering;
        let difference = Self {
            repr: poly_add(&self.repr, &[-value.clone()]),
            ..self.clone()
        };
        difference.sign().map(|s| match s {
            0 => Ordering::Equal,
            n if n < 0 => Ordering::Less,
            _ => Ordering::Greater,
        })
    }

    /// The value's representation as a polynomial in the generator,
    /// little-endian and reduced below `deg(minpoly)`. Two values in one
    /// extension are equal exactly when these agree, so this is the basis of a
    /// canonical rendering.
    #[must_use]
    pub fn representation(&self) -> &[BigRational] {
        &self.repr
    }

    /// The isolating interval `(lo, hi)`.
    #[must_use]
    pub fn interval(&self) -> (&BigRational, &BigRational) {
        (&self.lo, &self.hi)
    }
}

/// Distinct real roots of `p` in the CLOSED interval `[lo, hi]`.
///
/// Sturm counts over the half-open `(lo, hi]`, so a root sitting exactly on
/// `lo` is added back explicitly.
fn count_roots_in_closed(
    chain: &[Poly],
    p: &[BigRational],
    lo: &BigRational,
    hi: &BigRational,
) -> usize {
    if chain.is_empty() {
        return 0;
    }
    let half_open = sign_variations_at(chain, lo).saturating_sub(sign_variations_at(chain, hi));
    half_open + usize::from(poly_eval(p, lo).is_zero())
}

impl Algebraic {
    /// Distinct real roots of the minimal polynomial in `[lo, hi]`.
    #[must_use]
    pub fn count_roots_in(&self, lo: &BigRational, hi: &BigRational) -> usize {
        count_roots_in_closed(&sturm_chain(&self.minpoly), &self.minpoly, lo, hi)
    }

    /// The 1-based index of this root among the minimal polynomial's real
    /// roots in increasing order — the `k` in z3's `(root-obj p k)`.
    ///
    /// `sqrt(2)` is root 2 of `x^2 - 2`, matching what z3 publishes.
    #[must_use]
    pub fn root_index(&self) -> usize {
        let chain = sturm_chain(&self.minpoly);
        if chain.is_empty() {
            return 1;
        }
        let bound = root_bound(&self.minpoly);
        let below = count_roots_in_closed(&chain, &self.minpoly, &-bound, &self.lo);
        // The interval isolates this root, so every root at or below `lo` is
        // strictly smaller than it — unless the root IS `lo`, in which case
        // that count already includes this one.
        if poly_eval(&self.minpoly, &self.lo).is_zero() {
            below.max(1)
        } else {
            below + 1
        }
    }
}

/// Convenience: build a polynomial from integer coefficients, little-endian.
#[must_use]
pub fn integer_poly(coeffs: &[i64]) -> Vec<BigRational> {
    coeffs
        .iter()
        .map(|c| BigRational::from(BigInt::from(*c)))
        .collect()
}

// Ordering landed: see `Algebraic::sign` and `compare_to_rational`. Both are
// exact — zero by `is_zero_at_root`, non-zero by refining the isolating
// interval until a sound enclosure clears zero — and both return `None` rather
// than guess when the refinement budget runs out.

#[cfg(test)]
#[path = "algebraic_tests.rs"]
mod tests;
