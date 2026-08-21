// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact real algebraic numbers for NRA model witnesses (z3 `root-obj` parity).
//!
//! The exact univariate decision procedure (`univariate.rs`) can prove SAT for
//! constraints whose only solutions are irrational (e.g. `x*x = 2`). This
//! module gives those witnesses a first-class, exactly-computable
//! representation so the executor can carry them in the model, print them in
//! z3's `(root-obj <poly> <k>)` syntax, evaluate polynomial expressions over
//! them (`(* x x) -> 2`), and let full model validation confirm the model.
//!
//! Representation: [`RealAlgebraic`] is the `k`-th real root (1-based,
//! ascending) of a square-free integer polynomial, together with an open
//! isolating interval with rational, non-root endpoints. All arithmetic is
//! exact (`BigRational`/`BigInt` only — never floats):
//!
//!   * signs of arbitrary polynomials at the root via Sturm sequences plus
//!     interval refinement (`sign_of_poly_at_root`),
//!   * values of polynomial expressions via residue reduction modulo the
//!     defining polynomial ([`RealAlgebraicValue`]) — a constant residue is an
//!     exact rational value,
//!   * derived algebraic numbers (e.g. the value of `x^2` at `x = 5^(1/4)`)
//!     via the resultant `Res_x(q(x), y - r(x))`, computed exactly with
//!     Sylvester determinants and Lagrange interpolation,
//!   * exact comparisons, integrality tests and floors via interval
//!     refinement, with every "equal" answer confirmed by a polynomial
//!     GCD/sign certificate (never by numeric proximity).
//!
//! Every public operation is total-or-`None`: refinement loops carry hard
//! iteration caps as a defense-in-depth guard, and a capped-out computation
//! returns `None` so callers fail closed (model evaluation returns Unknown)
//! rather than fabricate a value.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::univariate::{
    cauchy_bound, isolate_roots, poly_gcd, rational_sign, square_free_part, sturm_count,
    sturm_sequence, RootMarker, UniPoly,
};
mod rational_root;
/// Hard cap on interval-refinement bisection steps. Each step halves the
/// isolating interval, so 4096 steps shrink it by 2^4096 — unreachable for any
/// genuine computation on these polynomial degrees; hitting the cap means a
/// logic bug and the operation fails closed (`None`).
const MAX_REFINE_STEPS: usize = 4096;

/// A real algebraic number: the `root_index`-th real root (1-based, in
/// ascending order) of the square-free integer polynomial `poly`, isolated by
/// the open interval `(lo, hi)` whose endpoints are not roots of `poly`.
///
/// This is exactly the information in z3's `(root-obj <poly> <k>)` model
/// values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealAlgebraic {
    /// Defining polynomial: square-free, integer coefficients with content 1,
    /// positive leading coefficient. Low-to-high coefficient order inside
    /// `UniPoly`.
    poly: UniPoly,
    /// 1-based index among the ascending real roots of `poly`.
    root_index: usize,
    /// Open isolating interval: contains exactly one root of `poly` (this
    /// number), and neither endpoint is a root.
    lo: BigRational,
    hi: BigRational,
}

/// Result of interval refinement: either a strictly smaller isolating
/// interval, or the exact (rational) root when a bisection midpoint hits it.
pub(crate) enum Refined {
    /// A strictly narrower isolating interval, endpoints still non-roots.
    Interval(BigRational, BigRational),
    /// The bisection landed exactly on the root, which is therefore rational.
    Exact(BigRational),
}

/// An exact real scalar: either a rational or a real algebraic value.
#[derive(Clone, Debug)]
pub enum RealScalar {
    /// An exact rational value.
    Rational(BigRational),
    /// An exact real algebraic (irrational-capable) value.
    Algebraic(RealAlgebraicValue),
}

impl RealScalar {
    /// Exact addition. Same-point algebraic operands add by residue
    /// arithmetic; different-point operands through the exact sum resultant
    /// ([`RealAlgebraicValue::cross_add`]). `None` only on a refinement cap
    /// (fail closed).
    pub fn add(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some(Self::Rational(a + b)),
            (Self::Rational(r), Self::Algebraic(a)) | (Self::Algebraic(a), Self::Rational(r)) => {
                Some(Self::Algebraic(a.add_rational(r)))
            }
            (Self::Algebraic(a), Self::Algebraic(b)) => a.try_add(b).or_else(|| a.cross_add(b)),
        }
    }

    /// Exact negation.
    pub fn neg(&self) -> Self {
        match self {
            Self::Rational(r) => Self::Rational(-r),
            Self::Algebraic(a) => Self::Algebraic(a.neg()),
        }
    }

    /// Exact multiplication. Same-point algebraic operands multiply by
    /// residue arithmetic; different-point operands through the exact product
    /// resultant ([`RealAlgebraicValue::cross_mul`]). `None` only on a
    /// refinement cap (fail closed).
    pub fn mul(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some(Self::Rational(a * b)),
            (Self::Rational(r), Self::Algebraic(a)) | (Self::Algebraic(a), Self::Rational(r)) => {
                Some(a.mul_rational(r))
            }
            (Self::Algebraic(a), Self::Algebraic(b)) => a.try_mul(b).or_else(|| a.cross_mul(b)),
        }
    }

    /// Exact reciprocal `1/self`. `None` when the value is exactly zero or on
    /// a refinement cap (fail closed) — never an approximation.
    pub fn recip(&self) -> Option<Self> {
        match self {
            Self::Rational(r) => {
                if r.is_zero() {
                    None
                } else {
                    Some(Self::Rational(r.recip()))
                }
            }
            Self::Algebraic(a) => a.recip(),
        }
    }

    /// Exact comparison (total on rationals and same-point algebraics; across
    /// points it goes through derived defining polynomials — still exact).
    pub fn cmp_exact(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some(a.cmp(b)),
            (Self::Rational(r), Self::Algebraic(a)) => {
                a.cmp_rational(r).map(std::cmp::Ordering::reverse)
            }
            (Self::Algebraic(a), Self::Rational(r)) => a.cmp_rational(r),
            (Self::Algebraic(a), Self::Algebraic(b)) => a.try_cmp(b),
        }
    }
}

impl RealAlgebraic {
    /// Construct from a polynomial and an open isolating interval.
    ///
    /// `p` need not be square-free or integer-normalized (both are computed
    /// here). Returns `None` unless the interval isolates EXACTLY one real
    /// root of `p` and neither endpoint is a root — the fail-closed contract
    /// callers rely on.
    pub(crate) fn from_isolating_interval(
        p: &UniPoly,
        lo: &BigRational,
        hi: &BigRational,
    ) -> Option<Self> {
        if lo >= hi {
            return None;
        }
        let sf = square_free_part(p)?;
        if sf.degree().unwrap_or(0) < 1 {
            return None;
        }
        let poly = integer_normalize(&sf)?;
        if poly.eval(lo).is_zero() || poly.eval(hi).is_zero() {
            return None;
        }
        let seq = sturm_sequence(&poly);
        if sturm_count(&seq, lo, hi) != 1 {
            return None;
        }
        // Index: number of roots at or below `lo`, plus one. All real roots
        // lie strictly within the Cauchy bound.
        let below = -(cauchy_bound(&poly)) - BigRational::one();
        let root_index = sturm_count(&seq, &below, lo) + 1;
        Some(Self {
            poly,
            root_index,
            lo: lo.clone(),
            hi: hi.clone(),
        })
    }

    /// The defining polynomial's integer coefficients, low-to-high degree.
    pub fn poly_coeffs(&self) -> Vec<BigInt> {
        self.poly
            .coeffs()
            .iter()
            .map(|c| c.numer().clone())
            .collect()
    }

    /// 1-based index among the ascending real roots of the defining polynomial.
    pub fn root_index(&self) -> usize {
        self.root_index
    }

    /// The current isolating interval (open, non-root rational endpoints).
    pub fn interval(&self) -> (&BigRational, &BigRational) {
        (&self.lo, &self.hi)
    }

    /// The value of the variable itself as a [`RealAlgebraicValue`].
    pub fn as_value(&self) -> RealAlgebraicValue {
        RealAlgebraicValue {
            alpha: self.clone(),
            residue: UniPoly::x(),
        }
    }

    /// One bisection step on an isolating interval of `poly`. The interval
    /// brackets a sign change (square-free polynomial, exactly one root, non-
    /// root endpoints), so one half keeps the sign change. If the midpoint is
    /// itself the root (only possible for a rational root, which can occur for
    /// intervals derived from enclosures), report it exactly.
    fn refine_step(poly: &UniPoly, lo: &BigRational, hi: &BigRational) -> Option<Refined> {
        let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
        let s_mid = rational_sign(&poly.eval(&mid));
        if s_mid == 0 {
            return Some(Refined::Exact(mid));
        }
        let s_lo = rational_sign(&poly.eval(lo));
        let s_hi = rational_sign(&poly.eval(hi));
        if s_lo == 0 || s_hi == 0 || s_lo == s_hi {
            // Invariant violation (endpoints must be non-roots with opposite
            // signs around a single simple root). Fail closed.
            return None;
        }
        if s_lo != s_mid {
            Some(Refined::Interval(lo.clone(), mid))
        } else {
            Some(Refined::Interval(mid, hi.clone()))
        }
    }

    /// One bisection of an enclosure of THIS number, against its own defining
    /// polynomial.
    ///
    /// `(lo, hi)` must isolate this number (the constructor's interval, or any
    /// interval derived from it by this method). Exposed for
    /// [`crate::mroot`], whose interval fast path narrows several algebraic
    /// coordinates in lockstep and therefore has to drive refinement itself
    /// rather than call a fixed-cap helper. `None` is the same fail-closed
    /// refusal [`Self::refine_step`] makes on a violated invariant.
    pub(crate) fn refine_from(&self, lo: &BigRational, hi: &BigRational) -> Option<Refined> {
        Self::refine_step(&self.poly, lo, hi)
    }

    /// Exact sign of an arbitrary polynomial `p` at this algebraic number.
    ///
    ///   * `0` is certified algebraically: `gcd(defining, square_free(p))`
    ///     has a root in the isolating interval (which can only be this
    ///     number).
    ///   * Otherwise the interval is refined until it contains no root of
    ///     `p`, making `p` sign-constant on it; the sign at the midpoint is
    ///     the exact answer.
    pub(crate) fn sign_of_poly(&self, p: &UniPoly) -> Option<i32> {
        if p.is_zero() {
            return Some(0);
        }
        let psf = square_free_part(p)?;
        if psf.degree().unwrap_or(0) < 1 {
            // `p` has no real roots: sign-constant everywhere.
            let mid = (&self.lo + &self.hi) / BigRational::from_integer(BigInt::from(2));
            return Some(rational_sign(&p.eval(&mid)));
        }
        // Zero test: does p vanish at this root?
        let g = poly_gcd(&self.poly, &psf);
        if g.degree().unwrap_or(0) >= 1 {
            let gseq = sturm_sequence(&g);
            // Endpoints are non-roots of `poly`, hence of `g` (g | poly).
            if sturm_count(&gseq, &self.lo, &self.hi) >= 1 {
                return Some(0);
            }
        }
        // p does not vanish here: refine until (lo, hi) is p-root-free.
        let pseq = sturm_sequence(&psf);
        let mut lo = self.lo.clone();
        let mut hi = self.hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let lo_is_root = psf.eval(&lo).is_zero();
            let hi_is_root = psf.eval(&hi).is_zero();
            if !lo_is_root && !hi_is_root && sturm_count(&pseq, &lo, &hi) == 0 {
                let mid = (&lo + &hi) / BigRational::from_integer(BigInt::from(2));
                return Some(rational_sign(&p.eval(&mid)));
            }
            match Self::refine_step(&self.poly, &lo, &hi)? {
                Refined::Interval(l, h) => {
                    lo = l;
                    hi = h;
                }
                Refined::Exact(r) => return Some(rational_sign(&p.eval(&r))),
            }
        }
        None
    }

    /// Exact comparison against a rational.
    pub fn cmp_rational(&self, r: &BigRational) -> Option<std::cmp::Ordering> {
        // sign of (x - r) at the root.
        let p = UniPoly::x().sub(&UniPoly::constant(r.clone()));
        self.sign_of_poly(&p).map(|s| s.cmp(&0))
    }

    /// Exact comparison between two algebraic numbers (possibly with
    /// different defining polynomials). Equality is certified by a GCD root
    /// count — never by numeric proximity; inequality by interval separation.
    pub fn cmp_number(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        if self == other {
            return Some(Ordering::Equal);
        }
        let mut a = (self.lo.clone(), self.hi.clone());
        let mut b = (other.lo.clone(), other.hi.clone());
        // Common-root certificate: g = gcd(p1, p2). The two numbers are equal
        // iff g has a root in the intersection of the isolating intervals
        // (that root is then the unique root of p1 in I1 AND of p2 in I2).
        let g = poly_gcd(&self.poly, &other.poly);
        let g_data = if g.degree().unwrap_or(0) >= 1 {
            Some((sturm_sequence(&g), g.clone()))
        } else {
            None
        };
        for _ in 0..MAX_REFINE_STEPS {
            if a.1 <= b.0 {
                return Some(Ordering::Less);
            }
            if b.1 <= a.0 {
                return Some(Ordering::Greater);
            }
            if let Some((gseq, gp)) = &g_data {
                let ilo = if a.0 > b.0 { a.0.clone() } else { b.0.clone() };
                let ihi = if a.1 < b.1 { a.1.clone() } else { b.1.clone() };
                if ilo < ihi
                    && !gp.eval(&ilo).is_zero()
                    && !gp.eval(&ihi).is_zero()
                    && sturm_count(gseq, &ilo, &ihi) >= 1
                {
                    return Some(Ordering::Equal);
                }
            }
            // Not yet separated and no common-root certificate: refine both.
            match Self::refine_step(&self.poly, &a.0, &a.1)? {
                Refined::Interval(l, h) => a = (l, h),
                Refined::Exact(r) => {
                    return match other.cmp_rational(&r)? {
                        Ordering::Less => Some(Ordering::Greater),
                        Ordering::Equal => Some(Ordering::Equal),
                        Ordering::Greater => Some(Ordering::Less),
                    }
                }
            }
            match Self::refine_step(&other.poly, &b.0, &b.1)? {
                Refined::Interval(l, h) => b = (l, h),
                Refined::Exact(r) => return self.cmp_rational(&r),
            }
        }
        None
    }

    /// Exact reciprocal `1/this` of the algebraic point itself.
    ///
    /// The interval is refined until it excludes 0; the reciprocal is then
    /// the unique root of the REVERSED defining polynomial (`y^d * p(1/y)`,
    /// whose roots are exactly the reciprocals of `p`'s nonzero roots) in
    /// `(1/hi, 1/lo)`. `None` when the value is exactly zero or on a
    /// refinement cap (fail closed).
    fn recip_number(&self) -> Option<RealScalar> {
        let mut lo = self.lo.clone();
        let mut hi = self.hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            if rational_sign(&lo) != 0 && rational_sign(&lo) == rational_sign(&hi) {
                // Interval excludes 0: t -> 1/t is a monotone bijection on the
                // same-sign region, so (1/hi, 1/lo) isolates the reciprocal
                // (verified again, fail-closed, by from_isolating_interval).
                let rev: Vec<BigRational> = self.poly.coeffs().iter().rev().cloned().collect();
                let revp = UniPoly::from_coeffs(rev);
                let ilo = hi.recip();
                let ihi = lo.recip();
                let alg = RealAlgebraic::from_isolating_interval(&revp, &ilo, &ihi)?;
                return Some(RealScalar::Algebraic(alg.as_value()));
            }
            match Self::refine_step(&self.poly, &lo, &hi)? {
                Refined::Interval(l, h) => {
                    lo = l;
                    hi = h;
                }
                Refined::Exact(r) => {
                    return if r.is_zero() {
                        None
                    } else {
                        Some(RealScalar::Rational(r.recip()))
                    };
                }
            }
        }
        None
    }

    /// Render in z3 4.15 `root-obj` syntax, e.g. `(root-obj (+ (^ x 2) (- 2)) 2)`
    /// for `sqrt(2)`. The bound variable is always the literal `x` (matching
    /// z3, regardless of the model variable's declared name); coefficients are
    /// integers, terms in descending degree, negative constants as `(- c)`.
    pub fn to_smtlib(&self) -> String {
        let coeffs = self.poly_coeffs();
        let deg = coeffs.len().saturating_sub(1);
        let mut terms: Vec<String> = Vec::new();
        for k in (0..=deg).rev() {
            let c = &coeffs[k];
            if c.is_zero() {
                continue;
            }
            let cstr = if c.is_negative() {
                format!("(- {})", -c)
            } else {
                c.to_string()
            };
            let term = match k {
                0 => cstr,
                1 => {
                    if c.is_one() {
                        "x".to_string()
                    } else {
                        format!("(* {cstr} x)")
                    }
                }
                _ => {
                    if c.is_one() {
                        format!("(^ x {k})")
                    } else {
                        format!("(* {cstr} (^ x {k}))")
                    }
                }
            };
            terms.push(term);
        }
        let poly_str = if terms.len() == 1 {
            terms.pop().expect("non-empty")
        } else {
            format!("(+ {})", terms.join(" "))
        };
        format!("(root-obj {} {})", poly_str, self.root_index)
    }
}

/// The exact value of a polynomial expression at a [`RealAlgebraic`] point:
/// `residue(alpha)`, where `residue` is reduced modulo the defining
/// polynomial (so a constant residue never reaches this type — it collapses
/// to a plain rational via [`RealAlgebraicValue::reduce`]).
#[derive(Clone, Debug)]
pub struct RealAlgebraicValue {
    alpha: RealAlgebraic,
    /// Non-constant residue with degree < deg(alpha.poly).
    residue: UniPoly,
}

impl RealAlgebraicValue {
    /// Reduce `poly(alpha)` to an exact scalar: a rational when the residue
    /// modulo the defining polynomial is constant, else an algebraic value.
    pub(crate) fn reduce(alpha: &RealAlgebraic, poly: &UniPoly) -> RealScalar {
        let residue = poly.rem(&alpha.poly);
        match residue.degree() {
            None => RealScalar::Rational(BigRational::zero()),
            Some(0) => RealScalar::Rational(residue.coeffs()[0].clone()),
            Some(_) => RealScalar::Algebraic(Self {
                alpha: alpha.clone(),
                residue,
            }),
        }
    }

    /// The underlying algebraic point.
    pub fn alpha(&self) -> &RealAlgebraic {
        &self.alpha
    }

    /// True when this value IS the algebraic point itself (identity residue).
    pub fn is_identity(&self) -> bool {
        self.residue == UniPoly::x()
    }

    /// value + r (exact; stays non-constant, so stays algebraic).
    pub fn add_rational(&self, r: &BigRational) -> Self {
        Self {
            alpha: self.alpha.clone(),
            residue: self.residue.add(&UniPoly::constant(r.clone())),
        }
    }

    /// value * r (exact). Zero collapses to the rational 0.
    pub fn mul_rational(&self, r: &BigRational) -> RealScalar {
        if r.is_zero() {
            return RealScalar::Rational(BigRational::zero());
        }
        RealScalar::Algebraic(Self {
            alpha: self.alpha.clone(),
            residue: self.residue.scale(r),
        })
    }

    /// -value (exact).
    pub fn neg(&self) -> Self {
        Self {
            alpha: self.alpha.clone(),
            residue: self.residue.neg(),
        }
    }

    /// value + other, when both are expressions over the SAME algebraic point
    /// (structurally identical defining data). `None` otherwise.
    pub fn try_add(&self, other: &Self) -> Option<RealScalar> {
        if self.alpha != other.alpha {
            return None;
        }
        Some(Self::reduce(&self.alpha, &self.residue.add(&other.residue)))
    }

    /// value * other, same-point requirement as [`Self::try_add`].
    pub fn try_mul(&self, other: &Self) -> Option<RealScalar> {
        if self.alpha != other.alpha {
            return None;
        }
        Some(Self::reduce(&self.alpha, &self.residue.mul(&other.residue)))
    }

    /// Exact sign of the value (-1, 0, +1). A 0 can only be produced by the
    /// algebraic GCD certificate in [`RealAlgebraic::sign_of_poly`].
    pub fn sign(&self) -> Option<i32> {
        self.alpha.sign_of_poly(&self.residue)
    }

    /// Exact comparison against a rational.
    pub fn cmp_rational(&self, r: &BigRational) -> Option<std::cmp::Ordering> {
        let diff = self.residue.sub(&UniPoly::constant(r.clone()));
        self.alpha.sign_of_poly(&diff).map(|s| s.cmp(&0))
    }

    /// Exact comparison against another algebraic value. Same-point values
    /// compare via an exact polynomial sign; different points via their
    /// derived defining polynomials ([`Self::to_number`]).
    pub fn try_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.alpha == other.alpha {
            let diff = self.residue.sub(&other.residue);
            return self.alpha.sign_of_poly(&diff).map(|s| s.cmp(&0));
        }
        let a = self.to_number()?;
        let b = other.to_number()?;
        match (a, b) {
            (RealScalar::Rational(x), RealScalar::Rational(y)) => Some(x.cmp(&y)),
            (RealScalar::Rational(x), RealScalar::Algebraic(y)) => {
                y.alpha.cmp_rational(&x).map(std::cmp::Ordering::reverse)
            }
            (RealScalar::Algebraic(x), RealScalar::Rational(y)) => x.alpha.cmp_rational(&y),
            (RealScalar::Algebraic(x), RealScalar::Algebraic(y)) => x.alpha.cmp_number(&y.alpha),
        }
    }

    /// Exact integrality test.
    pub fn is_integer(&self) -> Option<bool> {
        match self.floor_boundary()? {
            FloorResult::Exact(_) => Some(true),
            FloorResult::Strict(_) => Some(false),
        }
    }

    /// Exact floor of the value.
    pub fn floor(&self) -> Option<BigInt> {
        Some(match self.floor_boundary()? {
            FloorResult::Exact(n) | FloorResult::Strict(n) => n,
        })
    }

    /// Compute the floor with exactness information: `Exact(n)` when the
    /// value IS the integer `n`, `Strict(n)` when `n < value < n+1`.
    fn floor_boundary(&self) -> Option<FloorResult> {
        let mut lo = self.alpha.lo.clone();
        let mut hi = self.alpha.hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let (elo, ehi) = interval_eval(&self.residue, &lo, &hi);
            let f_lo = elo.floor().to_integer();
            let f_hi = ehi.floor().to_integer();
            if f_lo == f_hi && !ehi.is_integer() {
                // Whole enclosure inside [n, n+1). Decide n vs (n, n+1):
                // value == n iff sign(residue - n) == 0.
                let n = f_lo;
                let diff = self
                    .residue
                    .sub(&UniPoly::constant(BigRational::from_integer(n.clone())));
                return match self.alpha.sign_of_poly(&diff)? {
                    0 => Some(FloorResult::Exact(n)),
                    _ => Some(FloorResult::Strict(n)),
                };
            }
            // Enclosure spans an integer boundary `m`: test equality with the
            // candidate boundary before refining further, so exact-integer
            // values terminate immediately.
            let m = f_hi.clone();
            let diff = self
                .residue
                .sub(&UniPoly::constant(BigRational::from_integer(m.clone())));
            match self.alpha.sign_of_poly(&diff)? {
                0 => return Some(FloorResult::Exact(m)),
                s if s < 0 => {
                    // value < m: floor is at most m - 1; keep refining until
                    // the enclosure settles.
                }
                _ => {
                    // value > m: floor is m if value < m+1; keep refining.
                }
            }
            match RealAlgebraic::refine_step(&self.alpha.poly, &lo, &hi)? {
                Refined::Interval(l, h) => {
                    lo = l;
                    hi = h;
                }
                Refined::Exact(r) => {
                    let v = self.residue.eval(&r);
                    let n = v.floor().to_integer();
                    return if v.is_integer() {
                        Some(FloorResult::Exact(n))
                    } else {
                        Some(FloorResult::Strict(n))
                    };
                }
            }
        }
        None
    }

    /// The value as a standalone number: the point itself for the identity
    /// residue; otherwise the derived algebraic number whose defining
    /// polynomial is (the square-free part of) the resultant
    /// `Res_x(q(x), y - r(x))` — or an exact rational when the derived root
    /// turns out rational. This is what powers z3-parity `root-obj` printing
    /// of compound expressions like `(+ x 1)` or `(* x x)` at `x = 5^(1/4)`.
    pub fn to_number(&self) -> Option<RealScalar> {
        if self.is_identity() {
            return Some(RealScalar::Algebraic(self.clone()));
        }
        let resultant = resultant_y_minus_r(&self.alpha.poly, &self.residue)?;
        let sf = square_free_part(&resultant)?;
        let sf = integer_normalize(&sf)?;
        if sf.degree().unwrap_or(0) < 1 {
            return None;
        }
        let seq = sturm_sequence(&sf);
        let mut lo = self.alpha.lo.clone();
        let mut hi = self.alpha.hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let (elo, ehi) = interval_eval(&self.residue, &lo, &hi);
            // Rational-value escape: if an enclosure endpoint is a root of the
            // resultant, the value may BE that rational; certify exactly.
            for cand in [&elo, &ehi] {
                if sf.eval(cand).is_zero() && self.cmp_rational(cand)? == std::cmp::Ordering::Equal
                {
                    return Some(RealScalar::Rational(cand.clone()));
                }
            }
            if elo < ehi
                && !sf.eval(&elo).is_zero()
                && !sf.eval(&ehi).is_zero()
                && sturm_count(&seq, &elo, &ehi) == 1
            {
                let derived = RealAlgebraic::from_isolating_interval(&sf, &elo, &ehi)?;
                return Some(RealScalar::Algebraic(derived.as_value()));
            }
            match RealAlgebraic::refine_step(&self.alpha.poly, &lo, &hi)? {
                Refined::Interval(l, h) => {
                    lo = l;
                    hi = h;
                }
                Refined::Exact(r) => {
                    return Some(RealScalar::Rational(self.residue.eval(&r)));
                }
            }
        }
        None
    }

    /// z3 `root-obj` rendering of the value, or `None` when no derived
    /// defining polynomial could be computed (callers fail closed) or when the
    /// value is exactly rational (`Some(Err(rational))`-style is avoided —
    /// use [`Self::to_number_for_output`] for the rational case).
    pub fn to_smtlib(&self) -> Option<String> {
        match self.to_number_for_output()? {
            RealScalar::Rational(_) => None,
            RealScalar::Algebraic(v) => Some(v.alpha.to_smtlib()),
        }
    }

    /// Exact equality with another algebraic value (any defining data).
    pub fn eq_value(&self, other: &Self) -> Option<bool> {
        self.try_cmp(other).map(|o| o == std::cmp::Ordering::Equal)
    }

    /// Exact reciprocal `1/self`. `None` when the value is exactly zero or on
    /// a refinement cap (fail closed) — never an approximation.
    pub fn recip(&self) -> Option<RealScalar> {
        match self.to_number()? {
            RealScalar::Rational(r) => {
                if r.is_zero() {
                    None
                } else {
                    Some(RealScalar::Rational(r.recip()))
                }
            }
            RealScalar::Algebraic(v) => v.alpha.recip_number(),
        }
    }

    /// Exact sum with an algebraic value over a DIFFERENT point, via the sum
    /// resultant `Res_y(p(y), q(z - y))` (see [`cross_op_numbers`]).
    pub fn cross_add(&self, other: &Self) -> Option<RealScalar> {
        self.cross_op(other, CrossOp::Add)
    }

    /// Exact product with an algebraic value over a DIFFERENT point, via the
    /// product resultant `Res_y(p(y), y^n q(z / y))` (see
    /// [`cross_op_numbers`]).
    pub fn cross_mul(&self, other: &Self) -> Option<RealScalar> {
        self.cross_op(other, CrossOp::Mul)
    }

    /// Common driver for the cross-point operations: normalize both operands
    /// to standalone numbers first (a residue can collapse to a rational),
    /// then dispatch — rational operands use plain residue arithmetic, two
    /// genuine algebraic numbers go through the exact resultant construction.
    fn cross_op(&self, other: &Self, op: CrossOp) -> Option<RealScalar> {
        let a = self.to_number()?;
        let b = other.to_number()?;
        match (a, b) {
            (RealScalar::Rational(x), RealScalar::Rational(y)) => Some(match op {
                CrossOp::Add => RealScalar::Rational(x + y),
                CrossOp::Mul => RealScalar::Rational(x * y),
            }),
            (RealScalar::Rational(x), RealScalar::Algebraic(v))
            | (RealScalar::Algebraic(v), RealScalar::Rational(x)) => Some(match op {
                CrossOp::Add => RealScalar::Algebraic(v.add_rational(&x)),
                CrossOp::Mul => v.mul_rational(&x),
            }),
            (RealScalar::Algebraic(va), RealScalar::Algebraic(vb)) => {
                cross_op_numbers(&va.alpha, &vb.alpha, op)
            }
        }
    }
}

/// Cross-point binary operation kind (see [`cross_op_numbers`]).
#[derive(Clone, Copy)]
enum CrossOp {
    Add,
    Mul,
}

/// Exact `alpha op beta` for two algebraic numbers over DIFFERENT points,
/// z3-style: a defining polynomial for the result is the resultant
///
///   * Add: `R(z) = Res_y(p(y), q(z - y))` — vanishes at every `a_i + b_j`,
///   * Mul: `R(z) = Res_y(p(y), y^n q(z / y))` — vanishes at every `a_i b_j`
///     (zero roots of `p`/`q` are divided out first; the represented roots
///     are nonzero, so they are unaffected),
///
/// computed exactly by evaluating fixed-dimension Sylvester determinants at
/// integer sample points and Lagrange-interpolating. The result root is then
/// isolated by refining both operand intervals until the interval-arithmetic
/// enclosure of `alpha op beta` contains exactly one root of (the square-free
/// part of) `R` — an exact rational when that root is rational, else the
/// derived algebraic number. `None` only on a refinement cap (fail closed).
fn cross_op_numbers(a: &RealAlgebraic, b: &RealAlgebraic, op: CrossOp) -> Option<RealScalar> {
    let (p, q) = match op {
        CrossOp::Add => (a.poly.clone(), b.poly.clone()),
        CrossOp::Mul => (strip_zero_roots(&a.poly)?, strip_zero_roots(&b.poly)?),
    };
    let m = p.degree()?;
    let n = q.degree()?;
    if m == 0 || n == 0 {
        return None;
    }
    let bound = m * n;
    let mut points: Vec<(BigRational, BigRational)> = Vec::with_capacity(bound + 1);
    for t in 0..=bound {
        let tv = BigRational::from_integer(BigInt::from(t as u64));
        let qt = match op {
            CrossOp::Add => compose_t_minus_y(&q, &tv),
            CrossOp::Mul => homogenize_at(&q, &tv),
        };
        let det = sylvester_det_fixed(p.coeffs(), &qt)?;
        points.push((tv, det));
    }
    let r = lagrange_interpolate(&points)?;
    if r.is_zero() {
        return None;
    }
    let sf = integer_normalize(&square_free_part(&r)?)?;
    if sf.degree().unwrap_or(0) < 1 {
        return None;
    }
    let seq = sturm_sequence(&sf);
    let markers = isolate_roots(&sf)?;
    let (mut la, mut ha) = (a.lo.clone(), a.hi.clone());
    let (mut lb, mut hb) = (b.lo.clone(), b.hi.clone());
    for _ in 0..MAX_REFINE_STEPS {
        let (elo, ehi) = match op {
            CrossOp::Add => (&la + &lb, &ha + &hb),
            CrossOp::Mul => interval_product(&la, &ha, &lb, &hb),
        };
        if elo < ehi
            && !sf.eval(&elo).is_zero()
            && !sf.eval(&ehi).is_zero()
            && sturm_count(&seq, &elo, &ehi) == 1
        {
            return scalar_from_isolated_root(&sf, &seq, &markers, &elo, &ehi);
        }
        match RealAlgebraic::refine_step(&a.poly, &la, &ha)? {
            Refined::Interval(l, h) => {
                la = l;
                ha = h;
            }
            // A bisection midpoint hit `a` exactly: it is rational after all;
            // finish with plain residue arithmetic on `b`.
            Refined::Exact(ra) => {
                let bv = b.as_value();
                return Some(match op {
                    CrossOp::Add => RealScalar::Algebraic(bv.add_rational(&ra)),
                    CrossOp::Mul => bv.mul_rational(&ra),
                });
            }
        }
        match RealAlgebraic::refine_step(&b.poly, &lb, &hb)? {
            Refined::Interval(l, h) => {
                lb = l;
                hb = h;
            }
            Refined::Exact(rb) => {
                let av = a.as_value();
                return Some(match op {
                    CrossOp::Add => RealScalar::Algebraic(av.add_rational(&rb)),
                    CrossOp::Mul => av.mul_rational(&rb),
                });
            }
        }
    }
    None
}

/// The single root of `sf` isolated by `(elo, ehi)` (endpoints non-root,
/// Sturm count 1), as an exact scalar: the rational root marker when that
/// root is rational, else the derived [`RealAlgebraic`] identity value.
fn scalar_from_isolated_root(
    sf: &UniPoly,
    seq: &[UniPoly],
    markers: &[RootMarker],
    elo: &BigRational,
    ehi: &BigRational,
) -> Option<RealScalar> {
    for mk in markers {
        match mk {
            RootMarker::Rational(r) => {
                if r > elo && r < ehi {
                    return Some(RealScalar::Rational(r.clone()));
                }
            }
            RootMarker::Interval(mlo, mhi) => {
                let ilo = if mlo > elo { mlo.clone() } else { elo.clone() };
                let ihi = if mhi < ehi { mhi.clone() } else { ehi.clone() };
                if ilo < ihi
                    && !sf.eval(&ilo).is_zero()
                    && !sf.eval(&ihi).is_zero()
                    && sturm_count(seq, &ilo, &ihi) == 1
                {
                    let alg = RealAlgebraic::from_isolating_interval(sf, &ilo, &ihi)?;
                    return Some(RealScalar::Algebraic(alg.as_value()));
                }
            }
        }
    }
    None
}

/// Coefficients (length `deg(q) + 1`, low-to-high in `y`) of `q(t - y)`.
/// The leading coefficient is `±q_n`, so the nominal degree never drops.
fn compose_t_minus_y(q: &UniPoly, t: &BigRational) -> Vec<BigRational> {
    let mut acc: Vec<BigRational> = Vec::new();
    for c in q.coeffs().iter().rev() {
        // acc := acc * (t - y) + c   (Horner in the outer variable).
        let mut next = vec![BigRational::zero(); acc.len() + 1];
        for (k, a) in acc.iter().enumerate() {
            next[k] += a * t;
            let neg = -a;
            next[k + 1] += neg;
        }
        next[0] += c;
        acc = next;
    }
    acc
}

/// Coefficients (length `deg(q) + 1`, low-to-high in `y`) of `y^n * q(t/y)`:
/// the coefficient of `y^(n-j)` is `q_j * t^j`. With zero roots of `q`
/// divided out beforehand, the leading coefficient is `q_0 != 0`, so the
/// nominal degree never drops.
fn homogenize_at(q: &UniPoly, t: &BigRational) -> Vec<BigRational> {
    let qc = q.coeffs();
    let n = qc.len() - 1;
    let mut out = vec![BigRational::zero(); n + 1];
    let mut tpow = BigRational::one();
    for (j, c) in qc.iter().enumerate() {
        out[n - j] = c * &tpow;
        tpow *= t;
    }
    out
}

/// Divide out the `y^k` factor (zero roots). The represented roots are
/// nonzero, so root isolation over the quotient is unaffected. `None` for
/// the zero polynomial.
fn strip_zero_roots(p: &UniPoly) -> Option<UniPoly> {
    let c = p.coeffs();
    let k = c.iter().position(|x| !x.is_zero())?;
    Some(UniPoly::from_coeffs(c[k..].to_vec()))
}

/// Exact interval product: a closed rational enclosure of
/// `{s * t : s in [la, ha], t in [lb, hb]}`.
fn interval_product(
    la: &BigRational,
    ha: &BigRational,
    lb: &BigRational,
    hb: &BigRational,
) -> (BigRational, BigRational) {
    let p1 = la * lb;
    let p2 = la * hb;
    let p3 = ha * lb;
    let p4 = ha * hb;
    let mut mn = p1.clone();
    let mut mx = p1;
    for v in [p2, p3, p4] {
        if v < mn {
            mn = v.clone();
        }
        if v > mx {
            mx = v;
        }
    }
    (mn, mx)
}

/// Result of [`RealAlgebraicValue::floor_boundary`].
enum FloorResult {
    /// The value is exactly this integer.
    Exact(BigInt),
    /// The value lies strictly between this integer and the next.
    Strict(BigInt),
}

/// Normalize to integer coefficients with content 1 and a positive leading
/// coefficient (canonical form for identity comparison and z3 printing).
/// Root set is unchanged. `None` for the zero polynomial.
fn integer_normalize(p: &UniPoly) -> Option<UniPoly> {
    let coeffs = p.coeffs();
    if coeffs.is_empty() {
        return None;
    }
    // Common denominator.
    let mut denom_lcm = BigInt::one();
    for c in coeffs {
        denom_lcm = denom_lcm.lcm(c.denom());
    }
    let ints: Vec<BigInt> = coeffs
        .iter()
        .map(|c| c.numer() * (&denom_lcm / c.denom()))
        .collect();
    // Content.
    let mut content = BigInt::zero();
    for c in &ints {
        content = content.gcd(c);
    }
    if content.is_zero() {
        return None;
    }
    let leading_negative = ints.last().map(|c| c.is_negative()).unwrap_or(false);
    let divisor = if leading_negative { -content } else { content };
    let normalized: Vec<BigRational> = ints
        .iter()
        .map(|c| BigRational::from_integer(c / &divisor))
        .collect();
    Some(UniPoly::from_coeffs(normalized))
}

/// Exact interval evaluation (Horner) of `p` over `[lo, hi]`: returns a
/// closed rational enclosure of `{p(t) : t in [lo, hi]}`.
fn interval_eval(p: &UniPoly, lo: &BigRational, hi: &BigRational) -> (BigRational, BigRational) {
    let mut acc_lo = BigRational::zero();
    let mut acc_hi = BigRational::zero();
    for c in p.coeffs().iter().rev() {
        // [acc_lo, acc_hi] * [lo, hi]
        let p1 = &acc_lo * lo;
        let p2 = &acc_lo * hi;
        let p3 = &acc_hi * lo;
        let p4 = &acc_hi * hi;
        let mut mn = p1.clone();
        let mut mx = p1;
        for v in [p2, p3, p4] {
            if v < mn {
                mn = v.clone();
            }
            if v > mx {
                mx = v;
            }
        }
        acc_lo = mn + c;
        acc_hi = mx + c;
    }
    (acc_lo, acc_hi)
}

/// The resultant `R(y) = Res_x(q(x), y - r(x))`, a degree-`deg q` polynomial
/// in `y` that vanishes at `r(alpha)` for every root `alpha` of `q`. Computed
/// exactly by evaluating the Sylvester determinant at `deg q + 1` integer
/// points and Lagrange-interpolating.
fn resultant_y_minus_r(q: &UniPoly, r: &UniPoly) -> Option<UniPoly> {
    let m = q.degree()?;
    if m == 0 {
        return None;
    }
    let mut points: Vec<(BigRational, BigRational)> = Vec::with_capacity(m + 1);
    for j in 0..=m {
        let y = BigRational::from_integer(BigInt::from(j as i64));
        // g(x) = y - r(x)
        let g = UniPoly::constant(y.clone()).sub(r);
        let det = sylvester_resultant(q, &g)?;
        points.push((y, det));
    }
    lagrange_interpolate(&points)
}

/// Numeric resultant of two univariate polynomials via the Sylvester matrix
/// determinant (exact Gaussian elimination over `BigRational`).
fn sylvester_resultant(f: &UniPoly, g: &UniPoly) -> Option<BigRational> {
    sylvester_det_fixed(f.coeffs(), g.coeffs())
}

/// Sylvester determinant for coefficient vectors with FIXED nominal degrees
/// `fc.len()-1` and `gc.len()-1` (leading entries MAY be zero). This is what
/// bivariate resultant interpolation needs: specializing a coefficient
/// polynomial at a sample point can vanish the leading coefficient, and the
/// specialized resultant equals the determinant of the GENERIC-degree
/// Sylvester matrix with the specialized entries — NOT the resultant of the
/// degree-dropped polynomials.
pub(crate) fn sylvester_det_fixed(fc: &[BigRational], gc: &[BigRational]) -> Option<BigRational> {
    if fc.is_empty() || gc.is_empty() {
        return None;
    }
    let m = fc.len() - 1;
    let d = gc.len() - 1;
    let n = m + d;
    if n == 0 {
        return Some(BigRational::one());
    }
    // Row i (0 <= i < d): coefficients of x^(d-1-i) * f, descending powers.
    // Row d+i (0 <= i < m): likewise for g.
    let mut mat: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); n]; n];
    for i in 0..d {
        for (k, c) in fc.iter().rev().enumerate() {
            mat[i][i + k] = c.clone();
        }
    }
    for i in 0..m {
        for (k, c) in gc.iter().rev().enumerate() {
            mat[d + i][i + k] = c.clone();
        }
    }
    // Gaussian elimination with exact pivoting.
    let mut det = BigRational::one();
    for col in 0..n {
        let pivot_row = (col..n).find(|&row| !mat[row][col].is_zero());
        let Some(pr) = pivot_row else {
            return Some(BigRational::zero());
        };
        if pr != col {
            mat.swap(pr, col);
            det = -det;
        }
        let pivot = mat[col][col].clone();
        det *= &pivot;
        let (upper, lower) = mat.split_at_mut(col + 1);
        let pivot_row = &upper[col];
        for row in &mut *lower {
            if row[col].is_zero() {
                continue;
            }
            let factor = &row[col] / &pivot;
            for (entry, pivot_entry) in row[col..].iter_mut().zip(&pivot_row[col..]) {
                let sub = pivot_entry * &factor;
                *entry -= sub;
            }
        }
    }
    Some(det)
}

/// Lagrange interpolation through `points` (distinct abscissae), returning the
/// unique polynomial of degree < points.len().
pub(crate) fn lagrange_interpolate(points: &[(BigRational, BigRational)]) -> Option<UniPoly> {
    let mut acc = UniPoly::zero();
    for (i, (xi, yi)) in points.iter().enumerate() {
        if yi.is_zero() {
            continue;
        }
        let mut basis = UniPoly::constant(BigRational::one());
        let mut denom = BigRational::one();
        for (j, (xj, _)) in points.iter().enumerate() {
            if i == j {
                continue;
            }
            // basis *= (x - xj)
            basis = basis.mul(&UniPoly::x().sub(&UniPoly::constant(xj.clone())));
            denom *= xi - xj;
        }
        if denom.is_zero() {
            return None; // duplicate abscissae (caller bug)
        }
        let scale = yi / &denom;
        acc = acc.add(&basis.scale(&scale));
    }
    Some(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(coeffs: &[i64]) -> UniPoly {
        UniPoly::from_coeffs(
            coeffs
                .iter()
                .map(|&c| BigRational::from_integer(BigInt::from(c)))
                .collect(),
        )
    }

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn ratf(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// sqrt(2) as the 2nd root of x^2 - 2.
    fn sqrt2() -> RealAlgebraic {
        RealAlgebraic::from_isolating_interval(&poly(&[-2, 0, 1]), &rat(1), &rat(2))
            .expect("sqrt(2) isolates")
    }

    /// -sqrt(2) as the 1st root of x^2 - 2.
    fn neg_sqrt2() -> RealAlgebraic {
        RealAlgebraic::from_isolating_interval(&poly(&[-2, 0, 1]), &rat(-2), &rat(-1))
            .expect("-sqrt(2) isolates")
    }

    #[test]
    fn root_index_matches_z3() {
        assert_eq!(sqrt2().root_index(), 2);
        assert_eq!(neg_sqrt2().root_index(), 1);
        // cbrt(2): only real root of x^3 - 2.
        let cbrt2 = RealAlgebraic::from_isolating_interval(&poly(&[-2, 0, 0, 1]), &rat(1), &rat(2))
            .expect("cbrt(2) isolates");
        assert_eq!(cbrt2.root_index(), 1);
    }

    #[test]
    fn smtlib_rendering_matches_z3_forms() {
        assert_eq!(sqrt2().to_smtlib(), "(root-obj (+ (^ x 2) (- 2)) 2)");
        assert_eq!(neg_sqrt2().to_smtlib(), "(root-obj (+ (^ x 2) (- 2)) 1)");
        // 2x^2 - 1, positive root (z3: (root-obj (+ (* 2 (^ x 2)) (- 1)) 2)).
        let r = RealAlgebraic::from_isolating_interval(&poly(&[-1, 0, 2]), &ratf(1, 2), &rat(1))
            .expect("isolates");
        assert_eq!(r.to_smtlib(), "(root-obj (+ (* 2 (^ x 2)) (- 1)) 2)");
        // x^3 - 2x - 2, real root near 1.77
        // (z3: (root-obj (+ (^ x 3) (* (- 2) x) (- 2)) 1)).
        let r = RealAlgebraic::from_isolating_interval(&poly(&[-2, -2, 0, 1]), &rat(1), &rat(2))
            .expect("isolates");
        assert_eq!(r.to_smtlib(), "(root-obj (+ (^ x 3) (* (- 2) x) (- 2)) 1)");
    }

    #[test]
    fn squares_reduce_to_rationals() {
        // (sqrt 2)^2 = 2 exactly.
        let x = sqrt2().as_value();
        let sq = x.try_mul(&x).expect("same point");
        match sq {
            RealScalar::Rational(r) => assert_eq!(r, rat(2)),
            RealScalar::Algebraic(_) => panic!("x*x must reduce to the rational 2"),
        }
    }

    #[test]
    fn signs_and_comparisons_are_exact() {
        let x = sqrt2().as_value();
        assert_eq!(x.sign(), Some(1));
        assert_eq!(neg_sqrt2().as_value().sign(), Some(-1));
        // 1.414213 < sqrt(2) < 1.414214
        assert_eq!(
            x.cmp_rational(&ratf(1_414_213, 1_000_000)),
            Some(std::cmp::Ordering::Greater)
        );
        assert_eq!(
            x.cmp_rational(&ratf(1_414_214, 1_000_000)),
            Some(std::cmp::Ordering::Less)
        );
        // sqrt(2) == sqrt(2) via a DIFFERENT defining polynomial:
        // 2nd root of x^4 - 4 (roots -sqrt2, sqrt2) vs 2nd root of x^2 - 2.
        let other =
            RealAlgebraic::from_isolating_interval(&poly(&[-4, 0, 0, 0, 1]), &rat(1), &rat(2))
                .expect("isolates");
        assert_eq!(sqrt2().cmp_number(&other), Some(std::cmp::Ordering::Equal));
        assert_eq!(
            sqrt2().cmp_number(&neg_sqrt2()),
            Some(std::cmp::Ordering::Greater)
        );
    }

    #[test]
    fn integrality_and_floor_are_exact() {
        let x = sqrt2().as_value();
        assert_eq!(x.is_integer(), Some(false));
        assert_eq!(x.floor(), Some(BigInt::from(1)));
        assert_eq!(neg_sqrt2().as_value().floor(), Some(BigInt::from(-2)));
        // x + (2 - x) is exactly 2 (integer), via residue arithmetic.
        let two_minus = x.neg().add_rational(&rat(2));
        let sum = x.try_add(&two_minus).expect("same point");
        match sum {
            RealScalar::Rational(r) => assert_eq!(r, rat(2)),
            RealScalar::Algebraic(_) => panic!("must collapse to rational"),
        }
    }

    #[test]
    fn derived_numbers_via_resultant_match_z3() {
        // x = 5^(1/4) (1st positive real root of x^4 - 5, index 2 of the two
        // real roots). z3: (* x x) -> (root-obj (+ (^ x 2) (- 5)) 2).
        let x = RealAlgebraic::from_isolating_interval(&poly(&[-5, 0, 0, 0, 1]), &rat(1), &rat(2))
            .expect("isolates");
        let v = x.as_value();
        let sq = match v.try_mul(&v).expect("same point") {
            RealScalar::Algebraic(a) => a,
            RealScalar::Rational(r) => panic!("x*x = sqrt(5) is irrational, got {r}"),
        };
        assert_eq!(
            sq.to_smtlib().as_deref(),
            Some("(root-obj (+ (^ x 2) (- 5)) 2)")
        );
        // (+ x 1) at x = sqrt2: z3 -> (root-obj (+ (^ x 2) (* (- 2) x) (- 1)) 2).
        let xp1 = sqrt2().as_value().add_rational(&rat(1));
        assert_eq!(
            xp1.to_smtlib().as_deref(),
            Some("(root-obj (+ (^ x 2) (* (- 2) x) (- 1)) 2)")
        );
        // (- x) at x = sqrt2: z3 -> (root-obj (+ (^ x 2) (- 2)) 1).
        let neg = sqrt2().as_value().neg();
        assert_eq!(
            neg.to_smtlib().as_deref(),
            Some("(root-obj (+ (^ x 2) (- 2)) 1)")
        );
        // (* 3 x) at x = sqrt2: z3 -> (root-obj (+ (^ x 2) (- 18)) 2).
        let scaled = match sqrt2().as_value().mul_rational(&rat(3)) {
            RealScalar::Algebraic(a) => a,
            RealScalar::Rational(_) => panic!("3*sqrt2 is irrational"),
        };
        assert_eq!(
            scaled.to_smtlib().as_deref(),
            Some("(root-obj (+ (^ x 2) (- 18)) 2)")
        );
    }

    #[test]
    fn reciprocal_is_exact() {
        // 1/sqrt2: positive root of 2x^2 - 1 (z3 parity), and
        // (1/sqrt2) * sqrt2 collapses to exactly 1 (cross-point product).
        let x = sqrt2().as_value();
        let r = match x.recip().expect("nonzero value") {
            RealScalar::Algebraic(v) => v,
            RealScalar::Rational(r) => panic!("1/sqrt2 is irrational, got {r}"),
        };
        assert_eq!(
            r.to_smtlib().as_deref(),
            Some("(root-obj (+ (* 2 (^ x 2)) (- 1)) 2)")
        );
        match RealScalar::Algebraic(r)
            .mul(&RealScalar::Algebraic(x))
            .expect("computable")
        {
            RealScalar::Rational(v) => assert_eq!(v, rat(1)),
            RealScalar::Algebraic(_) => panic!("(1/sqrt2)*sqrt2 must collapse to 1"),
        }
        // Rational-valued reciprocal: 1/(sqrt2 * sqrt2) = 1/2.
        let sq = sqrt2().as_value();
        let two = match sq.try_mul(&sq).expect("same point") {
            RealScalar::Rational(v) => v,
            RealScalar::Algebraic(_) => panic!("sqrt2^2 is rational"),
        };
        assert_eq!(
            RealScalar::Rational(two).recip().map(|s| match s {
                RealScalar::Rational(v) => v,
                RealScalar::Algebraic(_) => panic!("1/2 is rational"),
            }),
            Some(ratf(1, 2))
        );
    }

    #[test]
    fn cross_point_sum_and_product_match_z3() {
        let s2 = sqrt2().as_value();
        let s3 = RealAlgebraic::from_isolating_interval(&poly(&[-3, 0, 1]), &rat(1), &rat(2))
            .expect("sqrt3 isolates")
            .as_value();
        // sqrt2 + sqrt3: 4th root of x^4 - 10x^2 + 1 (z3 parity).
        match s2.cross_add(&s3).expect("computable") {
            RealScalar::Algebraic(v) => assert_eq!(
                v.to_smtlib().as_deref(),
                Some("(root-obj (+ (^ x 4) (* (- 10) (^ x 2)) 1) 4)")
            ),
            RealScalar::Rational(r) => panic!("sqrt2+sqrt3 is irrational, got {r}"),
        }
        // sqrt2 * sqrt3 = sqrt6: positive root of x^2 - 6 (z3 parity).
        match s2.cross_mul(&s3).expect("computable") {
            RealScalar::Algebraic(v) => assert_eq!(
                v.to_smtlib().as_deref(),
                Some("(root-obj (+ (^ x 2) (- 6)) 2)")
            ),
            RealScalar::Rational(r) => panic!("sqrt6 is irrational, got {r}"),
        }
        // Cross-point ops that collapse to exact rationals: sqrt2 (as root of
        // x^2 - 2) times/plus sqrt2 / -sqrt2 represented over x^4 - 4.
        let pos4 =
            RealAlgebraic::from_isolating_interval(&poly(&[-4, 0, 0, 0, 1]), &rat(1), &rat(2))
                .expect("isolates")
                .as_value();
        let neg4 =
            RealAlgebraic::from_isolating_interval(&poly(&[-4, 0, 0, 0, 1]), &rat(-2), &rat(-1))
                .expect("isolates")
                .as_value();
        match s2.cross_mul(&pos4).expect("computable") {
            RealScalar::Rational(v) => assert_eq!(v, rat(2)),
            RealScalar::Algebraic(_) => panic!("sqrt2*sqrt2 must collapse to 2"),
        }
        match s2.cross_add(&neg4).expect("computable") {
            RealScalar::Rational(v) => assert_eq!(v, rat(0)),
            RealScalar::Algebraic(_) => panic!("sqrt2 + (-sqrt2) must collapse to 0"),
        }
    }

    #[test]
    fn zero_certificate_via_gcd() {
        // sign of (x^2 - 2) at sqrt(2) is exactly 0.
        assert_eq!(sqrt2().sign_of_poly(&poly(&[-2, 0, 1])), Some(0));
        // sign of (x^2 - 3) at sqrt(2) is negative.
        assert_eq!(sqrt2().sign_of_poly(&poly(&[-3, 0, 1])), Some(-1));
    }

    #[test]
    fn rejects_non_isolating_intervals() {
        // (0, 2) contains only sqrt(2)? No — it contains one root; but (-2, 2)
        // contains both roots of x^2 - 2 and must be rejected.
        assert!(
            RealAlgebraic::from_isolating_interval(&poly(&[-2, 0, 1]), &rat(-2), &rat(2)).is_none()
        );
        // Endpoint IS a root: reject.
        assert!(
            RealAlgebraic::from_isolating_interval(&poly(&[-4, 0, 1]), &rat(2), &rat(3)).is_none()
        );
    }
}
