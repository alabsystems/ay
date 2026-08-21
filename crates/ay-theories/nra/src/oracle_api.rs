// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feature-gated facade over the crate-private exact univariate / real-algebraic
//! primitives, used ONLY by the dev-only differential oracle
//! (`crates/ay-nra-oracle`).
//!
//! Nothing in the solver depends on this module: it is compiled only when the
//! `oracle-api` feature is on, which no shipping build ever enables. It exists
//! because [`crate::univariate::UniPoly`] and friends are `pub(crate)` — the
//! oracle has to reach them without widening the crate's real public surface.
//!
//! The wrappers are newtypes, not re-exports, so the crate-private types stay
//! crate-private and the facade can be deleted without touching solver code.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::algebraic::{sylvester_det_fixed, RealAlgebraic, RealScalar};
use crate::anum;
use crate::explain;
use crate::ialg;
use crate::mpbq;
use crate::mroot;
use crate::polymanager;
use crate::subresultant::{self, MPolyZ, Mono, RPoly};
use crate::univariate::{
    isolate_roots, poly_gcd, rational_sign, square_free_part, sturm_count, sturm_sequence,
    RootMarker, UniPoly,
};
use crate::upoly;

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

// ============================================================================
// The fraction-free subresultant / psc-chain substrate (`crate::subresultant`)
// ============================================================================
//
// Everything above this line wraps primitives AY has shipped for a long time.
// Everything below wraps `crate::subresultant` — 969 lines of NEW code on the
// CAD projection path, whose entire surface is `pub(crate)` inside a private
// `mod`, and which no differential oracle could reach until this facade
// existed. That unreachability is the point: the resultant check above calls
// `sylvester_det_fixed` from `algebraic.rs`, a DIFFERENT implementation, so a
// clean oracle run said nothing whatsoever about this module.

/// A univariate polynomial over `Z` — the coefficient ring the fraction-free
/// chain is actually written for.
#[derive(Clone, Debug, PartialEq)]
pub struct OZPoly(RPoly<BigInt>);

impl OZPoly {
    /// Build from low-to-high integer coefficients (trailing zeros trimmed).
    #[must_use]
    pub fn from_ints(coeffs: Vec<BigInt>) -> Self {
        Self(RPoly::from_coeffs(coeffs))
    }

    /// Low-to-high integer coefficients.
    #[must_use]
    pub fn coeffs(&self) -> Vec<BigInt> {
        self.0.coeffs().to_vec()
    }

    /// Degree, or `None` for the zero polynomial.
    #[must_use]
    pub fn degree(&self) -> Option<usize> {
        self.0.degree()
    }

    /// [`crate::subresultant::psc_chain`]: `psc_j` for `j` in `0..deg min`,
    /// lowest index first, zeros included.
    #[must_use]
    pub fn psc_chain(&self, other: &Self) -> Option<Vec<BigInt>> {
        subresultant::psc_chain(&self.0, &other.0)
    }

    /// [`crate::subresultant::resultant`] — the fraction-free `S_0`, NOT the
    /// Sylvester determinant that [`resultant`] above calls.
    #[must_use]
    pub fn resultant(&self, other: &Self) -> Option<BigInt> {
        subresultant::resultant(&self.0, &other.0)
    }

    /// [`crate::subresultant::discriminant`].
    #[must_use]
    pub fn discriminant(&self) -> Option<BigInt> {
        subresultant::discriminant(&self.0)
    }

    /// The full subresultant chain `S_0 .. S_n` as coefficient vectors, via the
    /// determinantal definition — the independent second implementation the PRS
    /// is supposed to agree with.
    #[must_use]
    pub fn subresultant_chain_det(&self, other: &Self) -> Option<Vec<Vec<BigInt>>> {
        let (p, q) = order_by_degree(&self.0, &other.0)?;
        let chain = subresultant::subresultant_chain_det(p, q)?;
        Some(chain.iter().map(|s| s.coeffs().to_vec()).collect())
    }

    /// The same chain via the fraction-free PRS recurrence. `None` when the
    /// recurrence's preconditions do not hold (`deg f > deg g >= 1`).
    #[must_use]
    pub fn subresultant_chain_prs(&self, other: &Self) -> Option<Vec<Vec<BigInt>>> {
        let (p, q) = order_by_degree(&self.0, &other.0)?;
        let chain = subresultant::subresultant_chain_prs(p, q)?;
        Some(chain.iter().map(|s| s.coeffs().to_vec()).collect())
    }
}

fn order_by_degree<'a, R: subresultant::ExactRing>(
    f: &'a RPoly<R>,
    g: &'a RPoly<R>,
) -> Option<(&'a RPoly<R>, &'a RPoly<R>)> {
    if f.degree()? >= g.degree()? {
        Some((f, g))
    } else {
        Some((g, f))
    }
}

/// A polynomial in `y` over `Z`: one coefficient of an [`OBiPoly`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OYPoly(MPolyZ);

impl OYPoly {
    /// Evaluate at `y = c`.
    ///
    /// The bivariate checks compare AY's multivariate psc entries against z3's
    /// univariate ones by specializing; this is the specialization map. It is
    /// deliberately implemented HERE and not in `subresultant`, so the module
    /// under test contributes nothing to the comparison but the answer.
    #[must_use]
    pub fn eval_at(&self, c: &BigInt) -> BigInt {
        let mut acc = BigInt::from(0);
        for (mono, coeff) in self.0.terms() {
            let mut term = coeff.clone();
            for &(_v, e) in mono.pairs() {
                term *= c.pow(e);
            }
            acc += term;
        }
        acc
    }

    /// Is this the zero polynomial?
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.terms().is_empty()
    }

    /// `(y-exponent, coefficient)` pairs, for reproducer rendering.
    #[must_use]
    pub fn terms(&self) -> Vec<(u32, BigInt)> {
        self.0
            .terms()
            .iter()
            .map(|(m, c)| {
                let e = m.pairs().first().map_or(0, |&(_, e)| e);
                (e, c.clone())
            })
            .collect()
    }
}

/// A BIVARIATE polynomial: univariate in the main variable `x`, with
/// coefficients in `Z[y]`.
///
/// This is the shape CAD projection actually operates on, and the shape the
/// univariate-only oracle never touched. Exercising it drives `MPolyZ`'s
/// multivariate `exact_div` — the operation the whole fraction-free design
/// rests on, and the one with no univariate analogue to fall back to.
#[derive(Clone, Debug, PartialEq)]
pub struct OBiPoly(RPoly<MPolyZ>);

/// The single `MPolyZ` variable index used for `y`.
const Y: u32 = 0;

impl OBiPoly {
    /// Build from `x`-coefficients, each given as `(y-exponent, coefficient)`
    /// pairs, low-to-high in `x`.
    #[must_use]
    pub fn from_x_coeffs(x_coeffs: &[Vec<(u32, BigInt)>]) -> Self {
        let coeffs: Vec<MPolyZ> = x_coeffs
            .iter()
            .map(|terms| {
                MPolyZ::from_terms(
                    terms
                        .iter()
                        .map(|(e, c)| (Mono::var_pow(Y, *e), c.clone()))
                        .collect(),
                )
            })
            .collect();
        Self(RPoly::from_coeffs(coeffs))
    }

    /// Degree in `x`, or `None` for the zero polynomial.
    #[must_use]
    pub fn degree_x(&self) -> Option<usize> {
        self.0.degree()
    }

    /// The leading `x`-coefficient, an element of `Z[y]`.
    #[must_use]
    pub fn leading_x(&self) -> Option<OYPoly> {
        self.0.leading().map(|c| OYPoly(c.clone()))
    }

    /// Substitute `y = c`, yielding a univariate integer polynomial.
    ///
    /// The `x`-degree is preserved exactly when `leading_x().eval_at(c)` is
    /// non-zero; the caller must check that before comparing specialized
    /// subresultants, because subresultants only commute with a specialization
    /// that preserves degree.
    #[must_use]
    pub fn specialize(&self, c: &BigInt) -> OZPoly {
        OZPoly(RPoly::from_coeffs(
            self.0
                .coeffs()
                .iter()
                .map(|m| OYPoly(m.clone()).eval_at(c))
                .collect(),
        ))
    }

    /// [`crate::subresultant::psc_chain`] over `Z[y]`.
    #[must_use]
    pub fn psc_chain(&self, other: &Self) -> Option<Vec<OYPoly>> {
        subresultant::psc_chain(&self.0, &other.0).map(|v| v.into_iter().map(OYPoly).collect())
    }

    /// [`crate::subresultant::resultant`] over `Z[y]` — the CAD projection
    /// primitive proper.
    #[must_use]
    pub fn resultant(&self, other: &Self) -> Option<OYPoly> {
        subresultant::resultant(&self.0, &other.0).map(OYPoly)
    }

    /// [`crate::subresultant::discriminant`] over `Z[y]`.
    #[must_use]
    pub fn discriminant(&self) -> Option<OYPoly> {
        subresultant::discriminant(&self.0).map(OYPoly)
    }
}

// ============================================================================
// Root isolation at an algebraic sample point (`crate::mroot`)
// ============================================================================
//
// The two nlsat-specific entry points: `isolate_roots` at a `var2anum` tuple
// and `isolate_roots_closest`. They have DIRECT z3 C-API counterparts —
// `Z3_algebraic_roots(c, p, n, a)` and `Z3_algebraic_eval(c, p, n, a)` are
// nothing but `isolate_roots(p, x2v, roots)` and `eval_sign_at(p, x2v)` with
// an expression-to-polynomial converter in front — so unlike everything above,
// these are compared against z3 answering the SAME question, not against a
// derived identity.

/// A value at a sample point: an exact rational, or a real algebraic number.
#[derive(Clone, Debug)]
pub struct OAnum(mroot::Anum);

impl OAnum {
    /// A rational sample value.
    #[must_use]
    pub fn rational(r: BigRational) -> Self {
        Self(mroot::Anum::Rat(r))
    }

    /// An algebraic sample value.
    #[must_use]
    pub fn algebraic(a: &OAlg) -> Self {
        Self(mroot::Anum::Alg(a.0.clone()))
    }

    /// Exact comparison against a rational; `None` when AY declines.
    #[must_use]
    pub fn cmp_rational(&self, r: &BigRational) -> Option<Ordering> {
        self.0.cmp_rational(r)
    }

    /// Is this value exactly rational?
    #[must_use]
    pub fn is_rational(&self) -> bool {
        matches!(self.0, mroot::Anum::Rat(_))
    }

    /// Degree of the defining polynomial (`1` for a rational).
    #[must_use]
    pub fn degree(&self) -> usize {
        self.0.degree()
    }
}

/// An assignment of sample values to variables — z3's `var2anum`.
#[derive(Clone, Debug, Default)]
pub struct OVar2Anum(mroot::Var2Anum);

impl OVar2Anum {
    /// The empty assignment.
    #[must_use]
    pub fn new() -> Self {
        Self(mroot::Var2Anum::new())
    }

    /// Bind variable `v`.
    pub fn set(&mut self, v: u32, a: &OAnum) {
        self.0.set(v, a.0.clone());
    }
}

/// A sparse multivariate polynomial over `Z`, built from
/// `(exponent vector, coefficient)` terms. Exponent entries past the end of a
/// vector are zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OMPoly(MPolyZ);

impl OMPoly {
    /// Build from `(exponents, coefficient)` terms.
    #[must_use]
    pub fn from_terms(terms: &[(Vec<u32>, BigInt)]) -> Self {
        Self(MPolyZ::from_terms(
            terms
                .iter()
                .map(|(exps, c)| {
                    (
                        Mono::from_pairs(
                            exps.iter()
                                .enumerate()
                                .map(|(v, &e)| (u32::try_from(v).unwrap_or(u32::MAX), e))
                                .collect(),
                        ),
                        c.clone(),
                    )
                })
                .collect(),
        ))
    }

    /// Is this the zero polynomial?
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.terms().is_empty()
    }

    /// Degree in variable `v`.
    #[must_use]
    pub fn degree_in(&self, v: u32) -> usize {
        mroot::degree_in(&self.0, v)
    }

    /// The variables that occur, ascending.
    #[must_use]
    pub fn vars(&self) -> Vec<u32> {
        mroot::vars_of(&self.0)
    }

    /// [`crate::mroot::eval_sign_at`] — the EXACT sign of this polynomial at
    /// the sample point. The direct counterpart of `Z3_algebraic_eval`.
    #[must_use]
    pub fn eval_sign_at(&self, x2v: &OVar2Anum) -> Option<i32> {
        mroot::eval_sign_at(&self.0, &x2v.0)
    }

    /// [`crate::mroot::isolate_roots_at`] — the real roots in `x` with every
    /// other variable fixed at the sample point, ascending. The direct
    /// counterpart of `Z3_algebraic_roots`.
    #[must_use]
    pub fn isolate_roots_at(&self, x: u32, x2v: &OVar2Anum) -> Option<Vec<OAnum>> {
        mroot::isolate_roots_at(&self.0, x, &x2v.0).map(|rs| rs.into_iter().map(OAnum).collect())
    }

    /// [`crate::mroot::isolate_roots_closest_at`] — the roots bracketing `s`,
    /// with their 1-based indices in the full ascending root list.
    #[must_use]
    pub fn isolate_roots_closest_at(
        &self,
        x: u32,
        x2v: &OVar2Anum,
        s: &BigRational,
    ) -> Option<(Vec<OAnum>, Vec<usize>)> {
        mroot::isolate_roots_closest_at(&self.0, x, &x2v.0, s)
            .map(|(rs, idx)| (rs.into_iter().map(OAnum).collect(), idx))
    }
}

// ===========================================================================
// The sparse multivariate polynomial manager (`crate::polymanager`)
// ===========================================================================

/// Facade over [`crate::polymanager::PolyManager`].
///
/// The manager owns the interned monomial table, so every polynomial handed
/// out by this type belongs to the manager that produced it and the oracle
/// keeps exactly one alive per case. Handles are opaque [`OMgrPoly`] values;
/// the oracle never sees a `MonoId`, which is what keeps a manager mix-up
/// impossible from outside the crate.
pub struct OPolyMgr(polymanager::PolyManager);

/// A polynomial belonging to an [`OPolyMgr`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OMgrPoly(polymanager::Poly);

/// Why one `mod_gcd` call declined, as counted inside the manager.
///
/// A decline is always SAFE (`PolyManager::gcd` falls back to the subresultant
/// PRS) but it is never free, so raising the certification rate needs to know
/// WHICH mechanism gave up. This is the read-only view of those counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OModGcdDiag(polymanager::ModGcdDiag);

impl OModGcdDiag {
    /// The single dominant cause, as a stable label suitable for a histogram
    /// key. `"certified"` when the call did not decline.
    #[must_use]
    pub fn primary(&self) -> &'static str {
        self.0.primary()
    }

    /// Whether the call ended in a certified answer.
    #[must_use]
    pub fn certified(&self) -> bool {
        self.0.certified()
    }

    /// Answers returned by a shortcut instead of by the certificate: a zero
    /// input, a constant input, or a unit modular image.
    #[must_use]
    pub fn shortcuts(&self) -> u32 {
        self.0.shortcut_zero + self.0.shortcut_const + self.0.shortcut_unit_image
    }

    /// Primes entered, and primes rejected before the recursion ran.
    #[must_use]
    pub fn primes_used(&self) -> u32 {
        self.0.primes_used
    }
    /// Primes rejected because a coefficient of `u` or `v` vanished mod `p`.
    #[must_use]
    pub fn prime_bad_coeff(&self) -> u32 {
        self.0.prime_bad_coeff
    }
    /// Primes rejected because the imposed leading coefficient vanished mod `p`.
    #[must_use]
    pub fn prime_bad_lcg(&self) -> u32 {
        self.0.prime_bad_lcg
    }
    /// Primes whose `Z_p` Brown recursion declined.
    #[must_use]
    pub fn prime_rec_declined(&self) -> u32 {
        self.0.prime_rec_declined
    }
    /// CRA rounds whose candidate failed the leading-coefficient gate.
    #[must_use]
    pub fn lc_gate_rejected(&self) -> u32 {
        self.0.lc_gate_rejected
    }
    /// Times the EXACT certificate rejected on the `u` leg.
    #[must_use]
    pub fn cert_reject_u(&self) -> u32 {
        self.0.cert_reject_u
    }
    /// Times the EXACT certificate rejected on the `v` leg.
    #[must_use]
    pub fn cert_reject_v(&self) -> u32 {
        self.0.cert_reject_v
    }
    /// Times the EXACT certificate accepted.
    #[must_use]
    pub fn cert_accepted(&self) -> u32 {
        self.0.cert_accepted
    }
    /// CRA steps that could not be combined.
    #[must_use]
    pub fn cra_failed(&self) -> u32 {
        self.0.cra_failed
    }
    /// Evaluation points the level below could not answer for.
    #[must_use]
    pub fn rec_inner_declined(&self) -> u32 {
        self.0.rec_inner_declined
    }
    /// Levels that ran out of evaluation-point budget.
    #[must_use]
    pub fn rec_budget_exhausted(&self) -> u32 {
        self.0.rec_budget_exhausted
    }
    /// Base-case Euclid refusals.
    #[must_use]
    pub fn rec_base_failed(&self) -> u32 {
        self.0.rec_base_failed
    }
    /// Content / primitive-part refusals inside the recursion.
    #[must_use]
    pub fn rec_content_failed(&self) -> u32 {
        self.0.rec_content_failed
    }
    /// Leading-coefficient GCD refusals inside the recursion.
    #[must_use]
    pub fn rec_lcgcd_failed(&self) -> u32 {
        self.0.rec_lcgcd_failed
    }
    /// Points where the `lc_H == lc_g` gate had not stabilized yet.
    #[must_use]
    pub fn rec_lch_mismatch(&self) -> u32 {
        self.0.rec_lch_mismatch
    }
    /// Points where the trial exact division rejected the interpolant.
    #[must_use]
    pub fn rec_trialdiv_reject(&self) -> u32 {
        self.0.rec_trialdiv_reject
    }
    /// Points discarded as unlucky (image leading monomial too large).
    #[must_use]
    pub fn rec_unlucky_degree(&self) -> u32 {
        self.0.rec_unlucky_degree
    }
    /// Points discarded because the imposed leading coefficient vanished there.
    #[must_use]
    pub fn rec_point_lcg_zero(&self) -> u32 {
        self.0.rec_point_lcg_zero
    }
    /// Evaluation points consumed, across every level and prime.
    #[must_use]
    pub fn rec_points_tried(&self) -> u32 {
        self.0.rec_points_tried
    }
    /// Images that could not be made glex-monic (they were zero).
    #[must_use]
    pub fn rec_monic_failed(&self) -> u32 {
        self.0.rec_monic_failed
    }
    /// Levels that used up every point of the field.
    #[must_use]
    pub fn rec_field_exhausted(&self) -> u32 {
        self.0.rec_field_exhausted
    }
    /// Newton steps that could not be extended.
    #[must_use]
    pub fn rec_newton_failed(&self) -> u32 {
        self.0.rec_newton_failed
    }
    /// Times the accumulated Newton form was discarded for a smaller image.
    #[must_use]
    pub fn rec_reset_smaller(&self) -> u32 {
        self.0.rec_reset_smaller
    }
    /// Largest number of interpolation points accumulated at one level.
    #[must_use]
    pub fn rec_max_points_at_level(&self) -> u32 {
        self.0.rec_max_points_at_level
    }
    /// Largest degree bound any level interpolated against.
    #[must_use]
    pub fn rec_max_deg_bound(&self) -> u32 {
        self.0.rec_max_deg_bound
    }
}

/// The result of a pseudo-division: `lc(q, x)^d * p == quot * q + rem`.
pub struct OPseudoDiv {
    /// The power of `lc(q, x)` carried by the identity.
    pub d: u32,
    /// The pseudo-quotient.
    pub quot: OMgrPoly,
    /// The pseudo-remainder.
    pub rem: OMgrPoly,
}

impl Default for OPolyMgr {
    fn default() -> Self {
        Self::new()
    }
}

impl OPolyMgr {
    /// A fresh manager.
    #[must_use]
    pub fn new() -> Self {
        Self(polymanager::PolyManager::new())
    }

    /// Build a polynomial from `(variable/exponent pairs, coefficient)` terms.
    pub fn mk(&mut self, terms: &[(Vec<(u32, u32)>, BigInt)]) -> OMgrPoly {
        OMgrPoly(self.0.mk_from_pairs(terms))
    }

    /// A constant polynomial.
    #[must_use]
    pub fn constant(&self, c: BigInt) -> OMgrPoly {
        OMgrPoly(self.0.mk_const(c))
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero(&self) -> OMgrPoly {
        OMgrPoly(self.0.zero())
    }

    /// Is this the zero polynomial?
    #[must_use]
    pub fn is_zero(&self, p: &OMgrPoly) -> bool {
        p.0.is_zero()
    }

    /// Is this polynomial free of variables?
    #[must_use]
    pub fn is_const(&self, p: &OMgrPoly) -> bool {
        self.0.is_const(&p.0)
    }

    /// Number of non-zero terms.
    #[must_use]
    pub fn len(&self, p: &OMgrPoly) -> usize {
        p.0.len()
    }

    /// Whether the polynomial has no terms at all.
    #[must_use]
    pub fn is_empty(&self, p: &OMgrPoly) -> bool {
        p.0.len() == 0
    }

    /// `deg_x(p)`.
    #[must_use]
    pub fn degree(&self, p: &OMgrPoly, x: u32) -> u32 {
        self.0.degree(&p.0, x)
    }

    /// Total degree.
    #[must_use]
    pub fn total_degree(&self, p: &OMgrPoly) -> u32 {
        self.0.total_degree(&p.0)
    }

    /// The variables occurring in `p`, ascending.
    #[must_use]
    pub fn vars(&self, p: &OMgrPoly) -> Vec<u32> {
        self.0.vars(&p.0)
    }

    /// The largest variable, or `None` for a constant.
    #[must_use]
    pub fn max_var(&self, p: &OMgrPoly) -> Option<u32> {
        self.0.max_var(&p.0)
    }

    /// Widest coefficient, in bits. Measurement only.
    #[must_use]
    pub fn max_coeff_bits(&self, p: &OMgrPoly) -> u64 {
        self.0.max_coeff_bits(&p.0)
    }

    /// How many distinct monomials the manager has interned. Measurement only.
    #[must_use]
    pub fn interned(&self) -> usize {
        self.0.interned()
    }

    /// The canonical term list as `(exponent pairs, coefficient)`, descending
    /// under the manager's monomial order. This is the ONLY way the oracle can
    /// see inside a `Poly`, and it is how the canonical-form invariants are
    /// checked from outside.
    #[must_use]
    pub fn terms(&self, p: &OMgrPoly) -> Vec<(Vec<(u32, u32)>, BigInt)> {
        p.0.terms()
            .iter()
            .map(|&(m, ref c)| (self.0.mono_pows(m).to_vec(), c.clone()))
            .collect()
    }

    /// Sum.
    #[must_use]
    pub fn add(&self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.add(&a.0, &b.0))
    }

    /// Difference.
    #[must_use]
    pub fn sub(&self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.sub(&a.0, &b.0))
    }

    /// Additive inverse.
    #[must_use]
    pub fn neg(&self, a: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.neg(&a.0))
    }

    /// Product.
    pub fn mul(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.mul(&a.0, &b.0))
    }

    /// `a^k`.
    pub fn pow(&mut self, a: &OMgrPoly, k: u32) -> OMgrPoly {
        OMgrPoly(self.0.pow(&a.0, k))
    }

    /// Multiply by an integer.
    #[must_use]
    pub fn mul_int(&self, a: &OMgrPoly, c: &BigInt) -> OMgrPoly {
        OMgrPoly(self.0.mul_int(&a.0, c))
    }

    /// `dp/dx`.
    pub fn derivative(&mut self, p: &OMgrPoly, x: u32) -> OMgrPoly {
        OMgrPoly(self.0.derivative(&p.0, x))
    }

    /// Substitute an integer for `x`.
    pub fn eval_var(&mut self, p: &OMgrPoly, x: u32, a: &BigInt) -> OMgrPoly {
        OMgrPoly(self.0.eval_var(&p.0, x, a))
    }

    /// The coefficient of `x^k`.
    pub fn coeff(&mut self, p: &OMgrPoly, x: u32, k: u32) -> OMgrPoly {
        OMgrPoly(self.0.coeff(&p.0, x, k))
    }

    /// The recursive view in `x`.
    pub fn x_coeffs(&mut self, p: &OMgrPoly, x: u32) -> Vec<OMgrPoly> {
        self.0.x_coeffs(&p.0, x).into_iter().map(OMgrPoly).collect()
    }

    /// Rebuild from a recursive view in `x`.
    pub fn from_x_coeffs(&mut self, x: u32, cs: &[OMgrPoly]) -> OMgrPoly {
        let raw: Vec<polymanager::Poly> = cs.iter().map(|c| c.0.clone()).collect();
        OMgrPoly(self.0.from_x_coeffs(x, &raw))
    }

    /// `lc(p, x)`.
    pub fn lc(&mut self, p: &OMgrPoly, x: u32) -> OMgrPoly {
        OMgrPoly(self.0.lc(&p.0, x))
    }

    /// Exact division, `None` when it does not divide.
    pub fn exact_div(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.exact_div(&a.0, &b.0).map(OMgrPoly)
    }

    /// Whether `b` divides `a`.
    pub fn divides(&mut self, b: &OMgrPoly, a: &OMgrPoly) -> bool {
        self.0.divides(&b.0, &a.0)
    }

    /// Pseudo-division. `exact` selects z3's `Exact_d` mode.
    pub fn pseudo_division(
        &mut self,
        p: &OMgrPoly,
        q: &OMgrPoly,
        x: u32,
        exact: bool,
    ) -> Option<OPseudoDiv> {
        let mode = if exact {
            polymanager::PseudoMode::Exact
        } else {
            polymanager::PseudoMode::Loose
        };
        self.0
            .pseudo_division(&p.0, &q.0, x, mode)
            .map(|r| OPseudoDiv {
                d: r.d,
                quot: OMgrPoly(r.quot),
                rem: OMgrPoly(r.rem),
            })
    }

    /// The integer content / content / primitive-part split with respect to
    /// `x`, as `(i, c, pp)` with `p == i * c * pp`.
    pub fn iccp(&mut self, p: &OMgrPoly, x: u32) -> Option<(BigInt, OMgrPoly, OMgrPoly)> {
        self.0
            .iccp(&p.0, x)
            .map(|r| (r.i, OMgrPoly(r.c), OMgrPoly(r.pp)))
    }

    /// The PRS GCD.
    /// The subresultant PRS answer with the modular fast path disabled all the
    /// way down. Every check that treats the PRS as an INDEPENDENT second
    /// opinion on `mod_gcd`, and every cost measurement reporting a PRS column,
    /// must use this rather than [`OPolyMgr::gcd`].
    pub fn gcd_via_prs(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.gcd_via_prs(&a.0, &b.0).map(OMgrPoly)
    }

    pub fn gcd(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.gcd(&a.0, &b.0).map(OMgrPoly)
    }

    /// The modular (Brown) GCD; `None` when it could not certify a candidate.
    pub fn mod_gcd(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.mod_gcd(&a.0, &b.0).map(OMgrPoly)
    }

    /// The modular GCD together with the DECLINE DIAGNOSIS of that call.
    ///
    /// The counters are written by `mod_gcd` and never read by it, so calling
    /// this instead of [`OPolyMgr::mod_gcd`] cannot change the answer — an
    /// invariant the `pm-mod-gcd-diag` oracle check asserts on every case.
    pub fn mod_gcd_diag(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> (Option<OMgrPoly>, OModGcdDiag) {
        let r = self.0.mod_gcd(&a.0, &b.0).map(OMgrPoly);
        (r, OModGcdDiag(self.0.mod_gcd_diag()))
    }

    /// The square-free part with respect to `x`.
    pub fn square_free_in(&mut self, p: &OMgrPoly, x: u32) -> Option<OMgrPoly> {
        self.0.square_free_in(&p.0, x).map(OMgrPoly)
    }

    /// The whole-polynomial square-free part.
    pub fn square_free(&mut self, p: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.square_free(&p.0).map(OMgrPoly)
    }

    /// Whether `p` is already square-free with respect to `x`.
    pub fn is_square_free_in(&mut self, p: &OMgrPoly, x: u32) -> Option<bool> {
        self.0.is_square_free_in(&p.0, x)
    }

    /// The positive GCD of the coefficients (`0` for the zero polynomial).
    ///
    /// Exposed for the one invariant that pins the SCALAR half of
    /// `square_free`: a dropped integer content is invisible to divisibility,
    /// to root sets and to square-freeness, and was found live by a verifier.
    #[must_use]
    pub fn int_content(&self, p: &OMgrPoly) -> BigInt {
        self.0.int_content(&p.0)
    }

    /// Specialize every variable except `x` to the given integers and read the
    /// result out as a DENSE low-to-high coefficient list in `x`.
    ///
    /// `None` when the specialization leaves a variable other than `x`
    /// standing, which would make the univariate reading a lie. This is the
    /// bridge every z3-backed check crosses: it turns a multivariate answer
    /// into something z3's univariate `Z3_algebraic_*` API can be asked about.
    pub fn specialize(
        &mut self,
        p: &OMgrPoly,
        x: u32,
        point: &[(u32, BigInt)],
    ) -> Option<Vec<BigInt>> {
        let mut cur = p.0.clone();
        for (v, val) in point {
            if *v == x {
                continue;
            }
            cur = self.0.eval_var(&cur, *v, val);
        }
        for v in self.0.vars(&cur) {
            if v != x {
                return None;
            }
        }
        if cur.is_zero() {
            return Some(Vec::new());
        }
        let d = self.0.degree(&cur, x);
        let mut out = vec![BigInt::from(0); d as usize + 1];
        for cs in self.0.x_coeffs(&cur, x).iter().enumerate() {
            let (k, c) = cs;
            match self.0.const_value(c) {
                Some(v) => out[k] = v,
                None => return None,
            }
        }
        while out.last().is_some_and(num_traits::Zero::is_zero) {
            out.pop();
        }
        Some(out)
    }
}

// ---------------------------------------------------------------------------
// `upoly`: dense univariate over Z and Z_p, and Z_p factorization
// ---------------------------------------------------------------------------

/// Dense univariate polynomial over `Z`, low-to-high coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OUniZ(upoly::ZPoly);

impl OUniZ {
    /// Build from low-to-high integer coefficients (trailing zeros trimmed).
    #[must_use]
    pub fn from_coeffs(c: Vec<BigInt>) -> Self {
        Self(upoly::ZPoly::from_coeffs(c))
    }

    /// Low-to-high coefficients (empty for the zero polynomial).
    #[must_use]
    pub fn coeffs(&self) -> Vec<BigInt> {
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

    /// Leading coefficient, or `None` for the zero polynomial.
    #[must_use]
    pub fn lc(&self) -> Option<BigInt> {
        self.0.lc().cloned()
    }

    /// Sum.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0.add(&other.0))
    }

    /// Difference.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self(self.0.sub(&other.0))
    }

    /// Product.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        Self(self.0.mul(&other.0))
    }

    /// Negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self(self.0.neg())
    }

    /// Scale by an integer.
    #[must_use]
    pub fn scale(&self, s: &BigInt) -> Self {
        Self(self.0.scale(s))
    }

    /// Formal derivative.
    #[must_use]
    pub fn derivative(&self) -> Self {
        Self(self.0.derivative())
    }

    /// Exact evaluation at an integer point.
    #[must_use]
    pub fn eval(&self, at: &BigInt) -> BigInt {
        self.0.eval(at)
    }

    /// Non-negative GCD of the coefficients; zero for the zero polynomial.
    #[must_use]
    pub fn content(&self) -> BigInt {
        self.0.content()
    }

    /// `(c, pp)` with `self == c * pp`, `pp` primitive with positive `lc`.
    #[must_use]
    pub fn split_content(&self) -> Option<(BigInt, Self)> {
        self.0.split_content().map(|(c, p)| (c, Self(p)))
    }

    /// Exact division in `Z[x]`; `None` when it does not divide exactly.
    #[must_use]
    pub fn exact_div(&self, den: &Self) -> Option<Self> {
        self.0.exact_div(&den.0).map(Self)
    }

    /// Pseudo-division: `(d, q, r)` with `lc(den)^d * self == q*den + r`.
    #[must_use]
    pub fn pseudo_div(&self, den: &Self) -> Option<(usize, Self, Self)> {
        self.0
            .pseudo_div(&den.0)
            .map(|pd| (pd.d, Self(pd.q), Self(pd.r)))
    }

    /// Subresultant-PRS GCD over `Z`, positive leading coefficient.
    #[must_use]
    pub fn gcd(&self, other: &Self) -> Option<Self> {
        self.0.gcd(&other.0).map(Self)
    }

    /// Yun's square-free decomposition: `(c, [(f_i, i)])` with
    /// `self == c * prod f_i^i`.
    #[must_use]
    pub fn square_free_decomposition(&self) -> Option<(BigInt, Vec<(Self, usize)>)> {
        self.0.square_free_decomposition().map(|d| {
            (
                d.c,
                d.factors.into_iter().map(|(f, m)| (Self(f), m)).collect(),
            )
        })
    }
}

/// Dense univariate polynomial over `Z_p`, low-to-high coefficients in `[0,p)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OUniZp(upoly::ZpPoly);

impl OUniZp {
    /// Low-to-high coefficients in `[0, p)` (empty for zero).
    #[must_use]
    pub fn coeffs(&self) -> Vec<u64> {
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

    /// Leading coefficient, or `None` for the zero polynomial.
    #[must_use]
    pub fn lc(&self) -> Option<u64> {
        self.0.lc()
    }
}

/// Work counters for one factorization, as `upoly` records them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OFactorStats {
    /// Iterations of the distinct-degree loop.
    pub ddf_iters: u64,
    /// Random polynomials drawn by equal-degree factorization.
    pub edf_attempts: u64,
    /// Successful splits performed by equal-degree factorization.
    pub edf_splits: u64,
    /// Calls to `x^e mod f`.
    pub powmods: u64,
    /// Polynomial multiplications performed inside `powmod`.
    pub powmod_mults: u64,
}

/// Arithmetic in `Z_p[x]` for a fixed prime `p`.
pub struct OZpMgr(upoly::Zp);

impl OZpMgr {
    /// `None` if `p` is not a prime below `2^31`.
    #[must_use]
    pub fn new(p: u64) -> Option<Self> {
        upoly::Zp::new(p).map(Self)
    }

    /// The modulus.
    #[must_use]
    pub fn p(&self) -> u64 {
        self.0.p()
    }

    /// Work counters accumulated since the last reset.
    #[must_use]
    pub fn stats(&self) -> OFactorStats {
        let s = self.0.stats();
        OFactorStats {
            ddf_iters: s.ddf_iters,
            edf_attempts: s.edf_attempts,
            edf_splits: s.edf_splits,
            powmods: s.powmods,
            powmod_mults: s.powmod_mults,
        }
    }

    /// Zero the work counters.
    pub fn reset_stats(&self) {
        self.0.reset_stats();
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero(&self) -> OUniZp {
        OUniZp(self.0.zero())
    }

    /// The constant `1`.
    #[must_use]
    pub fn one(&self) -> OUniZp {
        OUniZp(self.0.one())
    }

    /// Build from low-to-high coefficients, reduced mod `p`.
    #[must_use]
    pub fn from_u64(&self, c: Vec<u64>) -> OUniZp {
        OUniZp(self.0.from_u64(c))
    }

    /// Reduce a `Z` polynomial mod `p`; the degree drops when `p | lc`.
    #[must_use]
    pub fn reduce(&self, f: &OUniZ) -> OUniZp {
        OUniZp(self.0.reduce(&f.0))
    }

    /// Lift to `Z` with coefficients in `[0, p)`.
    #[must_use]
    pub fn lift(&self, f: &OUniZp) -> OUniZ {
        OUniZ(self.0.lift(&f.0))
    }

    /// Sum in `Z_p[x]`.
    #[must_use]
    pub fn add(&self, a: &OUniZp, b: &OUniZp) -> OUniZp {
        OUniZp(self.0.add(&a.0, &b.0))
    }

    /// Difference in `Z_p[x]`.
    #[must_use]
    pub fn sub(&self, a: &OUniZp, b: &OUniZp) -> OUniZp {
        OUniZp(self.0.sub(&a.0, &b.0))
    }

    /// Product in `Z_p[x]`.
    #[must_use]
    pub fn mul(&self, a: &OUniZp, b: &OUniZp) -> OUniZp {
        OUniZp(self.0.mul(&a.0, &b.0))
    }

    /// Scale by a scalar in `Z_p`.
    #[must_use]
    pub fn scale(&self, a: &OUniZp, s: u64) -> OUniZp {
        OUniZp(self.0.scale(&a.0, s))
    }

    /// Formal derivative in `Z_p[x]`.
    #[must_use]
    pub fn derivative(&self, a: &OUniZp) -> OUniZp {
        OUniZp(self.0.derivative(&a.0))
    }

    /// Modular inverse; `None` exactly when `p | a`.
    #[must_use]
    pub fn inv_s(&self, a: u64) -> Option<u64> {
        self.0.inv_s(a)
    }

    /// `(q, r)` with `a == q*b + r`, `deg r < deg b`; `None` when `b` is zero.
    #[must_use]
    pub fn div_rem(&self, a: &OUniZp, b: &OUniZp) -> Option<(OUniZp, OUniZp)> {
        self.0
            .div_rem(&a.0, &b.0)
            .map(|(q, r)| (OUniZp(q), OUniZp(r)))
    }

    /// Exact division; `None` when the remainder is non-zero.
    #[must_use]
    pub fn exact_div(&self, a: &OUniZp, b: &OUniZp) -> Option<OUniZp> {
        self.0.exact_div(&a.0, &b.0).map(OUniZp)
    }

    /// `(lc, monic)` with `a == lc * monic`.
    #[must_use]
    pub fn monic(&self, a: &OUniZp) -> Option<(u64, OUniZp)> {
        self.0.monic(&a.0).map(|(l, m)| (l, OUniZp(m)))
    }

    /// Monic GCD in `Z_p[x]`.
    #[must_use]
    pub fn gcd(&self, a: &OUniZp, b: &OUniZp) -> OUniZp {
        OUniZp(self.0.gcd(&a.0, &b.0))
    }

    /// `base^e mod m`.
    #[must_use]
    pub fn powmod(&self, base: &OUniZp, e: &BigInt, m: &OUniZp) -> Option<OUniZp> {
        self.0.powmod(&base.0, e, &m.0).map(OUniZp)
    }

    /// The `p`-th root; `None` if the input is not a `p`-th power.
    #[must_use]
    pub fn p_th_root(&self, a: &OUniZp) -> Option<OUniZp> {
        self.0.p_th_root(&a.0).map(OUniZp)
    }

    /// Square-free decomposition of a monic polynomial: `a == prod g_i^{m_i}`.
    #[must_use]
    pub fn square_free_decomposition(&self, a: &OUniZp) -> Option<Vec<(OUniZp, usize)>> {
        self.0
            .square_free_decomposition(&a.0)
            .map(|v| v.into_iter().map(|(g, m)| (OUniZp(g), m)).collect())
    }

    /// Distinct-degree factorization of a monic SQUARE-FREE polynomial.
    #[must_use]
    pub fn distinct_degree(&self, a: &OUniZp) -> Option<Vec<(OUniZp, usize)>> {
        self.0
            .distinct_degree(&a.0)
            .map(|v| v.into_iter().map(|(g, d)| (OUniZp(g), d)).collect())
    }

    /// Equal-degree (Cantor-Zassenhaus) split into degree-`d` irreducibles.
    #[must_use]
    pub fn equal_degree(&self, a: &OUniZp, d: usize) -> Option<Vec<OUniZp>> {
        self.0
            .equal_degree(&a.0, d)
            .map(|v| v.into_iter().map(OUniZp).collect())
    }

    /// Complete factorization: `(lc, [(f_i, e_i)])` with
    /// `a == lc * prod f_i^{e_i}`, every `f_i` monic irreducible.
    #[must_use]
    pub fn factor(&self, a: &OUniZp) -> Option<(u64, Vec<(OUniZp, usize)>)> {
        self.0.factor(&a.0).map(|f| {
            (
                f.lc,
                f.factors.into_iter().map(|(g, e)| (OUniZp(g), e)).collect(),
            )
        })
    }

    /// Rabin's irreducibility test — independent of the factorizer's control
    /// flow.
    #[must_use]
    pub fn is_irreducible(&self, a: &OUniZp) -> Option<bool> {
        self.0.is_irreducible(&a.0)
    }
}

// ============================================================================
// `mpbq` — binary rationals (dyadics) and the interval machinery on them
// ============================================================================

/// A binary rational `a / 2^k`, in canonical form (`k == 0` or `a` odd).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OBq(mpbq::Bq);

impl OBq {
    /// The exact value `a / 2^k`, normalized.
    #[must_use]
    pub fn new(a: BigInt, k: u32) -> Self {
        Self(mpbq::Bq::new(a, k))
    }

    /// The integer `n`.
    #[must_use]
    pub fn from_int(n: BigInt) -> Self {
        Self(mpbq::Bq::from_int(n))
    }

    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Self(mpbq::Bq::zero())
    }

    /// `2^(-k)`.
    #[must_use]
    pub fn inv_two_pow(k: u32) -> Self {
        Self(mpbq::Bq::inv_two_pow(k))
    }

    /// The canonical numerator.
    #[must_use]
    pub fn numerator(&self) -> BigInt {
        self.0.numerator().clone()
    }

    /// The canonical denominator exponent.
    #[must_use]
    pub fn k(&self) -> u32 {
        self.0.k()
    }

    /// Bit length of the canonical numerator.
    #[must_use]
    pub fn numerator_bits(&self) -> u64 {
        self.0.numerator_bits()
    }

    /// `-1`, `0` or `1`.
    #[must_use]
    pub fn sign(&self) -> i32 {
        self.0.sign()
    }

    /// Whether the value is an integer.
    #[must_use]
    pub fn is_int(&self) -> bool {
        self.0.is_int()
    }

    /// Negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self(self.0.neg())
    }

    /// Absolute value.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }

    /// Exact addition.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0.add(&other.0))
    }

    /// Exact subtraction.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self(self.0.sub(&other.0))
    }

    /// Exact multiplication.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Self> {
        self.0.mul(&other.0).map(Self)
    }

    /// `self * 2^e`.
    #[must_use]
    pub fn mul_two_pow(&self, e: u32) -> Self {
        Self(self.0.mul_two_pow(e))
    }

    /// `self / 2^e`.
    #[must_use]
    pub fn div_two_pow(&self, e: u32) -> Option<Self> {
        self.0.div_two_pow(e).map(Self)
    }

    /// Exact comparison.
    #[must_use]
    pub fn cmp_bq(&self, other: &Self) -> Ordering {
        self.0.cmp_bq(&other.0)
    }

    /// `floor(self)`.
    #[must_use]
    pub fn floor(&self) -> BigInt {
        self.0.floor()
    }

    /// `ceil(self)`.
    #[must_use]
    pub fn ceil(&self) -> BigInt {
        self.0.ceil()
    }

    /// `floor(self * 2^target)`.
    #[must_use]
    pub fn floor_at(&self, target: u32) -> BigInt {
        self.0.floor_at(target)
    }

    /// `ceil(self * 2^target)`.
    #[must_use]
    pub fn ceil_at(&self, target: u32) -> BigInt {
        self.0.ceil_at(target)
    }

    /// The exact rational this dyadic denotes.
    #[must_use]
    pub fn to_rational(&self) -> BigRational {
        self.0.to_rational()
    }

    /// The dyadic equal to `r`, or `None` when `r` is not exactly representable.
    #[must_use]
    pub fn from_rational(r: &BigRational) -> Option<Self> {
        mpbq::Bq::from_rational(r).map(Self)
    }

    /// Whether `r` is exactly representable as a dyadic.
    #[must_use]
    pub fn is_representable(r: &BigRational) -> bool {
        mpbq::Bq::is_representable(r)
    }
}

/// A non-empty open interval with dyadic endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OBqInterval(mpbq::BqInterval);

impl OBqInterval {
    /// Build `(lo, hi)`, or `None` when `lo >= hi`.
    #[must_use]
    pub fn new(lo: &OBq, hi: &OBq) -> Option<Self> {
        mpbq::BqInterval::new(lo.0.clone(), hi.0.clone()).map(Self)
    }

    /// Lower endpoint.
    #[must_use]
    pub fn lo(&self) -> OBq {
        OBq(self.0.lo().clone())
    }

    /// Upper endpoint.
    #[must_use]
    pub fn hi(&self) -> OBq {
        OBq(self.0.hi().clone())
    }

    /// `hi - lo`.
    #[must_use]
    pub fn width(&self) -> OBq {
        OBq(self.0.width())
    }

    /// The exact midpoint.
    #[must_use]
    pub fn midpoint(&self) -> Option<OBq> {
        self.0.midpoint().map(OBq)
    }

    /// Split at the midpoint: `(left, mid, right)`.
    #[must_use]
    pub fn bisect(&self) -> Option<(Self, OBq, Self)> {
        self.0.bisect().map(|(l, m, r)| (Self(l), OBq(m), Self(r)))
    }

    /// `lo < x < hi`.
    #[must_use]
    pub fn contains_open(&self, x: &OBq) -> bool {
        self.0.contains_open(&x.0)
    }

    /// The two open intervals share no point.
    #[must_use]
    pub fn disjoint(&self, other: &Self) -> bool {
        self.0.disjoint(&other.0)
    }

    /// The larger of the two endpoint precisions.
    #[must_use]
    pub fn max_k(&self) -> u32 {
        self.0.max_k()
    }
}

/// Exact sign of an integer polynomial (low-to-high) at a dyadic point.
#[must_use]
pub fn obq_poly_sign_at(p: &[BigInt], x: &OBq) -> Option<i32> {
    mpbq::poly_sign_at(p, &x.0)
}

/// Exact value of an integer polynomial at a dyadic point.
#[must_use]
pub fn obq_poly_eval_at(p: &[BigInt], x: &OBq) -> Option<OBq> {
    mpbq::poly_eval_at(p, &x.0).map(OBq)
}

/// The derived liveness bound for [`obq_refine_to_width`].
#[must_use]
pub fn obq_refine_step_bound(width: &OBq, target: &OBq) -> Option<u32> {
    mpbq::refine_step_bound(&width.0, &target.0)
}

/// What one refinement produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ORefined {
    /// The root is exactly this dyadic.
    Exact(OBq),
    /// A narrower isolating interval.
    Narrowed(OBqInterval),
}

/// The refinement's own account: steps taken, the derived bound, and the
/// precision of the answer (derived from the answer, not stored by the loop).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ORefineTrace {
    /// Bisections actually performed.
    pub steps: u32,
    /// The derived upper bound on `steps`.
    pub bound: u32,
    /// `max_k` of the returned interval.
    pub end_max_k: u32,
}

/// Narrow an isolating interval until its width is at most `target`.
#[must_use]
pub fn obq_refine_to_width(
    p: &[BigInt],
    iv: &OBqInterval,
    target: &OBq,
) -> Option<(ORefined, ORefineTrace)> {
    let (r, t) = mpbq::refine_to_width(p, &iv.0, &target.0)?;
    let r = match r {
        mpbq::Refined::Exact(v) => ORefined::Exact(OBq(v)),
        mpbq::Refined::Narrowed(iv) => ORefined::Narrowed(OBqInterval(iv)),
    };
    Some((
        r,
        ORefineTrace {
            steps: t.steps,
            bound: t.bound,
            end_max_k: t.end_max_k,
        },
    ))
}

/// How two isolated roots compare once separated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OSeparation {
    /// Disjoint intervals; this is the exact order.
    Ordered(Ordering),
    /// The budget ran out with the intervals still overlapping.
    Inconclusive,
}

/// Refine two isolating intervals in lockstep until they are disjoint.
#[must_use]
pub fn obq_refine_until_separated(
    p: &[BigInt],
    a: &OBqInterval,
    q: &[BigInt],
    b: &OBqInterval,
    max_rounds: u32,
) -> Option<(OSeparation, OBqInterval, OBqInterval, u32)> {
    let (s, ia, ib, n) = mpbq::refine_until_separated(p, &a.0, q, &b.0, max_rounds)?;
    let s = match s {
        mpbq::Separation::Ordered(o) => OSeparation::Ordered(o),
        mpbq::Separation::Inconclusive => OSeparation::Inconclusive,
    };
    Some((s, OBqInterval(ia), OBqInterval(ib), n))
}

/// An integer strictly inside `(lo, hi)`, closest to zero.
#[must_use]
pub fn obq_select_int(lo: &OBq, hi: &OBq) -> Option<BigInt> {
    mpbq::select_int(&lo.0, &hi.0)
}

/// The simplest dyadic strictly inside the interval, with its derived ceiling.
#[must_use]
pub fn obq_select_small(iv: &OBqInterval) -> Option<(OBq, u32)> {
    mpbq::select_small(&iv.0).map(|s| (OBq(s.value), s.k_ceiling))
}

/// The candidate numerator at precision `k`, or `None` when the scaled interval
/// contains no integer strictly inside.
///
/// This is the NEGATIVE half of `select_small`'s minimality certificate: for an
/// answer at exponent `k > 0`, this must be `None` at `k - 1`.
#[must_use]
pub fn obq_candidate_at(iv: &OBqInterval, k: u32) -> Option<BigInt> {
    mpbq::candidate_at(&iv.0, k)
}

/// A simple dyadic strictly inside the interval that is not a root of `p`.
#[must_use]
pub fn obq_select_non_root(p: &[BigInt], iv: &OBqInterval) -> Option<OBq> {
    mpbq::select_non_root(p, &iv.0).map(OBq)
}

/// The smallest `2^-k`-grid interval containing `(lo, hi)`.
#[must_use]
pub fn obq_enclose_rational(lo: &BigRational, hi: &BigRational, k: u32) -> Option<OBqInterval> {
    mpbq::enclose_rational(lo, hi, k).map(OBqInterval)
}
// ============================================================================
// `anum` — real algebraic numbers over dyadic isolating intervals
// ============================================================================

/// What a sign or comparison call did, for the oracle to pin the counters from.
///
/// `sep_bits` and `bound` are pure functions of the inputs and the oracle
/// recomputes both; `steps_*` are real counters pinned by the exact halving
/// identity; `equal_by_certificate` is pinned by `steps == 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OAnumTrace {
    /// Derived root-separation exponent, when refinement was needed.
    pub sep_bits: Option<u32>,
    /// Bisections on the first operand.
    pub steps_a: u32,
    /// Bisections on the second operand.
    pub steps_b: u32,
    /// Derived liveness bound.
    pub bound: u32,
    /// Answered by the gcd/Sturm equality certificate, with no refinement.
    pub equal_by_certificate: bool,
}

impl From<anum::AnumTrace> for OAnumTrace {
    fn from(t: anum::AnumTrace) -> Self {
        Self {
            sep_bits: t.sep_bits,
            steps_a: t.steps_a,
            steps_b: t.steps_b,
            bound: t.bound,
            equal_by_certificate: t.equal_by_certificate,
        }
    }
}

/// A real algebraic number over a DYADIC isolating interval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ODyadicAnum(anum::Anum);

impl ODyadicAnum {
    /// The unique root of `coeffs` inside `iv`, or `None` when `iv` does not
    /// isolate exactly one real root. This refusal is the check's whole point.
    #[must_use]
    pub fn from_poly_interval(coeffs: &[BigInt], iv: &OBqInterval) -> Option<Self> {
        anum::Anum::from_poly_interval(coeffs, &iv.0).map(Self)
    }

    /// The exact rational `r` as an algebraic number.
    #[must_use]
    pub fn rational(r: BigRational) -> Self {
        Self(anum::Anum::rational(r))
    }

    /// Is this the rational case?
    #[must_use]
    pub fn is_rational(&self) -> bool {
        self.0.is_rational()
    }

    /// The exact rational value, when there is one.
    #[must_use]
    pub fn to_rational(&self) -> Option<BigRational> {
        self.0.to_rational().cloned()
    }

    /// Degree of the defining polynomial (`1` for a rational).
    #[must_use]
    pub fn degree(&self) -> usize {
        self.0.degree()
    }

    /// The defining polynomial, low-to-high, for the algebraic case.
    #[must_use]
    pub fn poly_coeffs(&self) -> Option<Vec<BigInt>> {
        self.0.cell().map(|c| c.poly_coeffs().to_vec())
    }

    /// The dyadic isolating interval, for the algebraic case.
    #[must_use]
    pub fn interval(&self) -> Option<OBqInterval> {
        self.0.cell().map(|c| OBqInterval(c.interval().clone()))
    }

    /// The 1-based index among the ascending real roots of the defining
    /// polynomial. DERIVED on every call; never a stored field.
    #[must_use]
    pub fn root_index(&self) -> Option<usize> {
        self.0.cell().and_then(anum::AlgCell::root_index)
    }

    /// Narrow the isolating interval to at most `target`, preserving the
    /// invariant.
    #[must_use]
    pub fn refine(&self, target: &OBq) -> Option<Self> {
        self.0.refine(&target.0).map(Self)
    }

    /// Exact sign of the integer polynomial `q` at this number.
    #[must_use]
    pub fn sign_of_poly(&self, q: &[BigInt]) -> Option<i32> {
        self.0.sign_of_poly(q)
    }

    /// [`ODyadicAnum::sign_of_poly`] with the trace.
    #[must_use]
    pub fn sign_of_poly_traced(&self, q: &[BigInt]) -> Option<(i32, OAnumTrace)> {
        self.0.sign_of_poly_traced(q).map(|(s, t)| (s, t.into()))
    }

    /// Exact comparison.
    #[must_use]
    pub fn cmp_anum(&self, other: &Self) -> Option<Ordering> {
        self.0.cmp_anum(&other.0)
    }

    /// [`ODyadicAnum::cmp_anum`] with the trace.
    #[must_use]
    pub fn cmp_anum_traced(&self, other: &Self) -> Option<(Ordering, OAnumTrace)> {
        self.0.cmp_anum_traced(&other.0).map(|(o, t)| (o, t.into()))
    }

    /// Exact sum.
    #[must_use]
    pub fn add(&self, other: &Self) -> Option<Self> {
        self.0.add(&other.0).map(Self)
    }

    /// Exact product.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Self> {
        self.0.mul(&other.0).map(Self)
    }

    /// Exact negation.
    #[must_use]
    pub fn neg(&self) -> Option<Self> {
        self.0.neg().map(Self)
    }
}

/// The DERIVED root-separation exponent `B`: any two distinct real roots of the
/// square-free integer polynomial `coeffs` differ by more than `2^-B`.
///
/// Exposed as a **pure function**, deliberately. The campaign's fifth blind-spot
/// pattern is a pure function only ever tested through its consumer, where a
/// wrong branch can be structurally unreachable; this is the entry point the
/// oracle calls directly, on arbitrary inputs, and validates against z3's own
/// root list BEFORE any consumer runs.
#[must_use]
pub fn anum_root_separation_exponent(coeffs: &[BigInt]) -> Option<u32> {
    anum::root_separation_exponent(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
}

/// Distinct real roots of `coeffs` strictly inside `(lo, hi)`, by the
/// fraction-free Sturm chain over `Z`. `None` when an endpoint is a root — the
/// guard, exposed so it can be fired on purpose.
#[must_use]
pub fn anum_sturm_count_in(coeffs: &[BigInt], lo: &OBq, hi: &OBq) -> Option<usize> {
    let p = upoly::ZPoly::from_coeffs(coeffs.to_vec());
    let chain = anum::sturm_chain(&p)?;
    anum::sturm_count_in(&chain, &lo.0, &hi.0)
}

/// The square-free radical of `coeffs`, primitive with positive leading
/// coefficient: the defining-polynomial normal form.
#[must_use]
pub fn anum_normalize_defining(coeffs: &[BigInt]) -> Option<Vec<BigInt>> {
    anum::normalize_defining(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
        .map(|p| p.coeffs().to_vec())
}

/// The Cauchy bound: every real root of `coeffs` lies strictly inside `(-b, b)`.
#[must_use]
pub fn anum_cauchy_bound(coeffs: &[BigInt]) -> Option<BigInt> {
    anum::cauchy_bound_z(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
}

/// The ceiling on the derived separation exponent, above which the module
/// declines rather than spends.
#[must_use]
pub fn anum_max_separation_bits() -> u32 {
    anum::MAX_SEPARATION_BITS
}

/// Which path an arithmetic operation will take, and whether it can legitimately
/// decline. DIAGNOSTIC ONLY: `add` / `mul` answer identically whether or not this
/// is called.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OAnumOpDiag {
    /// No resultant is built: two rationals, or a zero operand.
    ClosedForm,
    /// The degree-preserving affine path for a dyadic rational operand.
    Affine,
    /// The resultant path, with the derived separation exponent.
    Resultant(u32),
    /// Above the declared ceiling: the ONLY legitimate decline.
    OverCeiling,
    /// Degenerate operand; the resultant cannot be built.
    Degenerate,
}

/// See [`OAnumOpDiag`]. `is_add` selects `+` over `*`.
#[must_use]
pub fn anum_binop_diag(a: &ODyadicAnum, b: &ODyadicAnum, is_add: bool) -> OAnumOpDiag {
    match anum::binop_diag(&a.0, &b.0, is_add) {
        anum::OpDiag::ClosedForm => OAnumOpDiag::ClosedForm,
        anum::OpDiag::Affine => OAnumOpDiag::Affine,
        anum::OpDiag::Resultant(b) => OAnumOpDiag::Resultant(b),
        anum::OpDiag::OverCeiling => OAnumOpDiag::OverCeiling,
        anum::OpDiag::Degenerate => OAnumOpDiag::Degenerate,
    }
}

// ============================================================================
// Interval sets over real algebraic endpoints (`crate::ialg`)
// ============================================================================

/// How simple a picked value is; see `ialg::Rung`. Ordered simplest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OIRung {
    /// An integer.
    Integer,
    /// A rational with denominator at most [`oialg_max_simple_den`].
    Simple,
    /// A dyadic that is not already `Simple`.
    Dyadic,
    /// Any other exact rational.
    Rational,
    /// A genuine algebraic number.
    Algebraic,
}

impl From<ialg::Rung> for OIRung {
    fn from(r: ialg::Rung) -> Self {
        match r {
            ialg::Rung::Integer => Self::Integer,
            ialg::Rung::Simple => Self::Simple,
            ialg::Rung::Dyadic => Self::Dyadic,
            ialg::Rung::Rational => Self::Rational,
            ialg::Rung::Algebraic => Self::Algebraic,
        }
    }
}

/// The rung a value sits on, DERIVED — never a stored tag.
///
/// Exposed as a pure function on purpose: it is the metric the `pick` ladder is
/// judged by, and if `pick` returned a stored tag instead, the oracle would be
/// reading the answer off the very thing it is checking.
///
/// It classifies the REPRESENTATION, not the abstract value: a cell whose root
/// happens to be rational still classifies `Algebraic`, because the sign
/// evaluation it will cost is the cell's. See `ialg::Rung` for the measurement.
#[must_use]
pub fn oialg_classify_value(v: &ODyadicAnum) -> OIRung {
    ialg::classify_value(&v.0).into()
}

/// The sign condition a cell must satisfy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OISignCond {
    /// `p < 0`.
    Lt,
    /// `p <= 0`.
    Le,
    /// `p = 0`.
    Eq,
    /// `p != 0`.
    Ne,
    /// `p >= 0`.
    Ge,
    /// `p > 0`.
    Gt,
}

impl OISignCond {
    fn inner(self) -> ialg::SignCond {
        match self {
            Self::Lt => ialg::SignCond::Lt,
            Self::Le => ialg::SignCond::Le,
            Self::Eq => ialg::SignCond::Eq,
            Self::Ne => ialg::SignCond::Ne,
            Self::Ge => ialg::SignCond::Ge,
            Self::Gt => ialg::SignCond::Gt,
        }
    }

    /// Does sign `s` satisfy this condition? The predicate itself, so the
    /// oracle can judge the cells without reimplementing it.
    #[must_use]
    pub fn accepts(self, s: i32) -> bool {
        self.inner().accepts(s)
    }
}

/// One interval of an [`OIAlgSet`], flattened for inspection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OIAlgInterval {
    /// Lower endpoint, `None` for `-inf`.
    pub lo: Option<ODyadicAnum>,
    /// Is the lower endpoint open?
    pub lo_open: bool,
    /// Upper endpoint, `None` for `+inf`.
    pub hi: Option<ODyadicAnum>,
    /// Is the upper endpoint open?
    pub hi_open: bool,
    /// The literals justifying this interval, ascending.
    pub lits: Vec<i32>,
}

/// A union of disjoint intervals with real algebraic endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OIAlgSet(ialg::IntervalSet);

impl OIAlgSet {
    /// The empty set — the conflict signal.
    #[must_use]
    pub fn empty() -> Self {
        Self(ialg::IntervalSet::empty())
    }

    /// The whole line, justified by `lits`.
    #[must_use]
    pub fn full(lits: &[i32]) -> Option<Self> {
        Some(Self(ialg::IntervalSet::full(just_of(lits)?)))
    }

    /// Build from flattened intervals, normalising (sort, merge, drop empty).
    ///
    /// `None` when any endpoint comparison could not be decided, when an
    /// infinite endpoint is marked closed, or when a ceiling is exceeded.
    #[must_use]
    pub fn from_parts(parts: &[OIAlgInterval]) -> Option<Self> {
        let mut ivs = Vec::with_capacity(parts.len());
        for p in parts {
            let lo = match &p.lo {
                Some(a) => ialg::AEnd::Fin(a.0.clone()),
                None => ialg::AEnd::NegInf,
            };
            let hi = match &p.hi {
                Some(a) => ialg::AEnd::Fin(a.0.clone()),
                None => ialg::AEnd::PosInf,
            };
            match ialg::AInterval::new(lo, p.lo_open, hi, p.hi_open, just_of(&p.lits)?)? {
                ialg::Made::Iv(v) => ivs.push(v),
                ialg::Made::Empty => {}
            }
        }
        ialg::IntervalSet::normalize(ivs).map(Self)
    }

    /// Is the set empty? Exact by construction — see the `ialg` header.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// How many disjoint intervals.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The intervals, ascending.
    #[must_use]
    pub fn intervals(&self) -> Vec<OIAlgInterval> {
        self.0
            .intervals()
            .iter()
            .map(|iv| OIAlgInterval {
                lo: iv.lo().value().cloned().map(ODyadicAnum),
                lo_open: iv.lo_open(),
                hi: iv.hi().value().cloned().map(ODyadicAnum),
                hi_open: iv.hi_open(),
                lits: iv.just().lits().to_vec(),
            })
            .collect()
    }

    /// Every literal responsible for the set.
    #[must_use]
    pub fn justification(&self) -> Option<Vec<i32>> {
        self.0.justification().map(|j| j.lits().to_vec())
    }

    /// Exact SET equality — same points, regardless of how the endpoints are
    /// represented or which literals justify them.
    ///
    /// The derived `PartialEq` on this type is STRUCTURAL and is NOT set
    /// equality; see `ialg::IntervalSet::same_set_as` for the two measured ways
    /// they come apart.
    #[must_use]
    pub fn same_set_as(&self, other: &Self) -> Option<bool> {
        self.0.same_set_as(&other.0)
    }

    /// Does the set contain `v`? `None` when undecided — never a guess.
    #[must_use]
    pub fn contains(&self, v: &ODyadicAnum) -> Option<bool> {
        self.0.contains(&v.0)
    }

    /// Union.
    #[must_use]
    pub fn union(&self, other: &Self) -> Option<Self> {
        self.0.union(&other.0).map(Self)
    }

    /// Intersection, keeping justifications.
    #[must_use]
    pub fn intersect(&self, other: &Self) -> Option<Self> {
        self.0.intersect(&other.0).map(Self)
    }

    /// Complement.
    #[must_use]
    pub fn complement(&self) -> Option<Self> {
        self.0.complement().map(Self)
    }

    /// `self \ other`.
    #[must_use]
    pub fn subtract(&self, other: &Self) -> Option<Self> {
        self.0.subtract(&other.0).map(Self)
    }

    /// A value in the set, as simple as the ladder can find. Every returned
    /// value has been VERIFIED to lie in the set before being returned.
    #[must_use]
    pub fn pick(&self) -> Option<ODyadicAnum> {
        self.0.pick().map(ODyadicAnum)
    }
}

fn just_of(lits: &[i32]) -> Option<ialg::Just> {
    let mut j = ialg::Just::none();
    for &l in lits {
        j = j.merge(&ialg::Just::of(l)?)?;
    }
    Some(j)
}

/// The feasible set of `p cond 0` given `p`'s real roots in ASCENDING order.
///
/// Root isolation is NOT repeated here; the roots are an argument precisely so
/// the oracle can drive this on z3's own root list rather than only through a
/// consumer.
#[must_use]
pub fn oialg_from_sign_condition(
    p: &[BigInt],
    roots: &[ODyadicAnum],
    cond: OISignCond,
    lits: &[i32],
) -> Option<OIAlgSet> {
    let rs: Vec<anum::Anum> = roots.iter().map(|r| r.0.clone()).collect();
    ialg::from_sign_condition(p, &rs, cond.inner(), just_of(lits)?).map(OIAlgSet)
}

/// The declared ceiling on intervals per set.
#[must_use]
pub fn oialg_max_intervals() -> usize {
    ialg::MAX_INTERVALS
}

/// The largest denominator the `Simple` rung will offer.
#[must_use]
pub fn oialg_max_simple_den() -> i64 {
    ialg::MAX_SIMPLE_DEN
}

/// The declared ceiling on literals per justification.
#[must_use]
pub fn oialg_max_just() -> usize {
    ialg::MAX_JUST
}

// ===========================================================================
// Conflict explanation (`crate::explain`)
// ===========================================================================

/// One trail literal in a conflict: `p cond 0`, asserted TRUE.
///
/// `roots` is supplied by the CALLER, so the oracle can drive every entry point
/// below on z3's own root list rather than only through a consumer. AY verifies
/// it in both directions and declines a list that is wrong either way.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OExplainLit {
    /// The trail literal's signed id. Never `0`.
    pub lit: i32,
    /// Integer coefficients, low-to-high.
    pub p: Vec<BigInt>,
    /// The sign condition asserted TRUE.
    pub cond: OISignCond,
    /// Every real root of `p`, ascending.
    pub roots: Vec<ODyadicAnum>,
}

impl OExplainLit {
    fn inner(&self) -> explain::ConflictLit {
        explain::ConflictLit {
            lit: self.lit,
            p: self.p.clone(),
            cond: self.cond.inner(),
            roots: self.roots.iter().map(|r| r.0.clone()).collect(),
        }
    }
}

fn explain_lits(ls: &[OExplainLit]) -> Vec<explain::ConflictLit> {
    ls.iter().map(OExplainLit::inner).collect()
}

/// A learned clause.
///
/// Carries NO validity flag: the campaign's third blind-spot pattern is a stored
/// flag the headline metric is read off, and this type is deliberately shaped so
/// that the only way to learn whether the clause is implied is to call
/// [`oexplain_clause_is_valid`] on the cited literals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OExplanation {
    /// The clause literals: the negation of each cited trail literal.
    pub lits: Vec<i32>,
    /// The trail literals cited.
    pub cited: Vec<i32>,
}

/// **The defining property.** Is `\/_j !L_j` a theory consequence — equivalently,
/// is `/\_j L_j` unsatisfiable over the reals?
///
/// `Some(true)` is a proof, `Some(false)` a refutation with a witness available
/// from [`oexplain_countermodel`], `None` a decline.
#[must_use]
pub fn oexplain_clause_is_valid(lits: &[OExplainLit]) -> Option<bool> {
    explain::clause_is_valid(&explain_lits(lits))
}

/// The real number witnessing that the clause is NOT valid, when there is one.
///
/// Exposed separately so the oracle can adjudicate the WITNESS rather than the
/// verdict: an unwitnessed witness is a blind spot, and z3 re-evaluates this
/// point against every cited literal.
#[must_use]
pub fn oexplain_countermodel(lits: &[OExplainLit]) -> Option<Option<ODyadicAnum>> {
    explain::clause_countermodel(&explain_lits(lits)).map(|o| o.map(ODyadicAnum))
}

/// Is the clause FALSE under the trail — every literal the negation of an
/// asserted one? Total: it cannot decline.
#[must_use]
pub fn oexplain_clause_is_falsified(clause: &[i32], trail: &[i32]) -> bool {
    explain::clause_is_falsified(clause, trail)
}

/// Explain a univariate conflict. `None` when there is no conflict, when a step
/// declines, or when the clause cannot be PROVED implied.
#[must_use]
pub fn oexplain_univariate(lits: &[OExplainLit]) -> Option<OExplanation> {
    explain::explain_univariate(&explain_lits(lits)).map(|e| OExplanation {
        lits: e.lits().to_vec(),
        cited: e.cited().to_vec(),
    })
}

/// The pairs whose root ordering matters at the sample point — the restriction
/// that keeps the projection from taking all `O(m^2)` resultants.
#[must_use]
pub fn oexplain_relevant_pairs(lits: &[OExplainLit]) -> Option<Vec<(usize, usize)>> {
    explain::relevant_pairs(&explain_lits(lits))
}

/// Which projection factor a polynomial came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OProjKind {
    /// Leading coefficient of input `i` in the projected variable.
    LeadingCoeff(usize),
    /// Discriminant of input `i`.
    Discriminant(usize),
    /// Resultant of inputs `i` and `j`.
    Resultant(usize, usize),
}

/// The CAD projection, with the degree report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OProjection {
    /// Each factor and where it came from.
    pub factors: Vec<(OProjKind, OYPoly)>,
    /// Largest total degree among the inputs.
    pub in_max_total_degree: u32,
    /// Largest total degree among the outputs.
    pub out_max_total_degree: u32,
    /// Outputs that are non-zero constants: no roots, so no cell boundary.
    pub constant_factors: usize,
}

/// [`crate::explain::project`] — leading coefficients, discriminants and the
/// resultants of `pairs`.
#[must_use]
pub fn oexplain_project(polys: &[OBiPoly], pairs: &[(usize, usize)]) -> Option<OProjection> {
    let inner: Vec<RPoly<MPolyZ>> = polys.iter().map(|p| p.0.clone()).collect();
    let p = explain::project(&inner, pairs)?;
    Some(OProjection {
        factors: p
            .factors
            .iter()
            .map(|f| {
                let k = match f.kind {
                    explain::ProjKind::LeadingCoeff(i) => OProjKind::LeadingCoeff(i),
                    explain::ProjKind::Discriminant(i) => OProjKind::Discriminant(i),
                    explain::ProjKind::Resultant(i, j) => OProjKind::Resultant(i, j),
                };
                (k, OYPoly(f.poly.clone()))
            })
            .collect(),
        in_max_total_degree: p.in_max_total_degree,
        out_max_total_degree: p.out_max_total_degree,
        constant_factors: p.constant_factors,
    })
}

/// The declared ceiling on literals per conflict.
#[must_use]
pub fn oexplain_max_conflict_lits() -> usize {
    explain::MAX_CONFLICT_LITS
}

/// The declared ceiling on distinct roots in the merged decomposition.
#[must_use]
pub fn oexplain_max_conflict_roots() -> usize {
    explain::MAX_CONFLICT_ROOTS
}
