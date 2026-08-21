// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real-root isolation of a MULTIVARIATE polynomial at an algebraic sample
//! point — z3's `algebraic_numbers::manager::isolate_roots(p, x2v, roots)` and
//! its `isolate_roots_closest` sibling.
//!
//! # Why this module exists
//!
//! Everything AY already owns in the real-algebraic layer is UNIVARIATE. Given
//! `p(x) in Q[x]` it can isolate roots, take signs, compare, and do exact
//! arithmetic. What nlsat actually asks for is one step harder and is the
//! entry point the whole MCSAT loop is built around:
//!
//! > view `p` as `q_n(y_1..y_k) x^n + ... + q_0(y_1..y_k)`, fix
//! > `y_i = alpha_i` at REAL ALGEBRAIC values, and isolate the real roots of
//! > the resulting univariate polynomial.
//!
//! Those roots are the cell boundaries in the current variable. Without them
//! there is no `nlsat_evaluator`, no `nlsat_interval_set` over algebraic
//! endpoints, and no way to place a sample point between two roots whose
//! coordinates are themselves irrational. The audit of AY's real credit
//! against the port target named this and `isolate_roots_closest` as the two
//! nlsat-specific entry points AY did not have.
//!
//! It is also the primitive the measured MV QF_NRA residual needs. Those 28
//! files fail because their witnesses are z3's dyadic approximations of
//! transcendental constants inside intervals ~`1e-7` wide, and no
//! candidate-generation constant reaches them. A root of the constraint
//! polynomial AT the current partial assignment is not a candidate that has to
//! be guessed — it is computed, exactly, wherever it lies.
//!
//! # The algorithm (z3 5.0.0 `algebraic_numbers.cpp:2709`)
//!
//! The difficulty is that the specialized polynomial
//! `p(alpha_1..alpha_k, x)` has coefficients in `Q(alpha_1..alpha_k)`, not
//! `Q`, so no univariate isolator can be pointed at it directly. z3's answer
//! is to compute a univariate polynomial over `Z` whose root set is a
//! SUPERSET, then sieve:
//!
//! 1. Substitute the rational fragment of the assignment directly.
//! 2. For each remaining assigned variable `y` (ascending by the degree of its
//!    value's defining polynomial, so the cheap eliminations happen first),
//!    replace `q` by `Res_y(q, m_y)` where `m_y` is `alpha_y`'s minimal
//!    polynomial. Each resultant is a polynomial identity: every root of `q`
//!    at `y = alpha_y` survives it, because `alpha_y` is a common root of `q`
//!    (viewed in `y`) and `m_y`.
//! 3. The surviving `q(x) in Z[x]` is univariate. Isolate its real roots with
//!    the existing univariate machinery.
//! 4. **Sieve**: keep a candidate `r` only when
//!    `sign(p(alpha_1..alpha_k, r)) == 0`. The resultant introduced roots for
//!    the CONJUGATES of the `alpha_i`; this step removes them.
//!
//! Step 4 is the whole reason [`eval_sign_at`] has to be exact rather than
//! numeric: a wrong zero-test here silently invents or deletes a cell
//! boundary.
//!
//! The one genuinely hard case is a **vanishing resultant** (`q == 0`), which
//! happens when `q` and `m_y` share a factor — i.e. `q` vanishes identically
//! at some conjugate of `alpha_y`. Then the resultant says nothing at all.
//! z3's escape, reproduced here in [`isolate_roots_at`]:
//!
//! * `deg_x p == 1`: solve `c_1 x + c_0 = 0` directly with exact algebraic
//!   arithmetic.
//! * otherwise: find the highest `i >= 1` with `c_i(alpha) != 0`, introduce a
//!   FRESH variable `z` bound to the value `c_i(alpha)`, and recurse on
//!   `z x^i + c_{i-1} x^{i-1} + ... + c_0`. The resultant cannot vanish a
//!   second time, because `0` is not a root of the polynomial defining a
//!   non-zero `z`. The recursion is depth-1 by construction; a second
//!   vanishing is a violated invariant and fails closed with `None`.
//!
//! # Where this deviates from z3, and why
//!
//! Two places, both forced by something AY does not own yet. Both are recorded
//! here because the next lane will meet them again.
//!
//! **1. No polynomial factorization.** z3 factors every derived defining
//! polynomial and keeps the irreducible factor its value actually satisfies
//! (`upolynomial_factorization.cpp`, not ported). AY's derived polynomials —
//! [`crate::algebraic::RealAlgebraicValue::to_number`] — are only SQUARE-FREE,
//! so they routinely carry factors the value does not satisfy. That breaks
//! z3's stated invariant for the vanishing-resultant escape ("0 is not a root
//! of the polynomial defining `a`"), and without a repair the escape's own
//! resultant vanishes and the computation refuses for no mathematical reason.
//! [`Anum::strip_zero_root`] repairs exactly the invariant that is needed, by
//! dividing out `y^t` from a value known to be non-zero. It is the minimum
//! that works; a real factorization pass would subsume it, and would also cut
//! every degree in the elimination chain.
//!
//! **2. Sign at a multi-coordinate point uses a separation bound, not
//! algebraic arithmetic.** See [`eval_sign_at`]. z3 has the algebraic-
//! arithmetic version sitting behind an `#if 0`; AY follows the live branch.
//!
//! # Fail-closed
//!
//! Every entry point returns `Option`. `None` means "AY declines", never "here
//! is an approximate answer". The refusals are enumerated at each site:
//! unassigned variables, a non-representable exact value, a refinement cap, a
//! second vanishing resultant, an exact-arithmetic degree cap.
//!
//! # Not wired in
//!
//! Nothing in the solve path calls this module. It cannot change a verdict.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::algebraic::{RealAlgebraic, RealScalar, Refined};
use crate::subresultant::{self, MPolyZ, MVar, Mono, RPoly};
use crate::univariate::{isolate_roots, square_free_part, RootMarker, UniPoly};

/// Refinement rounds allowed in [`eval_sign_at`]'s separation-bound loop.
///
/// Each round halves every algebraic coordinate's enclosure, so the enclosure
/// of the value shrinks geometrically and the loop provably ends — either
/// outside zero or strictly inside `(-L, L)`. The cap is a bug-catcher, not a
/// tuning knob: reaching it means the separation bound or the refinement is
/// wrong, and the operation fails closed.
const INTERVAL_ROUNDS: usize = 512;

/// Degree cap on an intermediate value during exact algebraic evaluation.
///
/// Multiplying two algebraic numbers over DIFFERENT defining polynomials
/// produces one whose defining polynomial has degree up to the product of the
/// two. A term of a multivariate polynomial can chain several such products,
/// so the degree can grow multiplicatively without bound. Past this cap the
/// computation is refused rather than attempted: an exact answer that never
/// arrives is not an exact answer.
const MAX_EXACT_DEGREE: usize = 96;

/// Recursion cap for the vanishing-resultant escape. z3's own escape is
/// depth-1 by construction (`nested_call` throws on a second vanishing); this
/// is the same bound stated as a number.
const MAX_NESTED: usize = 1;

// ============================================================================
// Algebraic sample points (z3's `anum` / `var2anum`)
// ============================================================================

/// A value at a sample point: an exact rational, or a real algebraic number
/// pinned by a square-free defining polynomial and an isolating interval.
///
/// This mirrors z3's `anum`, whose two states are "basic" (an `mpq`) and
/// "algebraic" (an `algebraic_cell`). Keeping them apart matters: the rational
/// fragment of an assignment is eliminated by SUBSTITUTION, which is cheap and
/// exact, while the algebraic fragment has to be eliminated by RESULTANTS,
/// which is neither.
/// `PartialEq` here is STRUCTURAL, not mathematical: two `Anum`s that denote
/// the same real number through different defining polynomials compare
/// unequal. Use [`Anum::cmp_rational`] or the exact scalar layer for a
/// mathematical comparison.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Anum {
    /// An exact rational value.
    Rat(BigRational),
    /// An irrational real algebraic value.
    Alg(RealAlgebraic),
}

impl Anum {
    /// Degree of the defining polynomial: `1` for a rational.
    ///
    /// z3 sorts the elimination order by this (`var_degree_lt`), so the
    /// resultants that grow the polynomial least happen first.
    pub(crate) fn degree(&self) -> usize {
        match self {
            Self::Rat(_) => 1,
            Self::Alg(a) => a.poly_coeffs().len().saturating_sub(1),
        }
    }

    /// The value as an exact scalar, for the exact-arithmetic paths.
    pub(crate) fn to_scalar(&self) -> RealScalar {
        match self {
            Self::Rat(r) => RealScalar::Rational(r.clone()),
            Self::Alg(a) => RealScalar::Algebraic(a.as_value()),
        }
    }

    /// A rational enclosure `(lo, hi)` with `lo <= value <= hi`, degenerate for
    /// a rational.
    fn enclosure(&self) -> (BigRational, BigRational) {
        match self {
            Self::Rat(r) => (r.clone(), r.clone()),
            Self::Alg(a) => {
                let (lo, hi) = a.interval();
                (lo.clone(), hi.clone())
            }
        }
    }

    /// Narrow this value's enclosure by one bisection, given the current one.
    ///
    /// `Some((lo, hi))` is a strictly narrower enclosure; a bisection that
    /// lands exactly on the root collapses the enclosure to that rational
    /// (returned as `(r, r)`). `None` is a fail-closed refusal from the
    /// underlying refinement.
    fn narrow(&self, lo: &BigRational, hi: &BigRational) -> Option<(BigRational, BigRational)> {
        match self {
            Self::Rat(r) => Some((r.clone(), r.clone())),
            Self::Alg(a) => match a.refine_from(lo, hi)? {
                Refined::Interval(l, h) => Some((l, h)),
                Refined::Exact(r) => Some((r.clone(), r)),
            },
        }
    }

    /// Build from an exact scalar, normalizing a derived (residue) algebraic
    /// value to a standalone defining polynomial first.
    ///
    /// `None` when the value has no representable standalone form (a
    /// refinement cap inside
    /// [`crate::algebraic::RealAlgebraicValue::to_number`]).
    pub(crate) fn from_scalar(s: &RealScalar) -> Option<Self> {
        match s {
            RealScalar::Rational(r) => Some(Self::Rat(r.clone())),
            RealScalar::Algebraic(v) => match v.to_number()? {
                RealScalar::Rational(r) => Some(Self::Rat(r)),
                RealScalar::Algebraic(w) => Some(Self::Alg(w.alpha().clone())),
            },
        }
    }

    /// The same value, with the factor `y^t` removed from its defining
    /// polynomial. **Only sound when the value is known to be non-zero**,
    /// which every caller checks first.
    ///
    /// z3's vanishing-resultant escape rests on one stated invariant: "the
    /// resultant will not vanish again because 0 is not a root of the
    /// polynomial defining `a`". z3 gets that for free because it FACTORS
    /// every derived defining polynomial and keeps the irreducible factor the
    /// value actually satisfies. AY's derived polynomials are only square-free
    /// (see [`crate::algebraic::RealAlgebraicValue::to_number`]), so they can
    /// still carry a spurious `y` factor — and when they do, the escape's own
    /// resultant vanishes and the whole computation fails closed for no
    /// mathematical reason.
    ///
    /// Removing exactly the zero root is the minimum that restores the
    /// invariant without a factorization pass. The isolating interval is
    /// preserved: a divisor has a subset of the roots, so an interval that
    /// isolated this root with non-root endpoints still does.
    fn strip_zero_root(&self) -> Option<Self> {
        let Self::Alg(a) = self else {
            return Some(self.clone());
        };
        let coeffs = a.poly_coeffs();
        let t = coeffs.iter().position(|c| !Zero::is_zero(c))?;
        if t == 0 {
            return Some(self.clone());
        }
        let trimmed = UniPoly::from_coeffs(
            coeffs[t..]
                .iter()
                .map(|c| BigRational::from_integer(c.clone()))
                .collect(),
        );
        let (lo, hi) = a.interval();
        let rebuilt = RealAlgebraic::from_isolating_interval(&trimmed, lo, hi)?;
        Some(Self::Alg(rebuilt))
    }

    /// Exact comparison against a rational. `None` on a fail-closed refusal.
    pub(crate) fn cmp_rational(&self, r: &BigRational) -> Option<Ordering> {
        match self {
            Self::Rat(q) => Some(q.cmp(r)),
            Self::Alg(a) => a.cmp_rational(r),
        }
    }
}

/// An assignment of sample-point values to variables — z3's
/// `polynomial::var2anum`.
#[derive(Clone, Debug, Default)]
pub(crate) struct Var2Anum {
    map: BTreeMap<MVar, Anum>,
}

impl Var2Anum {
    /// The empty assignment.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Bind `v` to `a`, replacing any previous binding.
    pub(crate) fn set(&mut self, v: MVar, a: Anum) {
        self.map.insert(v, a);
    }

    /// Is `v` assigned?
    pub(crate) fn contains(&self, v: MVar) -> bool {
        self.map.contains_key(&v)
    }

    /// The value of `v`, if assigned.
    pub(crate) fn get(&self, v: MVar) -> Option<&Anum> {
        self.map.get(&v)
    }

    /// The largest variable mentioned by this assignment, if any.
    fn max_var(&self) -> Option<MVar> {
        self.map.keys().next_back().copied()
    }

    /// A copy with one extra binding — z3's `ext_var2num`.
    fn extended(&self, v: MVar, a: Anum) -> Self {
        let mut out = self.clone();
        out.set(v, a);
        out
    }
}

// ============================================================================
// Multivariate polynomial views (recursive representation, substitution)
// ============================================================================

/// The variables occurring in `p`, ascending.
pub(crate) fn vars_of(p: &MPolyZ) -> Vec<MVar> {
    let mut out: Vec<MVar> = Vec::new();
    for (m, _) in p.terms() {
        for &(v, _) in m.pairs() {
            if !out.contains(&v) {
                out.push(v);
            }
        }
    }
    out.sort_unstable();
    out
}

/// Degree of `p` in `v` (zero when `v` does not occur, including for the zero
/// polynomial).
pub(crate) fn degree_in(p: &MPolyZ, v: MVar) -> usize {
    let mut d = 0u32;
    for (m, _) in p.terms() {
        for &(w, e) in m.pairs() {
            if w == v {
                d = d.max(e);
            }
        }
    }
    d as usize
}

/// The exponent of `v` in a monomial (`0` when absent).
fn exp_of(m: &Mono, v: MVar) -> u32 {
    m.pairs()
        .iter()
        .find(|&&(w, _)| w == v)
        .map_or(0, |&(_, e)| e)
}

/// `m` with `v` removed.
fn drop_var(m: &Mono, v: MVar) -> Mono {
    Mono::from_pairs(
        m.pairs()
            .iter()
            .filter(|&&(w, _)| w != v)
            .copied()
            .collect(),
    )
}

/// The coefficient of `v^k` in `p`, an element of `Z[other variables]`.
pub(crate) fn coeff_in(p: &MPolyZ, v: MVar, k: usize) -> MPolyZ {
    let k = k as u32;
    MPolyZ::from_terms(
        p.terms()
            .iter()
            .filter(|(m, _)| exp_of(m, v) == k)
            .map(|(m, c)| (drop_var(m, v), c.clone()))
            .collect(),
    )
}

/// `p` re-expressed as a univariate polynomial in `v` over `Z[other]` — z3's
/// recursive representation, and exactly the shape
/// [`crate::subresultant`] operates on.
pub(crate) fn to_rpoly(p: &MPolyZ, v: MVar) -> RPoly<MPolyZ> {
    let d = degree_in(p, v);
    RPoly::from_coeffs((0..=d).map(|k| coeff_in(p, v, k)).collect())
}

/// The inverse of [`to_rpoly`].
pub(crate) fn from_rpoly(rp: &RPoly<MPolyZ>, v: MVar) -> MPolyZ {
    let mut terms: Vec<(Mono, BigInt)> = Vec::new();
    for (k, c) in rp.coeffs().iter().enumerate() {
        for (m, coeff) in c.terms() {
            let mut pairs: Vec<(MVar, u32)> = m.pairs().to_vec();
            if k > 0 {
                pairs.push((v, k as u32));
            }
            terms.push((Mono::from_pairs(pairs), coeff.clone()));
        }
    }
    MPolyZ::from_terms(terms)
}

/// A univariate integer polynomial as an [`MPolyZ`] in variable `v`.
pub(crate) fn mpoly_from_ints(coeffs: &[BigInt], v: MVar) -> MPolyZ {
    MPolyZ::from_terms(
        coeffs
            .iter()
            .enumerate()
            .map(|(k, c)| (Mono::var_pow(v, k as u32), c.clone()))
            .collect(),
    )
}

/// Substitute `v = r` into `p`, staying in `Z[...]` by multiplying through by
/// `den(r)^deg_v(p)`.
///
/// That multiplier is STRICTLY POSITIVE (`num-rational` normalizes
/// denominators positive), so the substituted polynomial has the same real
/// roots in every remaining variable AND the same sign everywhere as the true
/// specialization. Both facts are load-bearing: [`isolate_roots_at`] relies on
/// the root sets agreeing, [`eval_sign_at`] on the signs agreeing.
pub(crate) fn subst_rational(p: &MPolyZ, v: MVar, r: &BigRational) -> MPolyZ {
    let d = degree_in(p, v);
    if d == 0 {
        return p.clone();
    }
    let num = r.numer();
    let den = r.denom();
    let mut terms: Vec<(Mono, BigInt)> = Vec::with_capacity(p.terms().len());
    for (m, c) in p.terms() {
        let e = exp_of(m, v) as usize;
        // c * num^e * den^(d - e), which is c * r^e * den^d.
        let factor = num.pow(e as u32) * den.pow((d - e) as u32);
        terms.push((drop_var(m, v), c * factor));
    }
    MPolyZ::from_terms(terms)
}

/// Substitute every RATIONAL binding of `x2v` into `p` at once.
pub(crate) fn subst_rational_fragment(p: &MPolyZ, x2v: &Var2Anum) -> MPolyZ {
    let mut out = p.clone();
    for v in vars_of(p) {
        if let Some(Anum::Rat(r)) = x2v.get(v) {
            out = subst_rational(&out, v, r);
        }
    }
    out
}

/// `Res_v(f, g)`, an element of `Z[remaining variables]`.
///
/// `None` when [`crate::subresultant::resultant`] declines (a zero operand, or
/// an exact division that is not exact — both fail-closed refusals).
pub(crate) fn resultant_in(f: &MPolyZ, g: &MPolyZ, v: MVar) -> Option<MPolyZ> {
    subresultant::resultant(&to_rpoly(f, v), &to_rpoly(g, v))
}

/// `p` as a univariate rational polynomial in `v`, provided no OTHER variable
/// occurs. `None` otherwise.
pub(crate) fn to_unipoly(p: &MPolyZ, v: MVar) -> Option<UniPoly> {
    if vars_of(p).iter().any(|&w| w != v) {
        return None;
    }
    let d = degree_in(p, v);
    let mut coeffs = vec![BigRational::zero(); d + 1];
    for (m, c) in p.terms() {
        coeffs[exp_of(m, v) as usize] = BigRational::from_integer(c.clone());
    }
    Some(UniPoly::from_coeffs(coeffs))
}

// ============================================================================
// Exact sign at an algebraic sample point (z3's `eval_sign_at`)
// ============================================================================

/// A closed rational interval used by the numeric fast path.
#[derive(Clone, Debug)]
struct Iv {
    lo: BigRational,
    hi: BigRational,
}

impl Iv {
    fn point(r: BigRational) -> Self {
        Self {
            lo: r.clone(),
            hi: r,
        }
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            lo: &self.lo + &other.lo,
            hi: &self.hi + &other.hi,
        }
    }

    fn mul(&self, other: &Self) -> Self {
        let a = &self.lo * &other.lo;
        let b = &self.lo * &other.hi;
        let c = &self.hi * &other.lo;
        let d = &self.hi * &other.hi;
        let lo = a.clone().min(b.clone()).min(c.clone()).min(d.clone());
        let hi = a.max(b).max(c).max(d);
        Self { lo, hi }
    }

    /// The sign of every point in the interval, or `None` when it straddles
    /// (or touches) zero.
    fn definite_sign(&self) -> Option<i32> {
        if self.lo.is_positive() {
            Some(1)
        } else if self.hi.is_negative() {
            Some(-1)
        } else {
            None
        }
    }
}

/// Evaluate `p` with interval arithmetic over the given per-variable
/// enclosures. Every variable of `p` must be present in `ivs`.
fn eval_interval(p: &MPolyZ, ivs: &BTreeMap<MVar, Iv>) -> Option<Iv> {
    let mut acc = Iv::point(BigRational::zero());
    for (m, c) in p.terms() {
        let mut term = Iv::point(BigRational::from_integer(c.clone()));
        for &(v, e) in m.pairs() {
            let iv = ivs.get(&v)?;
            for _ in 0..e {
                term = term.mul(iv);
            }
        }
        acc = acc.add(&term);
    }
    Some(acc)
}

/// The degree of a scalar's defining polynomial, for the growth cap.
fn scalar_degree(s: &RealScalar) -> usize {
    match s {
        RealScalar::Rational(_) => 1,
        RealScalar::Algebraic(v) => v.alpha().poly_coeffs().len().saturating_sub(1),
    }
}

/// Exact evaluation of `p` at `x2v` as a real algebraic scalar.
///
/// `None` on an unassigned variable, on a fail-closed refusal from the exact
/// arithmetic, or when an intermediate value's defining polynomial exceeds
/// [`MAX_EXACT_DEGREE`].
pub(crate) fn eval_exact(p: &MPolyZ, x2v: &Var2Anum) -> Option<RealScalar> {
    let mut acc = RealScalar::Rational(BigRational::zero());
    for (m, c) in p.terms() {
        let mut term = RealScalar::Rational(BigRational::from_integer(c.clone()));
        for &(v, e) in m.pairs() {
            let val = x2v.get(v)?.to_scalar();
            for _ in 0..e {
                term = term.mul(&val)?;
                if scalar_degree(&term) > MAX_EXACT_DEGREE {
                    return None;
                }
            }
        }
        acc = acc.add(&term)?;
        if scalar_degree(&acc) > MAX_EXACT_DEGREE {
            return None;
        }
    }
    Some(acc)
}

/// A certified lower bound on the magnitude of the NON-ZERO roots of `r`.
///
/// Write `r(y) = y^t * s(y)` with `s(0) != 0`; the non-zero roots of `r` are
/// exactly the roots of `s`. Apply Cauchy's upper bound to the reversal of
/// `s`, whose roots are the reciprocals of `s`'s:
///
/// ```text
///   |1/rho| <= 1 + max_{j > t} |a_j| / |a_t|      =>      |rho| >= L
///   L = |a_t| / (|a_t| + max_{j > t} |a_j|)
/// ```
///
/// `None` for the zero polynomial. `L` is always in `(0, 1]`.
fn nonzero_root_lower_bound(r: &UniPoly) -> Option<BigRational> {
    let coeffs = r.coeffs();
    let t = coeffs.iter().position(|c| !c.is_zero())?;
    let a_t = coeffs[t].abs();
    let mut max_above = BigRational::zero();
    for c in &coeffs[t + 1..] {
        let a = c.abs();
        if a > max_above {
            max_above = a;
        }
    }
    Some(&a_t / (&a_t + max_above))
}

/// A certified separation bound for `p` at `x2v`: a positive rational `L` such
/// that the exact value `v = p(x2v)` is either zero or satisfies `|v| >= L`.
///
/// This is z3's resultant argument (`algebraic_numbers.cpp:2506`). The
/// polynomials
///
/// ```text
///   y - p(x_1, .., x_n),  m_1(x_1),  ..,  m_n(x_n)
/// ```
///
/// all vanish at `y -> v, x_i -> alpha_i`, so `v` is a root of
/// `R(y) = Res_{x_1..x_n}(y - p, m_1, .., m_n)`. `R` is not the zero
/// polynomial — the coefficient of `y` in `y - p` is the constant `1`, so no
/// eliminated variable can carry a common factor with it — and a lower bound
/// on `R`'s non-zero roots is therefore a lower bound on `|v|` whenever `v` is
/// non-zero.
///
/// Every variable of `p` must be assigned to an irrational value (substitute
/// the rational fragment first). `None` is a fail-closed refusal.
fn separation_bound(p: &MPolyZ, xs: &[MVar], x2v: &Var2Anum) -> Option<BigRational> {
    // A fresh variable for the value.
    let y = xs
        .iter()
        .copied()
        .chain(x2v.max_var())
        .chain(vars_of(p))
        .max()
        .map_or(0, |m| m + 1);
    // R := y - p
    let mut terms: Vec<(Mono, BigInt)> = vec![(Mono::var_pow(y, 1), BigInt::one())];
    for (m, c) in p.terms() {
        terms.push((m.clone(), -c));
    }
    let mut r = MPolyZ::from_terms(terms);

    // Eliminate the coordinates cheapest-first, as z3 does.
    let mut order: Vec<MVar> = xs.to_vec();
    order.sort_by_key(|&v| x2v.get(v).map_or(usize::MAX, Anum::degree));
    for &v in &order {
        if degree_in(&r, v) == 0 {
            continue;
        }
        let Some(Anum::Alg(alpha)) = x2v.get(v) else {
            return None;
        };
        let m_v = mpoly_from_ints(&alpha.poly_coeffs(), v);
        r = resultant_in(&r, &m_v, v)?;
        if r.terms().is_empty() {
            // Cannot happen (see above); never guess when it does.
            return None;
        }
    }
    let up = to_unipoly(&r, y)?;
    nonzero_root_lower_bound(&up)
}

/// The EXACT sign of `p` at the sample point `x2v`: `-1`, `0` or `+1`.
///
/// This is z3's `eval_sign_at`, and it is the sieve [`isolate_roots_at`] hangs
/// on: a wrong zero-test here silently invents or deletes a cell boundary.
///
/// Interval arithmetic alone can only ever prove a value NON-zero — no finite
/// refinement of an enclosure that contains zero proves the value is zero. The
/// missing half is a **separation bound**: a certified `L > 0` such that the
/// value is zero or at least `L` in magnitude ([`separation_bound`]). With `L`
/// in hand, refining the enclosure terminates either way, and the answer is
/// exact.
///
/// Three paths, in cost order:
///
/// 1. **Rational coordinates only** — substitute and read the sign off.
/// 2. **One irrational coordinate** — substituting the rationals leaves a
///    univariate polynomial over `Q`, and the existing exact
///    [`RealAlgebraic::sign_of_poly`], which certifies a zero algebraically by
///    a GCD against the defining polynomial, answers directly.
/// 3. **Several irrational coordinates** — the separation-bound loop above.
///
/// Note what is deliberately NOT here: evaluating `p` with exact algebraic
/// arithmetic and testing the result against zero. That is correct but the
/// degrees multiply at every cross-point operation, and z3 has the same code
/// sitting behind an `#if 0` for exactly that reason. AY keeps that path
/// ([`eval_exact`]) only where an actual VALUE is needed rather than a sign.
///
/// `None` is a refusal, never a guess.
pub(crate) fn eval_sign_at(p: &MPolyZ, x2v: &Var2Anum) -> Option<i32> {
    if p.terms().is_empty() {
        return Some(0);
    }
    for v in vars_of(p) {
        if !x2v.contains(v) {
            return None;
        }
    }

    // (1) Eliminate the rational fragment. The multiplier this introduces is
    // strictly positive, so the sign is unchanged.
    let p2 = subst_rational_fragment(p, x2v);
    if p2.terms().is_empty() {
        return Some(0);
    }
    let xs = vars_of(&p2);
    if xs.is_empty() {
        return Some(sign_of_int(&p2.terms()[0].1));
    }

    // (2) A single irrational coordinate is the univariate case.
    if xs.len() == 1 {
        let v = xs[0];
        let Some(Anum::Alg(alpha)) = x2v.get(v) else {
            return None;
        };
        let up = to_unipoly(&p2, v)?;
        return alpha.sign_of_poly(&up);
    }

    // (3) Refine enclosures against the separation bound.
    let sep = separation_bound(&p2, &xs, x2v)?;
    let neg_sep = -&sep;
    let mut ivs: BTreeMap<MVar, Iv> = BTreeMap::new();
    for &v in &xs {
        let (lo, hi) = x2v.get(v)?.enclosure();
        ivs.insert(v, Iv { lo, hi });
    }
    for _ in 0..INTERVAL_ROUNDS {
        let value = eval_interval(&p2, &ivs)?;
        if let Some(s) = value.definite_sign() {
            return Some(s);
        }
        if value.lo > neg_sep && value.hi < sep {
            // The enclosure is strictly inside (-L, L) and contains zero, so
            // the value cannot be a non-zero root: it IS zero.
            return Some(0);
        }
        for &v in &xs {
            let iv = ivs.get(&v)?.clone();
            if iv.lo == iv.hi {
                continue;
            }
            let (lo, hi) = x2v.get(v)?.narrow(&iv.lo, &iv.hi)?;
            ivs.insert(v, Iv { lo, hi });
        }
    }
    // The enclosure width shrinks geometrically, so this is unreachable for
    // any input this layer produces. Fail closed rather than guess.
    None
}

fn sign_of_int(c: &BigInt) -> i32 {
    match c.sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    }
}

// ============================================================================
// isolate_roots at a var2anum tuple
// ============================================================================

/// Isolate the real roots of `p` in `x`, with every other variable of `p`
/// fixed at the algebraic sample point `x2v` — z3's
/// `isolate_roots(p, x2v, roots)`.
///
/// The result is ascending and duplicate-free. It is EMPTY, not an error, in
/// every degenerate case z3 also reports as empty:
///
/// * `p` is zero or constant;
/// * `p` becomes constant once the rational fragment is substituted;
/// * `x` does not occur in the specialized polynomial (its coefficients all
///   vanished), so `p` is not a polynomial in `x` at this point at all.
///
/// That last convention is worth stating plainly: a polynomial that vanishes
/// IDENTICALLY in `x` at this sample point reports no roots rather than
/// infinitely many, exactly as z3 does. Callers that need to distinguish
/// "no roots" from "everywhere zero" must ask [`eval_sign_at`] separately.
///
/// `None` is a fail-closed refusal (unassigned coordinate, a refinement or
/// degree cap, a second vanishing resultant).
pub(crate) fn isolate_roots_at(p: &MPolyZ, x: MVar, x2v: &Var2Anum) -> Option<Vec<Anum>> {
    isolate_roots_rec(p, x, x2v, 0)
}

fn isolate_roots_rec(p: &MPolyZ, x: MVar, x2v: &Var2Anum, depth: usize) -> Option<Vec<Anum>> {
    if p.terms().is_empty() {
        return Some(Vec::new());
    }
    // Univariate in `x` already: no specialization needed.
    if vars_of(p).iter().all(|&v| v == x) {
        return roots_of_univariate(p, x);
    }

    // (1) Eliminate the rational fragment by substitution.
    let p_prime = subst_rational_fragment(p, x2v);
    if p_prime.terms().is_empty() {
        return Some(Vec::new());
    }
    let vars = vars_of(&p_prime);
    if vars.is_empty() {
        // A non-zero constant has no roots.
        return Some(Vec::new());
    }
    if degree_in(&p_prime, x) == 0 {
        // `x` vanished under the substitution: not a polynomial in `x` here.
        return Some(Vec::new());
    }
    if vars.iter().all(|&v| v == x) {
        return roots_of_univariate(&p_prime, x);
    }

    // (2) Eliminate each remaining (necessarily irrational) coordinate by a
    // resultant against its minimal polynomial, cheapest first.
    let mut others: Vec<MVar> = vars.iter().copied().filter(|&v| v != x).collect();
    for &v in &others {
        if !x2v.contains(v) {
            return None;
        }
    }
    others.sort_by_key(|&v| x2v.get(v).map_or(usize::MAX, Anum::degree));

    let mut q = p_prime.clone();
    let mut vanished = false;
    for &y in &others {
        let Some(Anum::Alg(alpha)) = x2v.get(y) else {
            // A rational slipped past step (1) — impossible, but never guess.
            return None;
        };
        if degree_in(&q, y) == 0 {
            // `y` was already eliminated by an earlier resultant. z3 would
            // still compute `Res_y(q, m_y) = q^deg(m_y)`, which has the same
            // real roots; skipping it keeps the degree from being multiplied
            // for nothing and cannot change the answer.
            continue;
        }
        let m_y = mpoly_from_ints(&alpha.poly_coeffs(), y);
        q = resultant_in(&q, &m_y, y)?;
        if q.terms().is_empty() {
            vanished = true;
            break;
        }
    }

    if vanished {
        if depth >= MAX_NESTED {
            // z3 throws here; AY declines.
            return None;
        }
        return vanishing_escape(&p_prime, x, x2v, depth);
    }

    if vars_of(&q).is_empty() {
        // A non-zero constant resultant: `p` has no roots at this point.
        return Some(Vec::new());
    }
    if vars_of(&q).iter().any(|&v| v != x) {
        // The elimination did not reach a univariate polynomial. Refuse
        // rather than isolate roots of something that is not univariate.
        return None;
    }

    // (3) Isolate the candidates and (4) sieve them with the exact sign test.
    let candidates = roots_of_univariate(&q, x)?;
    let mut out = Vec::with_capacity(candidates.len());
    for r in candidates {
        let ext = x2v.extended(x, r.clone());
        if eval_sign_at(&p_prime, &ext)? == 0 {
            out.push(r);
        }
    }
    Some(out)
}

/// z3's vanishing-resultant escape, reproduced.
fn vanishing_escape(p_prime: &MPolyZ, x: MVar, x2v: &Var2Anum, depth: usize) -> Option<Vec<Anum>> {
    let n = degree_in(p_prime, x);
    if n == 0 {
        return Some(Vec::new());
    }
    if n == 1 {
        // Linear in `x`: solve `c_1 x + c_0 = 0` exactly.
        //
        // The zero test on `c_1` is done with [`eval_sign_at`] and NOT by
        // letting `RealScalar::recip` fail. `recip` returns `None` both for a
        // zero operand and for a fail-closed refusal, and collapsing those two
        // would report "no roots" for a computation that merely declined —
        // silently deleting a cell boundary, which is the exact failure this
        // module exists to avoid.
        let c1_poly = coeff_in(p_prime, x, 1);
        if eval_sign_at(&c1_poly, x2v)? == 0 {
            // The degree collapsed at this sample point: no roots.
            return Some(Vec::new());
        }
        let c0 = eval_exact(&coeff_in(p_prime, x, 0), x2v)?;
        let c1 = eval_exact(&c1_poly, x2v)?;
        // `c1 != 0` is established, so `None` here is a genuine refusal.
        let inv = c1.recip()?;
        let root = c0.mul(&inv)?.neg();
        return Some(vec![Anum::from_scalar(&root)?]);
    }
    // Find the highest `i >= 1` whose coefficient does not vanish here.
    let mut top = 0usize;
    for i in (1..=n).rev() {
        let c = coeff_in(p_prime, x, i);
        if eval_sign_at(&c, x2v)? != 0 {
            top = i;
            break;
        }
    }
    if top == 0 {
        // Every coefficient of a positive power of `x` vanishes: no roots.
        return Some(Vec::new());
    }
    // `a` is non-zero by construction (that is how `top` was chosen), so
    // stripping a spurious zero root is sound — and it is what makes the
    // recursive resultant non-vanishing.
    let a = Anum::from_scalar(&eval_exact(&coeff_in(p_prime, x, top), x2v)?)?.strip_zero_root()?;
    // A fresh variable, above everything either the polynomial or the
    // assignment mentions.
    let z = vars_of(p_prime)
        .into_iter()
        .chain(x2v.max_var())
        .chain(std::iter::once(x))
        .max()
        .map_or(0, |m| m + 1);
    // q2 = z*x^top + c_{top-1} x^{top-1} + ... + c_0
    let mut coeffs: Vec<MPolyZ> = (0..top).map(|i| coeff_in(p_prime, x, i)).collect();
    coeffs.push(MPolyZ::term(Mono::var_pow(z, 1), BigInt::one()));
    let q2 = from_rpoly(&RPoly::from_coeffs(coeffs), x);
    let ext = x2v.extended(z, a);
    isolate_roots_rec(&q2, x, &ext, depth + 1)
}

/// Real roots of a polynomial that is univariate in `x` over `Z`, ascending.
fn roots_of_univariate(p: &MPolyZ, x: MVar) -> Option<Vec<Anum>> {
    let up = to_unipoly(p, x)?;
    if up.degree().unwrap_or(0) < 1 {
        return Some(Vec::new());
    }
    let sf = square_free_part(&up)?;
    if sf.degree().unwrap_or(0) < 1 {
        return Some(Vec::new());
    }
    let markers = isolate_roots(&sf)?;
    let mut out = Vec::with_capacity(markers.len());
    for m in markers {
        match m {
            RootMarker::Rational(r) => out.push(Anum::Rat(r)),
            RootMarker::Interval(lo, hi) => {
                out.push(Anum::Alg(RealAlgebraic::from_isolating_interval(
                    &sf, &lo, &hi,
                )?));
            }
        }
    }
    Some(out)
}

// ============================================================================
// isolate_roots_closest
// ============================================================================

/// The roots of `p` at `x2v` that bracket the rational `s` — z3's
/// `isolate_roots_closest`.
///
/// Returns the last root `<= s` and the first root `> s`, or the single root
/// `s` itself when `s` is a root, together with each returned root's **1-based
/// index in the full ascending root list**. Both vectors are ascending and the
/// same length.
///
/// nlsat wants exactly this when it has a rational candidate sample point and
/// needs the cell containing it: the two roots that bound the cell, and
/// nothing else.
pub(crate) fn isolate_roots_closest_at(
    p: &MPolyZ,
    x: MVar,
    x2v: &Var2Anum,
    s: &BigRational,
) -> Option<(Vec<Anum>, Vec<usize>)> {
    let all = isolate_roots_at(p, x, x2v)?;
    let mut below: Option<usize> = None;
    let mut above: Option<usize> = None;
    for (i, r) in all.iter().enumerate() {
        match r.cmp_rational(s)? {
            Ordering::Equal => {
                // `s` is itself a root: it is the only answer.
                return Some((vec![r.clone()], vec![i + 1]));
            }
            Ordering::Less => below = Some(i),
            Ordering::Greater => {
                if above.is_none() {
                    above = Some(i);
                }
            }
        }
    }
    let mut roots = Vec::new();
    let mut indices = Vec::new();
    for i in below.into_iter().chain(above) {
        roots.push(all[i].clone());
        indices.push(i + 1);
    }
    Some((roots, indices))
}

#[cfg(test)]
#[path = "mroot_tests.rs"]
mod tests;
