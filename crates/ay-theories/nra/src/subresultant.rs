// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fraction-free subresultant algebra: the projection substrate for CAD/nlsat.
//!
//! # Why this module exists
//!
//! `algebraic.rs` currently computes resultants with
//! [`crate::algebraic::sylvester_det_fixed`] — an `n x n` Gaussian elimination
//! over [`BigRational`]. That is asymptotically wrong for CAD projection on two
//! independent counts:
//!
//! 1. **Coefficient blow-up.** Gaussian elimination over a fraction field grows
//!    numerators and denominators exponentially in `n`; the intermediate entries
//!    are unbounded rationals with no common structure. Fraction-free (Bareiss)
//!    elimination keeps every intermediate entry equal to a *minor* of the input
//!    matrix, so entries are Hadamard-bounded — a polynomial, not exponential,
//!    bit-size bound.
//! 2. **Multivariate specialization.** Projection needs `Res_x(p, q)` where the
//!    coefficients live in `Z[y_1..y_k]`, not `Q`. The incumbent can only work
//!    over a field, so `icp.rs::resultant_eliminate` has to *interpolate*: it
//!    evaluates `d1*kv + d2*ku + 1` separate Sylvester determinants at integer
//!    sample points and Lagrange-interpolates the answer back. That is only
//!    implemented for the bivariate case and is a dead end for `k >= 2`.
//!    Working directly over the ring `Z[y_1..y_k]` removes the interpolation
//!    loop entirely.
//!
//! Neither of those is what CAD actually asks for. Every projection operator in
//! use (Collins, Hong, McCallum, Lazard, Brown) is defined in terms of the
//! **principal subresultant coefficient chain** `psc_j(p, q, x)`, not a bare
//! resultant. z3 exposes exactly that as
//! `polynomial::manager::psc_chain(p, q, x, S)`
//! (`src/math/polynomial/polynomial.h:874`) and `nlsat_explain` consumes it
//! directly. This module supplies that primitive.
//!
//! # What is here
//!
//! * [`ExactRing`] — a commutative ring with *exact* division: `exact_div`
//!   returns `None` whenever the quotient is not in the ring. This is the whole
//!   fail-closed story; every algorithm below is division-free except for
//!   divisions that are exact by a theorem, so a `None` means "the caller's
//!   precondition was violated" and never "the answer is approximately this".
//! * [`RPoly`] — a dense univariate polynomial over an [`ExactRing`], with
//!   [`RPoly::pseudo_rem`] (`prem`, using the full `lc^(deg a - deg b + 1)`
//!   multiplier, matching z3's `exact_pseudo_remainder`).
//! * [`MPolyZ`] — a sparse multivariate polynomial over `Z` under graded-lex,
//!   with exact division. This is the coefficient ring CAD projection needs;
//!   `RPoly<MPolyZ>` is a polynomial in the main variable with coefficients in
//!   `Z[y_1..y_k]`, i.e. exactly z3's recursive representation.
//! * [`subresultant_chain_det`] — the **specification**: the classical
//!   determinantal definition of `S_j(f, g)`, evaluated with fraction-free
//!   Bareiss elimination over the ring. Correct by construction, `O(n^5)` ring
//!   operations for the whole chain.
//! * [`subresultant_chain_prs`] — the **fast path**: the classical subresultant
//!   polynomial remainder sequence recurrence (Collins/Brown/Ducos), `O(n^2)`
//!   ring operations, handling defective (degree-gap) chains explicitly.
//! * [`psc_chain`], [`resultant`], [`discriminant`] — the three things
//!   projection actually calls.
//!
//! The two chain implementations are cross-validated against each other on
//! randomized and hand-built degenerate inputs in the test module: the
//! determinantal one is the oracle, the PRS one is what a caller would use.
//!
//! # Not wired in
//!
//! Nothing in the solve path calls this module yet. It cannot change a verdict.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

// ============================================================================
// Exact-division rings
// ============================================================================

/// A commutative ring with unit in which division is *exact or refused*.
///
/// Every algorithm in this module is fraction-free: the only divisions
/// performed are ones a theorem guarantees to be exact. `exact_div` returning
/// `None` therefore always signals a violated precondition (or an internal
/// bug), never a rounding decision — callers fail closed.
pub(crate) trait ExactRing: Clone + PartialEq + std::fmt::Debug {
    /// The additive identity.
    fn zero() -> Self;
    /// The multiplicative identity.
    fn one() -> Self;
    /// Whether this is the additive identity.
    fn is_zero(&self) -> bool;
    /// Ring addition.
    fn add(&self, other: &Self) -> Self;
    /// Ring subtraction.
    fn sub(&self, other: &Self) -> Self;
    /// Ring multiplication.
    fn mul(&self, other: &Self) -> Self;
    /// Additive inverse.
    fn neg(&self) -> Self;
    /// Exact division: `Some(q)` with `q * other == self`, or `None` when no
    /// such ring element exists (including `other == 0`). Never approximates.
    fn exact_div(&self, other: &Self) -> Option<Self>;

    /// `self^k` by square-and-multiply. `k == 0` yields [`ExactRing::one`].
    fn pow(&self, k: usize) -> Self {
        let mut acc = Self::one();
        let mut base = self.clone();
        let mut e = k;
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        acc
    }
}

impl ExactRing for BigInt {
    fn zero() -> Self {
        <BigInt as Zero>::zero()
    }
    fn one() -> Self {
        <BigInt as One>::one()
    }
    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }
    fn add(&self, other: &Self) -> Self {
        self + other
    }
    fn sub(&self, other: &Self) -> Self {
        self - other
    }
    fn mul(&self, other: &Self) -> Self {
        self * other
    }
    fn neg(&self) -> Self {
        -self
    }
    fn exact_div(&self, other: &Self) -> Option<Self> {
        if Zero::is_zero(other) {
            return None;
        }
        let (q, r) = num_integer::div_rem(self.clone(), other.clone());
        if Zero::is_zero(&r) {
            Some(q)
        } else {
            None
        }
    }
}

// ============================================================================
// Sparse multivariate polynomials over Z (the CAD coefficient ring)
// ============================================================================

/// A variable index in [`MPolyZ`]. Deliberately *not* `TermId`: this layer is
/// pure algebra and must stay independent of the term store so it can be
/// reused by a future CAD projection stage without a term-store round trip.
pub(crate) type MVar = u32;

/// A monomial: variable/exponent pairs sorted strictly ascending by variable,
/// every exponent non-zero. The empty vector is the constant monomial `1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Mono {
    vars: Vec<(MVar, u32)>,
}

impl Mono {
    /// The constant monomial `1`.
    pub(crate) fn one() -> Self {
        Self { vars: Vec::new() }
    }

    /// `x_v^e`. An exponent of zero yields the constant monomial.
    pub(crate) fn var_pow(v: MVar, e: u32) -> Self {
        if e == 0 {
            Self::one()
        } else {
            Self { vars: vec![(v, e)] }
        }
    }

    /// Build from arbitrary `(var, exp)` pairs, merging duplicates and dropping
    /// zero exponents.
    pub(crate) fn from_pairs(mut pairs: Vec<(MVar, u32)>) -> Self {
        pairs.sort_unstable();
        let mut out: Vec<(MVar, u32)> = Vec::with_capacity(pairs.len());
        for (v, e) in pairs {
            if e == 0 {
                continue;
            }
            match out.last_mut() {
                Some(last) if last.0 == v => last.1 += e,
                _ => out.push((v, e)),
            }
        }
        Self { vars: out }
    }

    /// Total degree.
    fn total_degree(&self) -> u32 {
        self.vars.iter().map(|&(_, e)| e).sum()
    }

    /// Product of two monomials.
    fn mul(&self, other: &Self) -> Self {
        let mut out: Vec<(MVar, u32)> = Vec::with_capacity(self.vars.len() + other.vars.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.vars.len() || j < other.vars.len() {
            match (self.vars.get(i), other.vars.get(j)) {
                (Some(&(va, ea)), Some(&(vb, eb))) => {
                    if va < vb {
                        out.push((va, ea));
                        i += 1;
                    } else if va > vb {
                        out.push((vb, eb));
                        j += 1;
                    } else {
                        out.push((va, ea + eb));
                        i += 1;
                        j += 1;
                    }
                }
                (Some(&(va, ea)), None) => {
                    out.push((va, ea));
                    i += 1;
                }
                (None, Some(&(vb, eb))) => {
                    out.push((vb, eb));
                    j += 1;
                }
                (None, None) => unreachable!(),
            }
        }
        Self { vars: out }
    }

    /// Exact monomial division `self / other`, or `None` if `other` does not
    /// divide `self` (some exponent would go negative).
    fn exact_div(&self, other: &Self) -> Option<Self> {
        let mut out: Vec<(MVar, u32)> = Vec::with_capacity(self.vars.len());
        let mut i = 0usize;
        for &(vb, eb) in &other.vars {
            while i < self.vars.len() && self.vars[i].0 < vb {
                out.push(self.vars[i]);
                i += 1;
            }
            let (va, ea) = *self.vars.get(i)?;
            if va != vb || ea < eb {
                return None;
            }
            if ea > eb {
                out.push((va, ea - eb));
            }
            i += 1;
        }
        out.extend_from_slice(&self.vars[i..]);
        Some(Self { vars: out })
    }

    /// Graded lexicographic order: total degree first, then lexicographic on
    /// exponents with the *smallest* variable index most significant.
    fn cmp_grlex(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let (da, db) = (self.total_degree(), other.total_degree());
        if da != db {
            return da.cmp(&db);
        }
        let (mut i, mut j) = (0usize, 0usize);
        loop {
            match (self.vars.get(i), other.vars.get(j)) {
                (None, None) => return Ordering::Equal,
                // Equal total degrees make these unreachable in practice; keep
                // them total anyway so the order is a genuine total order.
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (Some(&(va, ea)), Some(&(vb, eb))) => {
                    if va < vb {
                        return Ordering::Greater;
                    }
                    if va > vb {
                        return Ordering::Less;
                    }
                    if ea != eb {
                        return ea.cmp(&eb);
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
    }
}

/// A sparse multivariate polynomial over `Z`, in canonical form: terms sorted
/// strictly *descending* under graded-lex, every coefficient non-zero. Canonical
/// form makes `PartialEq` structural equality and makes `terms[0]` the leading
/// term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MPolyZ {
    terms: Vec<(Mono, BigInt)>,
}

impl MPolyZ {
    /// The zero polynomial.
    pub(crate) fn zero() -> Self {
        Self { terms: Vec::new() }
    }

    /// A constant polynomial.
    pub(crate) fn constant(c: BigInt) -> Self {
        if Zero::is_zero(&c) {
            Self::zero()
        } else {
            Self {
                terms: vec![(Mono::one(), c)],
            }
        }
    }

    /// A single term `c * m`.
    pub(crate) fn term(m: Mono, c: BigInt) -> Self {
        if Zero::is_zero(&c) {
            Self::zero()
        } else {
            Self {
                terms: vec![(m, c)],
            }
        }
    }

    /// Build from arbitrary terms, combining like monomials and canonicalizing.
    pub(crate) fn from_terms(terms: Vec<(Mono, BigInt)>) -> Self {
        let mut ts = terms;
        ts.sort_by(|a, b| b.0.cmp_grlex(&a.0));
        let mut out: Vec<(Mono, BigInt)> = Vec::with_capacity(ts.len());
        for (m, c) in ts {
            match out.last_mut() {
                Some(last) if last.0 == m => {
                    last.1 += c;
                    if Zero::is_zero(&last.1) {
                        out.pop();
                    }
                }
                _ => {
                    if !Zero::is_zero(&c) {
                        out.push((m, c));
                    }
                }
            }
        }
        Self { terms: out }
    }

    /// The leading `(monomial, coefficient)` under graded-lex, or `None` when
    /// the polynomial is zero.
    fn lead(&self) -> Option<&(Mono, BigInt)> {
        self.terms.first()
    }
}

impl ExactRing for MPolyZ {
    fn zero() -> Self {
        Self::zero()
    }
    fn one() -> Self {
        Self::constant(<BigInt as One>::one())
    }
    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
    fn add(&self, other: &Self) -> Self {
        let mut ts = self.terms.clone();
        ts.extend_from_slice(&other.terms);
        Self::from_terms(ts)
    }
    fn sub(&self, other: &Self) -> Self {
        self.add(&ExactRing::neg(other))
    }
    fn mul(&self, other: &Self) -> Self {
        if self.terms.is_empty() || other.terms.is_empty() {
            return Self::zero();
        }
        let mut ts: Vec<(Mono, BigInt)> = Vec::with_capacity(self.terms.len() * other.terms.len());
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                ts.push((ma.mul(mb), ca * cb));
            }
        }
        Self::from_terms(ts)
    }
    fn neg(&self) -> Self {
        Self {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), -c)).collect(),
        }
    }

    /// Exact multivariate division by repeated leading-term cancellation under
    /// graded-lex. Returns `None` unless `other` divides `self` exactly in
    /// `Z[x]` — in particular integer coefficient divisibility is enforced, so
    /// `(2x) / (4)` refuses rather than producing a rational.
    fn exact_div(&self, other: &Self) -> Option<Self> {
        let (dm, dc) = other.lead()?;
        if self.terms.is_empty() {
            return Some(Self::zero());
        }
        let mut rem = self.clone();
        let mut quot: Vec<(Mono, BigInt)> = Vec::new();
        // Each iteration strictly lowers rem's leading monomial under a
        // well-order, so this terminates.
        while let Some((rm, rc)) = rem.lead() {
            let qm = rm.exact_div(dm)?;
            let qc = ExactRing::exact_div(rc, dc)?;
            let t = Self::term(qm, qc);
            quot.extend_from_slice(&t.terms);
            rem = ExactRing::sub(&rem, &ExactRing::mul(&t, other));
        }
        Some(Self::from_terms(quot))
    }
}

// ============================================================================
// Dense univariate polynomials over an exact ring
// ============================================================================

/// A dense univariate polynomial over `R`, coefficients low-to-high degree,
/// normalized so the top coefficient is non-zero (the zero polynomial has an
/// empty coefficient vector).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct RPoly<R: ExactRing> {
    coeffs: Vec<R>,
}

impl<R: ExactRing> RPoly<R> {
    /// The zero polynomial.
    pub(crate) fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Build from low-to-high coefficients, trimming trailing zeros.
    pub(crate) fn from_coeffs(coeffs: Vec<R>) -> Self {
        let mut c = coeffs;
        while c.last().map(ExactRing::is_zero).unwrap_or(false) {
            c.pop();
        }
        Self { coeffs: c }
    }

    /// Whether this is the zero polynomial.
    pub(crate) fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Degree, or `None` for the zero polynomial.
    pub(crate) fn degree(&self) -> Option<usize> {
        self.coeffs.len().checked_sub(1)
    }

    /// Leading coefficient, or `None` for the zero polynomial.
    pub(crate) fn leading(&self) -> Option<&R> {
        self.coeffs.last()
    }

    /// Coefficient of `x^i` (zero beyond the degree).
    pub(crate) fn coeff(&self, i: usize) -> R {
        self.coeffs.get(i).cloned().unwrap_or_else(R::zero)
    }

    /// Low-to-high coefficient slice.
    pub(crate) fn coeffs(&self) -> &[R] {
        &self.coeffs
    }

    /// Sum.
    pub(crate) fn add(&self, other: &Self) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            out.push(self.coeff(i).add(&other.coeff(i)));
        }
        Self::from_coeffs(out)
    }

    /// Difference.
    pub(crate) fn sub(&self, other: &Self) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            out.push(self.coeff(i).sub(&other.coeff(i)));
        }
        Self::from_coeffs(out)
    }

    /// Additive inverse.
    pub(crate) fn neg(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(ExactRing::neg).collect(),
        }
    }

    /// Product.
    pub(crate) fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut out = vec![R::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.coeffs.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                out[i + j] = out[i + j].add(&a.mul(b));
            }
        }
        Self::from_coeffs(out)
    }

    /// Multiply every coefficient by a ring element.
    pub(crate) fn scale(&self, s: &R) -> Self {
        if s.is_zero() {
            return Self::zero();
        }
        Self::from_coeffs(self.coeffs.iter().map(|c| c.mul(s)).collect())
    }

    /// Divide every coefficient exactly by a ring element; `None` if any
    /// coefficient division is inexact (fail closed).
    pub(crate) fn exact_div_ring(&self, d: &R) -> Option<Self> {
        let mut out = Vec::with_capacity(self.coeffs.len());
        for c in &self.coeffs {
            out.push(c.exact_div(d)?);
        }
        Some(Self::from_coeffs(out))
    }

    /// Multiply by `x^k`.
    pub(crate) fn shift(&self, k: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut out = vec![R::zero(); k];
        out.extend(self.coeffs.iter().cloned());
        Self::from_coeffs(out)
    }

    /// Formal derivative.
    pub(crate) fn derivative(&self) -> Self {
        if self.coeffs.len() < 2 {
            return Self::zero();
        }
        let mut out = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, c) in self.coeffs.iter().enumerate().skip(1) {
            // Multiply by the integer i, realized as repeated addition-free
            // scaling by the ring image of i.
            let mut n = R::zero();
            for _ in 0..i {
                n = n.add(&R::one());
            }
            out.push(c.mul(&n));
        }
        Self::from_coeffs(out)
    }

    /// The **exact pseudo-remainder** `prem(self, b)`: the remainder of
    /// `lc(b)^(deg self - deg b + 1) * self` divided by `b`, computed entirely
    /// inside the ring (no division at all). Matches z3's
    /// `exact_pseudo_remainder`, which always uses the full exponent rather
    /// than the minimal one — the subresultant recurrence depends on that.
    ///
    /// Returns `None` when `b` is zero.
    pub(crate) fn pseudo_rem(&self, b: &Self) -> Option<Self> {
        let db = b.degree()?;
        let Some(da) = self.degree() else {
            return Some(Self::zero());
        };
        if da < db {
            return Some(self.clone());
        }
        let lc_b = b.leading()?.clone();
        let mut r = self.clone();
        // Number of multiplier powers still owed after the loop.
        let mut owed = da - db + 1;
        while let Some(dr) = r.degree() {
            if dr < db {
                break;
            }
            let lc_r = r.leading()?.clone();
            // r <- lc(b)*r - lc(r)*x^(dr-db)*b
            r = r.scale(&lc_b).sub(&b.shift(dr - db).scale(&lc_r));
            owed -= 1;
            // The leading term cancels by construction; assert the degree
            // strictly dropped so the loop is guaranteed to terminate.
            debug_assert!(r.degree().map(|d| d < dr).unwrap_or(true));
        }
        Some(r.scale(&lc_b.pow(owed)))
    }
}

// ============================================================================
// Fraction-free (Bareiss) determinant — the specification's engine
// ============================================================================

/// Determinant of a square matrix over an [`ExactRing`] by the Bareiss
/// fraction-free algorithm.
///
/// Every intermediate entry produced by Bareiss is itself a minor of the input
/// matrix (Sylvester's identity), so the entries stay Hadamard-bounded instead
/// of blowing up the way fraction-field Gaussian elimination does. The only
/// divisions performed are the ones Sylvester's identity guarantees exact;
/// an inexact one returns `None` (fail closed) rather than a wrong determinant.
///
/// `None` also for a non-square or ragged matrix.
pub(crate) fn bareiss_det<R: ExactRing>(matrix: &[Vec<R>]) -> Option<R> {
    let n = matrix.len();
    if n == 0 {
        return Some(R::one());
    }
    if matrix.iter().any(|row| row.len() != n) {
        return None;
    }
    let mut m: Vec<Vec<R>> = matrix.to_vec();
    let mut prev = R::one();
    let mut sign_negative = false;
    for k in 0..n - 1 {
        if m[k][k].is_zero() {
            let Some(pivot) = (k + 1..n).find(|&r| !m[r][k].is_zero()) else {
                // Whole remaining column is zero: the determinant is zero.
                return Some(R::zero());
            };
            m.swap(k, pivot);
            sign_negative = !sign_negative;
        }
        let pivot_val = m[k][k].clone();
        for i in k + 1..n {
            let mik = m[i][k].clone();
            for j in k + 1..n {
                let num = m[i][j].mul(&pivot_val).sub(&mik.mul(&m[k][j]));
                m[i][j] = num.exact_div(&prev)?;
            }
            m[i][k] = R::zero();
        }
        prev = pivot_val;
    }
    let det = m[n - 1][n - 1].clone();
    Some(if sign_negative { det.neg() } else { det })
}

// ============================================================================
// Subresultants: the determinantal specification
// ============================================================================

/// The `j`-th subresultant `S_j(f, g)`, straight from the classical
/// determinantal definition.
///
/// With `m = deg f`, `n = deg g` and `m >= n > j >= 0`, `S_j` is the
/// *determinant polynomial* of the `(m + n - 2j) x (m + n - 2j)` matrix built
/// from the rows
///
/// ```text
///   x^(n-j-1) f, ..., x f, f      (n - j rows)
///   x^(m-j-1) g, ..., x g, g      (m - j rows)
/// ```
///
/// taking as columns the powers `x^(m+n-j-1) .. x^(j+1)` (that is
/// `m + n - 2j - 1` columns) followed by one further column for `x^k`:
///
/// ```text
///   S_j = sum_{k=0}^{j} det(M_{j,k}) * x^k
/// ```
///
/// `S_0` is the resultant. This is `O(j * (m+n)^3)` ring operations per `j` —
/// slower than the PRS below, and used as the oracle the PRS is checked
/// against, but correct by construction with no case analysis to get wrong.
///
/// Returns `None` when `f` or `g` is zero, when `deg f < deg g`, or when
/// `j >= deg g`.
pub(crate) fn subresultant_det<R: ExactRing>(
    f: &RPoly<R>,
    g: &RPoly<R>,
    j: usize,
) -> Option<RPoly<R>> {
    let m = f.degree()?;
    let n = g.degree()?;
    if m < n || j >= n {
        return None;
    }
    let size = m + n - 2 * j;
    // Column `c` of the leading block carries the power x^(m+n-j-1-c).
    let lead_cols = size - 1;
    let mut out: Vec<R> = Vec::with_capacity(j + 1);
    for k in 0..=j {
        let mut mat: Vec<Vec<R>> = Vec::with_capacity(size);
        // Rows x^s * f for s = n-j-1 down to 0.
        for s in (0..n - j).rev() {
            mat.push(shifted_row(f, s, m + n - j - 1, lead_cols, k));
        }
        // Rows x^s * g for s = m-j-1 down to 0.
        for s in (0..m - j).rev() {
            mat.push(shifted_row(g, s, m + n - j - 1, lead_cols, k));
        }
        out.push(bareiss_det(&mat)?);
    }
    Some(RPoly::from_coeffs(out))
}

/// One matrix row for [`subresultant_det`]: the coefficients of `x^s * p` read
/// off at the powers `top, top-1, ..., top-(lead_cols-1)`, followed by the
/// coefficient at `x^k`.
fn shifted_row<R: ExactRing>(
    p: &RPoly<R>,
    s: usize,
    top: usize,
    lead_cols: usize,
    k: usize,
) -> Vec<R> {
    let mut row = Vec::with_capacity(lead_cols + 1);
    for c in 0..lead_cols {
        let power = top - c;
        row.push(if power >= s {
            p.coeff(power - s)
        } else {
            R::zero()
        });
    }
    row.push(if k >= s { p.coeff(k - s) } else { R::zero() });
    row
}

/// The full determinantal chain `[S_0, S_1, ..., S_{n-1}]` where `n = deg g`.
pub(crate) fn subresultant_chain_det<R: ExactRing>(
    f: &RPoly<R>,
    g: &RPoly<R>,
) -> Option<Vec<RPoly<R>>> {
    let n = g.degree()?;
    let mut out = Vec::with_capacity(n);
    for j in 0..n {
        out.push(subresultant_det(f, g, j)?);
    }
    Some(out)
}

// ============================================================================
// Subresultants: the PRS fast path
// ============================================================================

/// The subresultant chain of `f` and `g` in the main variable, computed by the
/// classical subresultant polynomial remainder sequence.
///
/// Returns `chain` with `chain[j] = S_j` for `j` in `0 ..= deg f`, using the
/// standard chain normalization `S_{deg f} = f` and `S_{deg f - 1} = g`
/// (this is the "PSC chain" convention: `R_{deg f} = 1`). For `j <= deg g` the
/// entries coincide with the determinantal subresultants of
/// [`subresultant_chain_det`]; entries above `deg g` are the normalization
/// seeds and carry no separate meaning.
///
/// The recurrence, for a regular step (`deg S_j == j`):
///
/// ```text
///   S_{j-1} = prem(S_{j+1}, S_j) / lc(S_{j+1})^2
/// ```
///
/// and for a defective step (`r = deg S_j < j`):
///
/// ```text
///   S_{j-1} = ... = S_{r+1} = 0
///   S_r     = lc(S_j)^(j-r) * S_j / lc(S_{j+1})^(j-r)
///   S_{r-1} = prem(S_{j+1}, S_j) / (-lc(S_{j+1}))^(j-r+2)      (if r > 0)
/// ```
///
/// All divisions are exact by the subresultant theorem; an inexact one returns
/// `None` (fail closed).
///
/// Preconditions, all enforced with `None`: `f` and `g` non-zero,
/// `deg f > deg g >= 1`. The strict inequality is required — with
/// `deg f == deg g` the very first step is neither regular nor defective and
/// the recurrence has nothing to stand on. That is the same restriction z3's
/// `polynomial.cpp::subresultant_chain` documents ("does not work if
/// deg_p == deg_q"); callers in that situation must use
/// [`subresultant_chain_det`], or reduce `f` modulo `g` first.
pub(crate) fn subresultant_chain_prs<R: ExactRing>(
    f: &RPoly<R>,
    g: &RPoly<R>,
) -> Option<Vec<RPoly<R>>> {
    let n = f.degree()?;
    let dg = g.degree()?;
    if n == 0 || dg == 0 || dg >= n {
        return None;
    }
    let mut s: Vec<RPoly<R>> = vec![RPoly::zero(); n + 1];
    s[n] = f.clone();
    s[n - 1] = g.clone();

    let mut j = n - 1;
    // Each iteration strictly decreases `j`, so this terminates.
    while j > 0 {
        // lc of S_{j+1} at its *nominal* degree j+1. By construction S_{j+1} is
        // regular whenever we get here; at the seed step the chain convention
        // fixes R_n = 1.
        let r_j1 = if j == n - 1 {
            R::one()
        } else {
            s[j + 1].coeff(j + 1)
        };
        if r_j1.is_zero() {
            // S_{j+1} not regular: the recurrence's precondition is broken.
            return None;
        }
        if s[j].is_zero() {
            // gcd reached: every lower subresultant vanishes.
            for slot in s.iter_mut().take(j) {
                *slot = RPoly::zero();
            }
            return Some(s);
        }
        let r = s[j].degree()?;
        if r > j {
            return None; // malformed chain; refuse rather than guess
        }
        if r == j {
            // Regular step.
            let prem = s[j + 1].pseudo_rem(&s[j])?;
            let next = prem.exact_div_ring(&r_j1)?.exact_div_ring(&r_j1)?;
            s[j - 1] = next;
            j -= 1;
        } else {
            // Defective step: a degree gap of j - r.
            let gap = j - r;
            for slot in s.iter_mut().take(j).skip(r + 1) {
                *slot = RPoly::zero();
            }
            let lc_sj = s[j].leading()?.clone();
            let mut s_r = s[j].scale(&lc_sj.pow(gap));
            for _ in 0..gap {
                s_r = s_r.exact_div_ring(&r_j1)?;
            }
            s[r] = s_r;
            if r == 0 {
                return Some(s);
            }
            let prem = s[j + 1].pseudo_rem(&s[j])?;
            let mut s_r1 = prem;
            for _ in 0..gap + 2 {
                s_r1 = s_r1.exact_div_ring(&r_j1)?;
            }
            if (gap + 2) % 2 == 1 {
                s_r1 = s_r1.neg();
            }
            s[r - 1] = s_r1;
            j = r - 1;
        }
    }
    Some(s)
}

/// The **principal subresultant coefficient chain**: `psc_j = coeff(S_j, x^j)`
/// for `j` in `0 .. deg g`, lowest index first.
///
/// This is the primitive every CAD projection operator is written in terms of,
/// and the direct analogue of z3's
/// `polynomial::manager::psc_chain(p, q, x, S)`.
///
/// Uses the PRS when its preconditions hold (`deg f > deg g >= 1`) and falls
/// back to the determinantal definition otherwise, so the caller never has to
/// know which case it is in. Arguments are swapped if `deg f < deg g`;
/// subresultants are symmetric up to a sign that does not affect which psc's
/// vanish, but the swap keeps the *values* equal to `psc_j(max, min)`.
pub(crate) fn psc_chain<R: ExactRing>(f: &RPoly<R>, g: &RPoly<R>) -> Option<Vec<R>> {
    let (p, q) = if f.degree()? >= g.degree()? {
        (f, g)
    } else {
        (g, f)
    };
    let n = q.degree()?;
    if n == 0 {
        return Some(Vec::new());
    }
    if let Some(chain) = subresultant_chain_prs(p, q) {
        return Some((0..n).map(|j| chain[j].coeff(j)).collect());
    }
    let chain = subresultant_chain_det(p, q)?;
    Some((0..n).map(|j| chain[j].coeff(j)).collect())
}

/// The resultant `Res(f, g) = S_0(f, g)`.
///
/// Handles the constant cases exactly: `Res(f, c) = c^deg f` for a non-zero
/// constant `c`, and `Res(f, 0)` is undefined (`None`).
pub(crate) fn resultant<R: ExactRing>(f: &RPoly<R>, g: &RPoly<R>) -> Option<R> {
    let m = f.degree()?;
    let n = g.degree()?;
    if m == 0 && n == 0 {
        return Some(R::one());
    }
    if n == 0 {
        return Some(g.coeff(0).pow(m));
    }
    if m == 0 {
        return Some(f.coeff(0).pow(n));
    }
    // Res(f, g) = (-1)^(mn) Res(g, f); normalize to deg f >= deg g.
    let (p, q, flip) = if m >= n {
        (f, g, false)
    } else {
        (g, f, m * n % 2 == 1)
    };
    let r = if let Some(chain) = subresultant_chain_prs(p, q) {
        chain[0].coeff(0)
    } else {
        subresultant_det(p, q, 0)?.coeff(0)
    };
    Some(if flip { r.neg() } else { r })
}

/// The discriminant `disc(f) = (-1)^(m(m-1)/2) * Res(f, f') / lc(f)`.
///
/// Returns `None` for `deg f < 1`, for a vanishing derivative (characteristic
/// issues cannot arise over `Z` but the check keeps the function total), or if
/// the division by `lc(f)` is not exact in the ring — fail closed, never a
/// rational fallback.
pub(crate) fn discriminant<R: ExactRing>(f: &RPoly<R>) -> Option<R> {
    let m = f.degree()?;
    if m < 1 {
        return None;
    }
    let df = f.derivative();
    if df.is_zero() {
        return None;
    }
    let res = resultant(f, &df)?;
    let quot = res.exact_div(f.leading()?)?;
    let sign_negative = (m * (m - 1) / 2) % 2 == 1;
    Some(if sign_negative { quot.neg() } else { quot })
}

// ============================================================================
// Bridges from the existing rational representations
// ============================================================================

/// Clear denominators from a rational coefficient vector, returning an integer
/// polynomial that is a positive rational multiple of the input.
///
/// Subresultants are *not* invariant under scaling, so this is deliberately not
/// used to compute a "the same" resultant — it is the entry point for callers
/// that own a rational polynomial and want the integer polynomial whose
/// subresultant chain they should be reasoning about. `None` on the zero
/// polynomial.
pub(crate) fn integer_poly_from_rationals(
    coeffs: &[num_rational::BigRational],
) -> Option<RPoly<BigInt>> {
    if coeffs.iter().all(Zero::is_zero) {
        return None;
    }
    let mut lcm = <BigInt as One>::one();
    for c in coeffs {
        let d = c.denom();
        lcm = num_integer::lcm(lcm, d.clone());
    }
    if lcm.is_negative() {
        lcm = -lcm;
    }
    let out: Vec<BigInt> = coeffs
        .iter()
        .map(|c| (c.numer() * &lcm) / c.denom())
        .collect();
    Some(RPoly::from_coeffs(out))
}

#[cfg(test)]
#[path = "subresultant_tests.rs"]
mod tests;

/// Measurement harness backing this module's coefficient-blow-up claim.
///
/// Compares the incumbent [`crate::algebraic::sylvester_det_fixed`] (rational
/// Gaussian elimination) against this module's fraction-free paths on integer
/// polynomials of growing degree, and reports the bit size of the answer so the
/// claim is backed by a number rather than an adjective.
///
/// This is a MEASUREMENT, not a correctness assertion, so it is an
/// `examples/` entry point rather than a `#[test]` — it used to be a `#[test]`
/// carrying `#[ignore]`, which `ay-quality-gate` forbids and which meant it
/// never ran anywhere. It still asserts agreement between the three paths at
/// every degree, so a divergence aborts the run rather than printing a
/// misleading speedup.
///
/// Run: `cargo run --release -p ay-nra --example subresultant_measurement`
#[must_use]
pub fn diag_subresultant_incumbent_versus_fraction_free() -> String {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use std::fmt::Write as _;
    use std::time::Instant;

    // Deterministic PRNG so the reported numbers are reproducible (no `rand`
    // dependency in this crate).
    struct Lcg(u64);
    impl Lcg {
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0 >> 11
        }
        fn next_i64(&mut self, range: i64) -> i64 {
            let span = (2 * range + 1) as u64;
            (self.next_u64() % span) as i64 - range
        }
    }
    fn zp(coeffs: &[i64]) -> RPoly<BigInt> {
        RPoly::from_coeffs(coeffs.iter().map(|&c| BigInt::from(c)).collect())
    }

    let mut rng = Lcg(0x1234_5678_9ABC_DEF0);
    let mut out = String::new();
    let _ = writeln!(
        out,
        "{:>4} {:>14} {:>14} {:>14} {:>10}",
        "deg", "incumbent(us)", "bareiss(us)", "prs(us)", "res bits"
    );
    for deg in [4usize, 6, 8, 10, 12, 14, 16, 20] {
        let mut fc: Vec<i64> = (0..=deg).map(|_| rng.next_i64(1000)).collect();
        let mut gc: Vec<i64> = (0..deg).map(|_| rng.next_i64(1000)).collect();
        if fc[deg] == 0 {
            fc[deg] = 1;
        }
        let last = gc.len() - 1;
        if gc[last] == 0 {
            gc[last] = 1;
        }
        let f_rat: Vec<BigRational> = fc
            .iter()
            .map(|&c| BigRational::from(BigInt::from(c)))
            .collect();
        let g_rat: Vec<BigRational> = gc
            .iter()
            .map(|&c| BigRational::from(BigInt::from(c)))
            .collect();
        let f = zp(&fc);
        let g = zp(&gc);

        let t0 = Instant::now();
        let inc = crate::algebraic::sylvester_det_fixed(&f_rat, &g_rat)
            .expect("incumbent Sylvester determinant is defined for these inputs");
        let t_inc = t0.elapsed().as_micros();

        let t1 = Instant::now();
        let bar = subresultant_det(&f, &g, 0)
            .expect("fraction-free determinant is defined for these inputs")
            .coeff(0);
        let t_bar = t1.elapsed().as_micros();

        let t2 = Instant::now();
        let prs = subresultant_chain_prs(&f, &g)
            .expect("subresultant PRS is defined for these inputs")[0]
            .coeff(0);
        let t_prs = t2.elapsed().as_micros();

        assert_eq!(inc, BigRational::from(bar.clone()), "deg {deg}");
        assert_eq!(bar, prs, "deg {deg}");
        let _ = writeln!(
            out,
            "{:>4} {:>14} {:>14} {:>14} {:>10}",
            deg,
            t_inc,
            t_bar,
            t_prs,
            bar.bits()
        );
    }
    out
}
