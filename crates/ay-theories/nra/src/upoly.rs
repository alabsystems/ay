// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dense univariate polynomials over `Z` and over `Z_p`, plus complete
//! factorization over `Z_p` — the `upolynomial` layer that z3's
//! `algebraic_numbers` is built on.
//!
//! # Why this module exists when `univariate.rs` already ships
//!
//! `crates/ay-theories/nra/src/univariate.rs` owns `UniPoly`, a dense
//! univariate over the **rationals**. Measured, its entire polynomial-algebra
//! surface is 184 LOC of `impl UniPoly` plus a handful of free functions:
//! `add`/`sub`/`mul`/`scale`/`eval`/`derivative`/`rem`, a Euclidean
//! `poly_gcd` over `Q`, a `square_free_part`, Sturm sequences and real-root
//! isolation. Everything else in that 5,784-line file is the NRA *solver* —
//! intervals, ICP, cells, linear expressions, PSD matrices.
//!
//! What it does NOT have, and what this module adds:
//!
//!   * A representation over `Z`. `UniPoly` is over `Q`, so it has no notion
//!     of content, primitive part, or a fraction-free division. Every
//!     factorization algorithm needs those.
//!   * Pseudo-division. `UniPoly::rem` divides by the leading coefficient in
//!     `Q`; over `Z` that is not available and `lc(b)^d * a = q*b + r` is the
//!     replacement.
//!   * Square-free **decomposition**. `square_free_part` returns
//!     `p / gcd(p, p')` — the radical, one polynomial, no multiplicities. Yun's
//!     algorithm here returns the full `p = c * prod f_i^i`, which is what a
//!     factorizer consumes.
//!   * A `Z_p` layer of any kind at the univariate level. `polymanager.rs` has
//!     `Z_p` images, but they are *sparse multivariate* images used inside
//!     Brown's modular GCD; there is no dense univariate `Z_p` arithmetic, no
//!     modular inverse, no `x^(p^k) mod f`.
//!   * Factorization. Nothing anywhere in `ay-nra` factors a univariate
//!     polynomial. No distinct-degree, no equal-degree, no irreducibility test.
//!
//! So the overlap with `univariate.rs` is the trivial ring arithmetic, and
//! nothing above it.
//!
//! # Scope, honestly stated
//!
//! Ported: the dense `Z` layer, the dense `Z_p` layer, square-free
//! decomposition on both, and complete factorization over `Z_p`
//! (square-free -> distinct-degree -> equal-degree/Cantor-Zassenhaus), plus an
//! independent Rabin irreducibility test.
//!
//! **Deferred and NOT implemented here**: Hensel lifting to `Z` and the
//! Zassenhaus factor-recombination search. That is deliberate — recombination
//! is where the exponential blow-up lives, and a recombination search that
//! passes correctness tests while trying `2^r` subsets is exactly the
//! "correct-but-exponential" trap. It is better left unbuilt than built
//! unmeasured.
//!
//! # Arithmetic model
//!
//! The `Z` layer is `BigInt` — arbitrary precision, no bounds. The `Z_p` layer
//! is `u64` with the modulus capped at `< 2^31`, so every product `a*b` with
//! `a,b < p` fits in a `u64` without overflow and every operation is exact
//! machine-integer arithmetic. The cap also makes the primality test
//! **deterministic**: Miller-Rabin over the bases `{2,3,5,...,37}` is proven
//! exact for all `n < 3.3 * 10^24`, far above `2^31`. A modulus outside the
//! range, or a composite one, is refused (`None`) rather than guessed at.
//!
//! No `f32`/`f64` appears anywhere in this file.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::cell::Cell;

/// Largest modulus accepted by [`Zp::new`].
///
/// `2^31` keeps `a * b < 2^62` for `a, b < p`, so modular multiplication never
/// overflows `u64`, and keeps every modulus inside the range where the
/// Miller-Rabin base set below is a *proof* of primality rather than a
/// probabilistic test.
pub(crate) const MAX_MODULUS: u64 = 1 << 31;

/// Hard cap on Cantor-Zassenhaus splitting attempts for ONE SPLIT. Each attempt
/// splits with probability `>= 1/2 - 1/(2p^d)`, so 512 consecutive failures on a
/// single split is astronomically unlikely; the cap exists so that a bug can
/// only ever produce `None`, never a hang.
///
/// PER SPLIT, not per call — and that distinction is the whole point. This
/// budget was originally allocated ONCE per `equal_degree` call and threaded
/// through every split, which made it a cap on TOTAL work rather than a
/// liveness guard. A verifier measured what that cost: splitting
/// `prod_{i<n}(x-i)` mod 65537 consumes ~1.5 attempts per split, so from around
/// n = 335 the call ran out and `factor()` DECLINED on ordinary, fully-split
/// input — non-monotonically (340 declined, 350 succeeded, 355 declined,
/// 370/384/512 declined), because whether it fits depends on how lucky the
/// earlier splits were. That is a capability cliff, not a liveness guard.
///
/// Total work stays bounded: `equal_degree` performs at most `n/d` splits, so
/// the call is capped at `512 * n/d` attempts and still cannot hang.
const EDF_ATTEMPT_BUDGET: u64 = 512;

// ---------------------------------------------------------------------------
// Dense univariate over Z
// ---------------------------------------------------------------------------

/// A dense univariate polynomial over `Z`; `c[i]` is the coefficient of `x^i`.
///
/// The zero polynomial is the empty vector. Every constructor normalizes, so a
/// non-zero polynomial always has a non-zero leading coefficient.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ZPoly {
    c: Vec<BigInt>,
}

impl ZPoly {
    pub(crate) fn zero() -> Self {
        Self { c: Vec::new() }
    }

    pub(crate) fn one() -> Self {
        Self {
            c: vec![BigInt::one()],
        }
    }

    /// The monomial `x`.
    pub(crate) fn x() -> Self {
        Self {
            c: vec![BigInt::zero(), BigInt::one()],
        }
    }

    pub(crate) fn constant(v: BigInt) -> Self {
        Self::from_coeffs(vec![v])
    }

    /// `v * x^k`.
    pub(crate) fn monomial(v: BigInt, k: usize) -> Self {
        if v.is_zero() {
            return Self::zero();
        }
        let mut c = vec![BigInt::zero(); k];
        c.push(v);
        Self { c }
    }

    /// Build from low-to-high coefficients, trimming trailing zeros.
    pub(crate) fn from_coeffs(c: Vec<BigInt>) -> Self {
        let mut p = Self { c };
        p.normalize();
        p
    }

    fn normalize(&mut self) {
        while self.c.last().is_some_and(Zero::is_zero) {
            self.c.pop();
        }
    }

    pub(crate) fn coeffs(&self) -> &[BigInt] {
        &self.c
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    /// Degree, or `None` for the zero polynomial. The zero polynomial has no
    /// degree; it does not have degree 0, and conflating the two is how a
    /// division loop turns into an infinite loop.
    pub(crate) fn degree(&self) -> Option<usize> {
        if self.c.is_empty() {
            None
        } else {
            Some(self.c.len() - 1)
        }
    }

    pub(crate) fn lc(&self) -> Option<&BigInt> {
        self.c.last()
    }

    pub(crate) fn eval(&self, at: &BigInt) -> BigInt {
        let mut acc = BigInt::zero();
        for coeff in self.c.iter().rev() {
            acc = acc * at + coeff;
        }
        acc
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let n = self.c.len().max(other.c.len());
        let mut c = Vec::with_capacity(n);
        for i in 0..n {
            let a = self.c.get(i).cloned().unwrap_or_else(BigInt::zero);
            let b = other.c.get(i).cloned().unwrap_or_else(BigInt::zero);
            c.push(a + b);
        }
        Self::from_coeffs(c)
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            c: self.c.iter().map(std::ops::Neg::neg).collect(),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut c = vec![BigInt::zero(); self.c.len() + other.c.len() - 1];
        for (i, a) in self.c.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.c.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                c[i + j] += a * b;
            }
        }
        Self::from_coeffs(c)
    }

    pub(crate) fn scale(&self, s: &BigInt) -> Self {
        if s.is_zero() {
            return Self::zero();
        }
        Self {
            c: self.c.iter().map(|a| a * s).collect(),
        }
    }

    /// Exact division of every coefficient by `s`. `None` if `s` is zero or
    /// does not divide some coefficient exactly.
    pub(crate) fn divide_by_int(&self, s: &BigInt) -> Option<Self> {
        if s.is_zero() {
            return None;
        }
        let mut c = Vec::with_capacity(self.c.len());
        for a in &self.c {
            let (q, r) = a.div_rem(s);
            if !r.is_zero() {
                return None;
            }
            c.push(q);
        }
        Some(Self::from_coeffs(c))
    }

    pub(crate) fn derivative(&self) -> Self {
        if self.c.len() <= 1 {
            return Self::zero();
        }
        let c = self
            .c
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, a)| a * BigInt::from(i))
            .collect();
        Self::from_coeffs(c)
    }

    /// The non-negative GCD of all coefficients. Zero for the zero polynomial.
    pub(crate) fn content(&self) -> BigInt {
        let mut g = BigInt::zero();
        for a in &self.c {
            g = g.gcd(a);
        }
        g.abs()
    }

    /// `p / content(p)`, with the sign left alone. `None` for the zero
    /// polynomial, which has no primitive part.
    pub(crate) fn primitive_part(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        self.divide_by_int(&self.content())
    }

    /// Primitive part normalized to a POSITIVE leading coefficient, together
    /// with the unit-and-content factor `c` such that `self == c * pp`.
    pub(crate) fn split_content(&self) -> Option<(BigInt, Self)> {
        if self.is_zero() {
            return None;
        }
        let mut cont = self.content();
        if self.lc()?.is_negative() {
            cont = -cont;
        }
        let pp = self.divide_by_int(&cont)?;
        Some((cont, pp))
    }

    /// Exact polynomial division. `None` when `den` is zero or does not divide
    /// `num` exactly in `Z[x]` — including the case where it divides in `Q[x]`
    /// but not in `Z[x]`.
    pub(crate) fn exact_div(&self, den: &Self) -> Option<Self> {
        let d_deg = den.degree()?;
        let d_lc = den.lc()?;
        if self.is_zero() {
            return Some(Self::zero());
        }
        let n_deg = self.degree()?;
        if n_deg < d_deg {
            return None;
        }
        let mut r = self.clone();
        let mut q = vec![BigInt::zero(); n_deg - d_deg + 1];
        while let Some(r_deg) = r.degree() {
            if r_deg < d_deg {
                break;
            }
            let (t, rem) = r.lc()?.div_rem(d_lc);
            if !rem.is_zero() {
                return None;
            }
            let shift = r_deg - d_deg;
            q[shift] = t.clone();
            r = r.sub(&den.mul(&Self::monomial(t, shift)));
            // The leading term must have cancelled; if it did not, the
            // subtraction is wrong and the loop would not terminate.
            if r.degree().is_some_and(|d| d >= r_deg) {
                return None;
            }
        }
        if !r.is_zero() {
            return None;
        }
        Some(Self::from_coeffs(q))
    }

    /// Pseudo-division: returns `(d, q, r)` with
    /// `lc(den)^d * self == q*den + r` and `deg(r) < deg(den)`, where
    /// `d == deg(self) - deg(den) + 1` (clamped at 0).
    ///
    /// `None` when `den` is the zero polynomial.
    pub(crate) fn pseudo_div(&self, den: &Self) -> Option<PseudoDiv> {
        let d_deg = den.degree()?;
        let l = den.lc()?.clone();
        let Some(n_deg) = self.degree() else {
            return Some(PseudoDiv {
                d: 0,
                q: Self::zero(),
                r: Self::zero(),
            });
        };
        if n_deg < d_deg {
            return Some(PseudoDiv {
                d: 0,
                q: Self::zero(),
                r: self.clone(),
            });
        }
        let total = n_deg - d_deg + 1;
        let mut e = total;
        let mut q = Self::zero();
        let mut r = self.clone();
        while let Some(r_deg) = r.degree() {
            if r_deg < d_deg {
                break;
            }
            let t = Self::monomial(r.lc()?.clone(), r_deg - d_deg);
            q = q.scale(&l).add(&t);
            r = r.scale(&l).sub(&den.mul(&t));
            e -= 1;
            if r.degree().is_some_and(|d| d >= r_deg) {
                // Leading term failed to cancel: structurally impossible, but
                // fail closed rather than spin.
                return None;
            }
        }
        let mut pow = BigInt::one();
        for _ in 0..e {
            pow *= &l;
        }
        Some(PseudoDiv {
            d: total,
            q: q.scale(&pow),
            r: r.scale(&pow),
        })
    }

    /// GCD over `Z` by the subresultant polynomial remainder sequence
    /// (Cohen, *A Course in Computational Algebraic Number Theory*, 3.3.1),
    /// normalized to a positive leading coefficient.
    ///
    /// `gcd(0, 0)` is the zero polynomial. Otherwise the result is the
    /// primitive GCD scaled by `gcd` of the two contents, i.e. the true GCD in
    /// `Z[x]`.
    pub(crate) fn gcd(&self, other: &Self) -> Option<Self> {
        if self.is_zero() && other.is_zero() {
            return Some(Self::zero());
        }
        if self.is_zero() {
            return Some(other.split_content()?.1.scale(&other.content()));
        }
        if other.is_zero() {
            return Some(self.split_content()?.1.scale(&self.content()));
        }
        let (mut a, mut b) = if self.degree()? >= other.degree()? {
            (self.clone(), other.clone())
        } else {
            (other.clone(), self.clone())
        };
        let ca = a.content();
        let cb = b.content();
        let common = ca.gcd(&cb);
        a = a.divide_by_int(&ca)?;
        b = b.divide_by_int(&cb)?;

        let mut g = BigInt::one();
        let mut h = BigInt::one();
        loop {
            let delta = a.degree()? - b.degree()?;
            let pd = a.pseudo_div(&b)?;
            let r = pd.r;
            if r.is_zero() {
                break;
            }
            if r.degree()? == 0 {
                b = Self::one();
                break;
            }
            a = b;
            // Divide out g * h^delta exactly. A non-exact division here means
            // the subresultant theory has been violated; fail closed.
            let mut divisor = g.clone();
            for _ in 0..delta {
                divisor *= &h;
            }
            b = r.divide_by_int(&divisor)?;
            g = a.lc()?.clone();
            // h <- g^delta / h^(delta-1)
            if delta == 0 {
                // h unchanged
            } else if delta == 1 {
                h = g.clone();
            } else {
                let mut num = BigInt::one();
                for _ in 0..delta {
                    num *= &g;
                }
                let mut den = BigInt::one();
                for _ in 0..(delta - 1) {
                    den *= &h;
                }
                let (qq, rr) = num.div_rem(&den);
                if !rr.is_zero() {
                    return None;
                }
                h = qq;
            }
        }
        let (_, pp) = b.split_content()?;
        Some(pp.scale(&common))
    }

    /// Yun's square-free decomposition over `Z`.
    ///
    /// Returns `(c, [(f_1, 1), (f_2, 2), ...])` with the exact identity
    ///
    /// ```text
    ///     self == c * prod_i f_i^i
    /// ```
    ///
    /// where every `f_i` is primitive, square-free, has positive leading
    /// coefficient, and the `f_i` are pairwise coprime. `c` carries both the
    /// integer content and the sign. Only indices with `deg(f_i) > 0` appear.
    ///
    /// `None` for the zero polynomial (which has no square-free
    /// decomposition) or if any structurally-exact division fails.
    pub(crate) fn square_free_decomposition(&self) -> Option<SqfDecomp> {
        let (c, prim) = self.split_content()?;
        let mut factors: Vec<(Self, usize)> = Vec::new();
        if prim.degree()? == 0 {
            return Some(SqfDecomp { c, factors });
        }
        let dp = prim.derivative();
        let a = prim.gcd(&dp)?;
        let mut b = prim.exact_div(&a)?;
        let cc = dp.exact_div(&a)?;
        let mut d = cc.sub(&b.derivative());
        let mut i = 1usize;
        // Yun's recurrence peels off one multiplicity level per iteration, so a
        // correct run cannot exceed `deg(prim)` levels: no factor of a degree-n
        // polynomial has multiplicity above n.
        //
        // This bound is a LIVENESS guard, and it is the one this module was
        // missing. Every other loop here already fails closed — `exact_div` and
        // `pseudo_div` carry `r.degree() >= r_deg` guards, `Zp::gcd` breaks on
        // `None`, `edf_split` has an attempt budget — but this loop had none. A
        // verifier injected the classic Yun off-by-one (`d = c_next -
        // b.derivative()` instead of `b_next.derivative()`) and it SPUN
        // FOREVER on inputs of the shape (x-a)(x-b)^2(x-c)^3, wedging the fuzz
        // driver past a ten-minute wall with no output. A hang is strictly
        // worse than a decline here: the differential oracle can report a wrong
        // answer and can report a `None`, but it cannot report a process that
        // never returns.
        let max_levels = prim.degree()?;
        loop {
            if i > max_levels {
                return None;
            }
            let ai = b.gcd(&d)?;
            if ai.degree()? > 0 {
                factors.push((ai.clone(), i));
            }
            let b_next = b.exact_div(&ai)?;
            let c_next = d.exact_div(&ai)?;
            d = c_next.sub(&b_next.derivative());
            b = b_next;
            i += 1;
            if b.degree()? == 0 {
                break;
            }
        }
        Some(SqfDecomp { c, factors })
    }
}

/// Result of [`ZPoly::pseudo_div`]: `lc(den)^d * num == q*den + r`.
#[derive(Clone, Debug)]
pub(crate) struct PseudoDiv {
    pub(crate) d: usize,
    pub(crate) q: ZPoly,
    pub(crate) r: ZPoly,
}

/// Result of [`ZPoly::square_free_decomposition`]: `input == c * prod f_i^i`.
#[derive(Clone, Debug)]
pub(crate) struct SqfDecomp {
    pub(crate) c: BigInt,
    pub(crate) factors: Vec<(ZPoly, usize)>,
}

// ---------------------------------------------------------------------------
// Dense univariate over Z_p
// ---------------------------------------------------------------------------

/// A dense univariate polynomial over `Z_p`; `c[i]` is the coefficient of
/// `x^i`, always reduced into `[0, p)`. Zero is the empty vector.
///
/// The modulus is NOT stored here — it lives in the [`Zp`] manager, exactly as
/// z3 keeps it in `upolynomial::zp_manager`. Mixing polynomials from two
/// managers is a caller error the type system does not catch; every entry
/// point that could observe it re-reduces its input.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ZpPoly {
    c: Vec<u64>,
}

impl ZpPoly {
    pub(crate) fn coeffs(&self) -> &[u64] {
        &self.c
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    pub(crate) fn degree(&self) -> Option<usize> {
        if self.c.is_empty() {
            None
        } else {
            Some(self.c.len() - 1)
        }
    }

    pub(crate) fn lc(&self) -> Option<u64> {
        self.c.last().copied()
    }

    fn normalize(&mut self) {
        while self.c.last() == Some(&0) {
            self.c.pop();
        }
    }
}

/// Counters describing how much work a factorization actually did.
///
/// These exist because "the factorization was correct" says nothing about
/// whether it was exponential. Every field is incremented at exactly one call
/// site inside this module.
///
/// They are also, by construction, the kind of stored number a headline metric
/// could be read off while the code beneath it is wrong — so the oracle does
/// not merely print them. `ddf_iters` is re-derived exactly from the returned
/// buckets, and `edf_splits` is pinned to `factors - buckets`; see
/// `crates/ay-nra-oracle/src/upoly.rs`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct FactorStats {
    /// Iterations of the distinct-degree loop.
    pub(crate) ddf_iters: u64,
    /// Random polynomials drawn by equal-degree factorization.
    pub(crate) edf_attempts: u64,
    /// Successful splits performed by equal-degree factorization.
    pub(crate) edf_splits: u64,
    /// Calls to `x^e mod f` (the dominant cost).
    pub(crate) powmods: u64,
    /// Polynomial multiplications performed inside `powmod`.
    pub(crate) powmod_mults: u64,
}

/// Arithmetic in `Z_p[x]` for a fixed prime `p < 2^31`.
#[derive(Debug)]
pub(crate) struct Zp {
    p: u64,
    stats: Cell<FactorStats>,
}

impl Zp {
    /// Build a manager for the prime `p`.
    ///
    /// `None` if `p < 2`, `p >= 2^31`, or `p` is composite. The bound is what
    /// makes both the multiplication and the primality test exact; see
    /// [`MAX_MODULUS`].
    pub(crate) fn new(p: u64) -> Option<Self> {
        if !(2..MAX_MODULUS).contains(&p) || !is_prime_u64(p) {
            return None;
        }
        Some(Self {
            p,
            stats: Cell::new(FactorStats::default()),
        })
    }

    pub(crate) fn p(&self) -> u64 {
        self.p
    }

    pub(crate) fn stats(&self) -> FactorStats {
        self.stats.get()
    }

    pub(crate) fn reset_stats(&self) {
        self.stats.set(FactorStats::default());
    }

    fn bump<F: FnOnce(&mut FactorStats)>(&self, f: F) {
        let mut s = self.stats.get();
        f(&mut s);
        self.stats.set(s);
    }

    // ---- scalar arithmetic ----

    fn norm(&self, a: u64) -> u64 {
        a % self.p
    }

    fn add_s(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p {
            s - self.p
        } else {
            s
        }
    }

    fn sub_s(&self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            a + self.p - b
        }
    }

    fn mul_s(&self, a: u64, b: u64) -> u64 {
        // `p < 2^31` so `a*b < 2^62`: exact in u64, no overflow, no floats.
        (a * b) % self.p
    }

    fn pow_s(&self, mut base: u64, mut e: u64) -> u64 {
        let mut acc = 1 % self.p;
        base %= self.p;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul_s(acc, base);
            }
            base = self.mul_s(base, base);
            e >>= 1;
        }
        acc
    }

    /// Modular inverse. `None` exactly when `p` divides `a` — the degenerate
    /// case a caller must not paper over.
    pub(crate) fn inv_s(&self, a: u64) -> Option<u64> {
        let a = self.norm(a);
        if a == 0 {
            return None;
        }
        // p is prime, so a^(p-2) == a^-1.
        Some(self.pow_s(a, self.p - 2))
    }

    // ---- constructors ----

    pub(crate) fn zero(&self) -> ZpPoly {
        ZpPoly { c: Vec::new() }
    }

    pub(crate) fn one(&self) -> ZpPoly {
        self.from_u64(vec![1])
    }

    pub(crate) fn x(&self) -> ZpPoly {
        self.from_u64(vec![0, 1])
    }

    pub(crate) fn from_u64(&self, c: Vec<u64>) -> ZpPoly {
        let mut q = ZpPoly {
            c: c.into_iter().map(|a| self.norm(a)).collect(),
        };
        q.normalize();
        q
    }

    /// Reduce a `Z` polynomial mod `p`. The degree DROPS when `p` divides the
    /// leading coefficient — that is not an error, but callers that need the
    /// degree preserved must compare it themselves.
    pub(crate) fn reduce(&self, f: &ZPoly) -> ZpPoly {
        let p = BigInt::from(self.p);
        let c = f
            .coeffs()
            .iter()
            .map(|a| {
                let m = a.mod_floor(&p);
                u64::try_from(m).unwrap_or(0)
            })
            .collect();
        self.from_u64(c)
    }

    /// Lift to `Z` with coefficients in `[0, p)`.
    pub(crate) fn lift(&self, f: &ZpPoly) -> ZPoly {
        ZPoly::from_coeffs(f.c.iter().map(|&a| BigInt::from(a)).collect())
    }

    // ---- ring arithmetic ----

    pub(crate) fn add(&self, a: &ZpPoly, b: &ZpPoly) -> ZpPoly {
        let n = a.c.len().max(b.c.len());
        let mut c = Vec::with_capacity(n);
        for i in 0..n {
            c.push(self.add_s(
                a.c.get(i).copied().unwrap_or(0),
                b.c.get(i).copied().unwrap_or(0),
            ));
        }
        let mut q = ZpPoly { c };
        q.normalize();
        q
    }

    pub(crate) fn sub(&self, a: &ZpPoly, b: &ZpPoly) -> ZpPoly {
        let n = a.c.len().max(b.c.len());
        let mut c = Vec::with_capacity(n);
        for i in 0..n {
            c.push(self.sub_s(
                a.c.get(i).copied().unwrap_or(0),
                b.c.get(i).copied().unwrap_or(0),
            ));
        }
        let mut q = ZpPoly { c };
        q.normalize();
        q
    }

    pub(crate) fn mul(&self, a: &ZpPoly, b: &ZpPoly) -> ZpPoly {
        if a.is_zero() || b.is_zero() {
            return self.zero();
        }
        let mut c = vec![0u64; a.c.len() + b.c.len() - 1];
        for (i, &x) in a.c.iter().enumerate() {
            if x == 0 {
                continue;
            }
            for (j, &y) in b.c.iter().enumerate() {
                if y == 0 {
                    continue;
                }
                c[i + j] = self.add_s(c[i + j], self.mul_s(x, y));
            }
        }
        let mut q = ZpPoly { c };
        q.normalize();
        q
    }

    pub(crate) fn scale(&self, a: &ZpPoly, s: u64) -> ZpPoly {
        let s = self.norm(s);
        if s == 0 {
            return self.zero();
        }
        let mut q = ZpPoly {
            c: a.c.iter().map(|&x| self.mul_s(x, s)).collect(),
        };
        q.normalize();
        q
    }

    pub(crate) fn derivative(&self, a: &ZpPoly) -> ZpPoly {
        if a.c.len() <= 1 {
            return self.zero();
        }
        let c =
            a.c.iter()
                .enumerate()
                .skip(1)
                .map(|(i, &x)| self.mul_s(x, self.norm(u64::try_from(i).unwrap_or(0))))
                .collect();
        let mut q = ZpPoly { c };
        q.normalize();
        q
    }

    /// Division with remainder. `None` when `b` is zero.
    pub(crate) fn div_rem(&self, a: &ZpPoly, b: &ZpPoly) -> Option<(ZpPoly, ZpPoly)> {
        let b_deg = b.degree()?;
        let inv_lc = self.inv_s(b.lc()?)?;
        if a.is_zero() {
            return Some((self.zero(), self.zero()));
        }
        let a_deg = a.degree()?;
        if a_deg < b_deg {
            return Some((self.zero(), a.clone()));
        }
        let mut r = a.c.clone();
        let mut q = vec![0u64; a_deg - b_deg + 1];
        for shift in (0..=a_deg - b_deg).rev() {
            let top = r[shift + b_deg];
            if top == 0 {
                continue;
            }
            let t = self.mul_s(top, inv_lc);
            q[shift] = t;
            for (j, &bj) in b.c.iter().enumerate() {
                r[shift + j] = self.sub_s(r[shift + j], self.mul_s(t, bj));
            }
        }
        let mut rem = ZpPoly { c: r };
        rem.normalize();
        let mut quot = ZpPoly { c: q };
        quot.normalize();
        Some((quot, rem))
    }

    pub(crate) fn rem(&self, a: &ZpPoly, b: &ZpPoly) -> Option<ZpPoly> {
        Some(self.div_rem(a, b)?.1)
    }

    /// Exact division; `None` if the remainder is non-zero or `b` is zero.
    pub(crate) fn exact_div(&self, a: &ZpPoly, b: &ZpPoly) -> Option<ZpPoly> {
        let (q, r) = self.div_rem(a, b)?;
        if r.is_zero() {
            Some(q)
        } else {
            None
        }
    }

    /// `(lc, monic)` with `a == lc * monic`. `None` for the zero polynomial.
    pub(crate) fn monic(&self, a: &ZpPoly) -> Option<(u64, ZpPoly)> {
        let lc = a.lc()?;
        let inv = self.inv_s(lc)?;
        Some((lc, self.scale(a, inv)))
    }

    /// Monic GCD. `gcd(0,0)` is zero; otherwise the result is monic.
    pub(crate) fn gcd(&self, a: &ZpPoly, b: &ZpPoly) -> ZpPoly {
        let mut x = a.clone();
        let mut y = b.clone();
        while !y.is_zero() {
            match self.rem(&x, &y) {
                Some(r) => {
                    x = y;
                    y = r;
                }
                // `y` is non-zero here, so `rem` cannot fail; if it somehow
                // does, stop rather than spin.
                None => break,
            }
        }
        if x.is_zero() {
            return x;
        }
        self.monic(&x).map_or_else(|| self.zero(), |(_, m)| m)
    }

    /// `base^e mod m`, by square-and-multiply over the bits of `e`.
    ///
    /// `None` when `m` is zero or constant (there is no meaningful residue
    /// ring) — a degenerate case every caller must have excluded.
    pub(crate) fn powmod(&self, base: &ZpPoly, e: &BigInt, m: &ZpPoly) -> Option<ZpPoly> {
        if m.degree()? == 0 {
            return None;
        }
        if e.is_negative() {
            return None;
        }
        self.bump(|s| s.powmods += 1);
        let mut acc = self.one();
        let mut b = self.rem(base, m)?;
        let bits = e.bits();
        for i in 0..bits {
            if e.bit(i) {
                acc = self.rem(&self.mul(&acc, &b), m)?;
                self.bump(|s| s.powmod_mults += 1);
            }
            if i + 1 < bits {
                b = self.rem(&self.mul(&b, &b), m)?;
                self.bump(|s| s.powmod_mults += 1);
            }
        }
        Some(acc)
    }

    /// The `p`-th root of a polynomial all of whose exponents are multiples of
    /// `p`. In `F_p` the Frobenius map is the identity on coefficients, so this
    /// is purely an exponent contraction.
    ///
    /// `None` if some exponent is not a multiple of `p` — i.e. the input was
    /// not a `p`-th power, which means the caller's case analysis was wrong.
    pub(crate) fn p_th_root(&self, a: &ZpPoly) -> Option<ZpPoly> {
        let p = usize::try_from(self.p).ok()?;
        let mut c = Vec::new();
        for (i, &v) in a.c.iter().enumerate() {
            if i % p == 0 {
                c.push(v);
            } else if v != 0 {
                return None;
            }
        }
        let mut q = ZpPoly { c };
        q.normalize();
        Some(q)
    }

    /// Square-free decomposition over `Z_p` of a MONIC polynomial.
    ///
    /// Returns `[(g_i, m_i)]` with `a == prod g_i^{m_i}`, every `g_i` monic,
    /// square-free, of degree `>= 1`, and pairwise coprime.
    ///
    /// Handles the characteristic-`p` degenerate case explicitly: when `a' == 0`
    /// the polynomial is a `p`-th power (`x^p + 1` is the smallest example) and
    /// the whole decomposition recurses on its `p`-th root with every
    /// multiplicity scaled by `p`. Getting that branch wrong is the classic
    /// square-free-over-`F_p` bug; it is why `a' == 0` is not treated as
    /// "already square-free".
    pub(crate) fn square_free_decomposition(&self, a: &ZpPoly) -> Option<Vec<(ZpPoly, usize)>> {
        if a.is_zero() {
            return None;
        }
        if a.lc()? != 1 {
            return None;
        }
        let mut out = Vec::new();
        self.sqf_rec(a, 1, &mut out)?;
        // Deterministic order: ascending multiplicity, then the polynomial
        // itself. Matches the `Z` layer, where Yun produces the multiplicities
        // in ascending order by construction.
        out.sort_by(|x, y| (x.1, &x.0).cmp(&(y.1, &y.0)));
        Some(out)
    }

    fn sqf_rec(&self, a: &ZpPoly, scale: usize, out: &mut Vec<(ZpPoly, usize)>) -> Option<()> {
        if a.degree()? == 0 {
            return Some(());
        }
        let da = self.derivative(a);
        if da.is_zero() {
            // `a` is a p-th power.
            let root = self.p_th_root(a)?;
            let next = scale.checked_mul(usize::try_from(self.p).ok()?)?;
            return self.sqf_rec(&root, next, out);
        }
        let mut c = self.gcd(a, &da);
        let mut w = self.exact_div(a, &c)?;
        let mut i = 1usize;
        while w.degree()? > 0 {
            let y = self.gcd(&w, &c);
            let z = self.exact_div(&w, &y)?;
            if z.degree()? > 0 {
                out.push((z, i.checked_mul(scale)?));
            }
            c = self.exact_div(&c, &y)?;
            w = y;
            i += 1;
        }
        if c.degree()? > 0 {
            // Whatever survives is a p-th power.
            let root = self.p_th_root(&c)?;
            let next = scale.checked_mul(usize::try_from(self.p).ok()?)?;
            self.sqf_rec(&root, next, out)?;
        }
        Some(())
    }

    /// Distinct-degree factorization of a MONIC SQUARE-FREE polynomial.
    ///
    /// Returns `[(g_d, d)]` where `g_d` is the product of all the monic
    /// irreducible factors of `a` of degree exactly `d`, and `prod g_d == a`.
    ///
    /// Refuses (`None`) a non-square-free input rather than returning a wrong
    /// answer for it: the whole method rests on `x^(p^d) - x` being square-free,
    /// which is false for a repeated factor.
    pub(crate) fn distinct_degree(&self, a: &ZpPoly) -> Option<Vec<(ZpPoly, usize)>> {
        let n = a.degree()?;
        if a.lc()? != 1 {
            return None;
        }
        if n == 0 {
            return Some(Vec::new());
        }
        let da = self.derivative(a);
        if da.is_zero() || self.gcd(a, &da).degree()? != 0 {
            return None;
        }
        let mut out = Vec::new();
        let mut fstar = a.clone();
        let mut h = self.x();
        let xp = self.x();
        let pbig = BigInt::from(self.p);
        let mut i = 1usize;
        while fstar.degree().unwrap_or(0) >= 2 * i {
            self.bump(|s| s.ddf_iters += 1);
            h = self.powmod(&h, &pbig, &fstar)?;
            let g = self.gcd(&self.sub(&h, &xp), &fstar);
            if g.degree()? > 0 {
                out.push((g.clone(), i));
                fstar = self.exact_div(&fstar, &g)?;
                // NOTE: z3 re-reduces `h` against the shrunken `f*` here. That
                // statement is REDUNDANT in this implementation and has been
                // removed rather than left as code the oracle cannot see:
                // [`Zp::powmod`] reduces its base before the first squaring, so
                // the next iteration normalizes `h` anyway. Deleting the
                // re-reduction was injected as a defect and produced ZERO
                // divergences over 2,700 oracle cases — which is the correct
                // outcome for a no-op, and is recorded here so that nobody
                // re-adds it believing it does something.
            }
            i += 1;
        }
        let d = fstar.degree()?;
        if d > 0 {
            out.push((fstar, d));
        }
        Some(out)
    }

    /// Equal-degree (Cantor-Zassenhaus) factorization: split a monic
    /// square-free `a` all of whose irreducible factors have degree exactly
    /// `d` into those factors.
    ///
    /// The randomness is drawn from a DETERMINISTIC generator seeded from the
    /// input, so the same polynomial always factors along the same path and a
    /// failing case reproduces. `None` if `d` does not divide `deg(a)`, or if
    /// the attempt budget is exhausted — never a hang, never a guess.
    pub(crate) fn equal_degree(&self, a: &ZpPoly, d: usize) -> Option<Vec<ZpPoly>> {
        let n = a.degree()?;
        if d == 0 || n % d != 0 || a.lc()? != 1 {
            return None;
        }
        let mut rng = DetRng::seeded(self.p, &a.c);
        let mut out = Vec::new();
        let mut stack = vec![a.clone()];
        while let Some(cur) = stack.pop() {
            let m = cur.degree()?;
            if m == d {
                out.push(cur);
                continue;
            }
            // A fresh budget PER SPLIT. See `EDF_ATTEMPT_BUDGET`: sharing one
            // budget across the whole call turned a liveness guard into a cap
            // on total work, and made `factor()` decline on ordinary input from
            // around degree 335.
            let mut budget = EDF_ATTEMPT_BUDGET;
            let g = self.edf_split(&cur, d, m, &mut rng, &mut budget)?;
            let other = self.exact_div(&cur, &g)?;
            self.bump(|s| s.edf_splits += 1);
            stack.push(g);
            stack.push(other);
        }
        out.sort();
        Some(out)
    }

    /// One non-trivial splitting factor of `cur`, or `None` if the budget ran
    /// out.
    fn edf_split(
        &self,
        cur: &ZpPoly,
        d: usize,
        m: usize,
        rng: &mut DetRng,
        budget: &mut u64,
    ) -> Option<ZpPoly> {
        while *budget > 0 {
            *budget -= 1;
            self.bump(|s| s.edf_attempts += 1);
            let a = self.random_below(rng, m);
            if a.degree().unwrap_or(0) < 1 {
                continue;
            }
            // A lucky non-trivial gcd splits immediately.
            let g = self.gcd(&a, cur);
            let gd = g.degree().unwrap_or(0);
            if gd > 0 && gd < m {
                return Some(g);
            }
            let cand = if self.p == 2 {
                // `(p^d - 1)/2` is not an integer in characteristic 2; the
                // trace map `a + a^2 + ... + a^(2^(d-1))` replaces it.
                self.trace_map(&a, d, cur)?
            } else {
                // b = a^((p^d - 1)/2) mod cur; b-1 catches the factors where
                // `a` is a quadratic residue.
                let e = (BigInt::from(self.p).pow(u32::try_from(d).ok()?) - BigInt::one()) / 2;
                let b = self.powmod(&a, &e, cur)?;
                self.sub(&b, &self.one())
            };
            let g2 = self.gcd(&cand, cur);
            let g2d = g2.degree().unwrap_or(0);
            if g2d > 0 && g2d < m {
                return Some(g2);
            }
        }
        None
    }

    /// `a + a^2 + a^4 + ... + a^(2^(d-1)) mod m`, for `p == 2`.
    fn trace_map(&self, a: &ZpPoly, d: usize, m: &ZpPoly) -> Option<ZpPoly> {
        let mut t = self.rem(a, m)?;
        let mut acc = t.clone();
        for _ in 1..d {
            t = self.rem(&self.mul(&t, &t), m)?;
            acc = self.add(&acc, &t);
        }
        Some(acc)
    }

    fn random_below(&self, rng: &mut DetRng, m: usize) -> ZpPoly {
        let c = (0..m).map(|_| rng.below(self.p)).collect();
        self.from_u64(c)
    }

    /// Complete factorization over `Z_p`.
    ///
    /// Returns `lc` and `[(f_i, e_i)]` with every `f_i` monic irreducible,
    /// pairwise distinct, and the EXACT identity
    ///
    /// ```text
    ///     a == lc * prod_i f_i^{e_i}
    /// ```
    ///
    /// `None` for the zero polynomial. A non-zero constant factors as itself
    /// with an empty factor list.
    pub(crate) fn factor(&self, a: &ZpPoly) -> Option<ZpFactorization> {
        if a.is_zero() {
            return None;
        }
        let lc = a.lc()?;
        if a.degree()? == 0 {
            return Some(ZpFactorization {
                lc,
                factors: Vec::new(),
            });
        }
        let (_, monic) = self.monic(a)?;
        let mut factors: Vec<(ZpPoly, usize)> = Vec::new();
        for (g, mult) in self.square_free_decomposition(&monic)? {
            for (bucket, d) in self.distinct_degree(&g)? {
                for irr in self.equal_degree(&bucket, d)? {
                    factors.push((irr, mult));
                }
            }
        }
        factors.sort();
        Some(ZpFactorization { lc, factors })
    }

    /// Rabin's irreducibility test for a MONIC polynomial over `Z_p`.
    ///
    /// `a` of degree `n >= 1` is irreducible iff `x^(p^n) == x (mod a)` and
    /// `gcd(x^(p^(n/q)) - x, a) == 1` for every prime `q | n`.
    ///
    /// This shares `powmod`, `rem` and `gcd` with the factorizer but shares
    /// NONE of its control flow — no square-free split, no distinct-degree
    /// loop, no Cantor-Zassenhaus. It is the independent witness the oracle
    /// uses to confirm that every returned factor really is irreducible.
    pub(crate) fn is_irreducible(&self, a: &ZpPoly) -> Option<bool> {
        let n = a.degree()?;
        if n == 0 || a.lc()? != 1 {
            return None;
        }
        if n == 1 {
            return Some(true);
        }
        let xp = self.x();
        let pbig = BigInt::from(self.p);
        let frob = |k: usize| -> Option<ZpPoly> {
            let mut h = self.x();
            for _ in 0..k {
                h = self.powmod(&h, &pbig, a)?;
            }
            Some(h)
        };
        if frob(n)? != xp {
            return Some(false);
        }
        for q in distinct_prime_divisors(n) {
            let h = frob(n / q)?;
            if self.gcd(&self.sub(&h, &xp), a).degree()? != 0 {
                return Some(false);
            }
        }
        Some(true)
    }
}

/// Result of [`Zp::factor`]: `input == lc * prod f_i^{e_i}`.
#[derive(Clone, Debug)]
pub(crate) struct ZpFactorization {
    pub(crate) lc: u64,
    pub(crate) factors: Vec<(ZpPoly, usize)>,
}

// ---------------------------------------------------------------------------
// Support
// ---------------------------------------------------------------------------

/// Deterministic xorshift used by equal-degree factorization.
///
/// Cantor-Zassenhaus is a randomized algorithm; a solver that used a real RNG
/// would not be reproducible, and a differential oracle could not replay a
/// divergence. Seeding from the input makes the whole factorization a pure
/// function of the polynomial.
struct DetRng {
    s: u64,
}

impl DetRng {
    fn seeded(p: u64, coeffs: &[u64]) -> Self {
        let mut h = 0x9E37_79B9_7F4A_7C15u64 ^ p.wrapping_mul(0x0100_0000_01B3);
        for &c in coeffs {
            h ^= c.wrapping_add(0x9E37_79B9_7F4A_7C15);
            h = h.rotate_left(27).wrapping_mul(0x94D0_49BB_1331_11EB);
        }
        Self { s: h | 1 }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.s;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.s = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next_u64() % n
        }
    }
}

include!("upoly/primality.rs");
