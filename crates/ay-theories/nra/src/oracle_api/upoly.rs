// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
