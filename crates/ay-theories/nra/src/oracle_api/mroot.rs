// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
