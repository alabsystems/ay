// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
