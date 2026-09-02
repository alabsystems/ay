// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `sos.rs` to keep certificate polynomial helpers in
// the NIA SOS checker's private namespace.

fn zero() -> BigRational {
    BigRational::zero()
}
fn one() -> BigRational {
    BigRational::one()
}

/// Orient a single constraint `p ⋈ 0` to a `g ⋈ 0` normal form with `g ≥ 0`,
/// `g > 0`, or `g = 0`. Returns `None` for `≠` atoms (a disjunction, not a
/// single nonnegative/zero atom).
pub(crate) fn orient(c: &MultiConstraint) -> Option<(MultiPoly, OrientedKind)> {
    match c.rel {
        Rel::Ge => Some((c.poly.clone(), OrientedKind::Ge)),
        Rel::Gt => Some((c.poly.clone(), OrientedKind::Gt)),
        Rel::Le => Some((c.poly.neg(), OrientedKind::Ge)),
        Rel::Lt => Some((c.poly.neg(), OrientedKind::Gt)),
        Rel::Eq => Some((c.poly.clone(), OrientedKind::Eq)),
        Rel::Ne => None,
    }
}

/// Re-derive a certificate term's oriented polynomial and kind from the original
/// constraints (used by the independent checker).
fn derive_oriented(
    origin: CertOrigin,
    constraints: &[MultiConstraint],
    budget: &mut SosPolynomialBudget,
) -> Result<(MultiPoly, OrientedKind), SosError> {
    match origin {
        CertOrigin::Constraint(i) => {
            let c = constraints.get(i).ok_or(SosError::BadConstraintIndex)?;
            orient(c).ok_or(SosError::NotOrientable)
        }
        CertOrigin::Product(i, j) => {
            let ci = constraints.get(i).ok_or(SosError::BadConstraintIndex)?;
            let cj = constraints.get(j).ok_or(SosError::BadConstraintIndex)?;
            let (gi, ki) = orient(ci).ok_or(SosError::NotOrientable)?;
            let (gj, kj) = orient(cj).ok_or(SosError::NotOrientable)?;
            if !ki.is_inequality()
                || !kj.is_inequality()
                || poly_degree(&gi) > 1
                || poly_degree(&gj) > 1
            {
                return Err(SosError::NotOrientable);
            }
            let kind = if ki.is_strict() && kj.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            let product = checked_poly_mul(&gi, &gj, budget).ok_or(SosError::ResourceLimit)?;
            Ok((product, kind))
        }
    }
}

/// The monomial `basis[a] · basis[b]` as a sorted `Vec<TermId>`.
fn mono_product(a: &[TermId], b: &[TermId]) -> Vec<TermId> {
    let mut m = Vec::with_capacity(a.len() + b.len());
    m.extend_from_slice(a);
    m.extend_from_slice(b);
    m.sort_unstable();
    m
}

/// Scale every coefficient of a polynomial by a rational.
fn scale(
    p: &MultiPoly,
    k: &BigRational,
    budget: &mut SosPolynomialBudget,
) -> Result<MultiPoly, SosError> {
    if k.is_zero() {
        return Ok(MultiPoly::zero());
    }
    let mut out = MultiPoly::zero();
    for (m, c) in &p.terms {
        let term = MultiPoly {
            terms: vec![(m.clone(), c * k)],
        };
        out = checked_poly_add(&out, &term, budget).ok_or(SosError::ResourceLimit)?;
    }
    Ok(out)
}

/// Expand `σ0 = basisᵀ Q basis` into a [`MultiPoly`].
fn sigma0_poly(
    basis: &[Vec<TermId>],
    gram: &[Vec<BigRational>],
    budget: &mut SosPolynomialBudget,
) -> Result<MultiPoly, SosError> {
    let mut out = MultiPoly::zero();
    for (a, ba) in basis.iter().enumerate() {
        for (b, bb) in basis.iter().enumerate() {
            let q = &gram[a][b];
            if q.is_zero() {
                continue;
            }
            let term = MultiPoly {
                terms: vec![(mono_product(ba, bb), q.clone())],
            };
            out = checked_poly_add(&out, &term, budget).ok_or(SosError::ResourceLimit)?;
        }
    }
    Ok(out)
}
