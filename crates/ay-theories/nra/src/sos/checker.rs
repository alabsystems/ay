// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent bounded exact-rational certificate replay.

use super::budget::{
    checked_poly_add, checked_poly_mul, checked_poly_sub, polynomial_fits, rational_fits,
    SosLpBudget, SosPolynomialBudget, SosProgress, MAX_SOS_ASSERTED_LITERALS,
    MAX_SOS_TOTAL_POLY_TERMS,
};
use super::lp::{lp_div, lp_mul, lp_sub};
use super::*;

/// Validate already-expanded source polynomials before cloning or arithmetic.
pub(super) fn source_fits(
    constraints: &[MultiConstraint],
    vars: Option<&[TermId]>,
    budget: &mut SosPolynomialBudget<'_>,
) -> bool {
    if constraints.len() > MAX_SOS_ASSERTED_LITERALS || !budget.charge(constraints.len(), 0) {
        return false;
    }
    let Some(terms) = constraints.iter().try_fold(0usize, |total, constraint| {
        total.checked_add(constraint.poly.terms.len())
    }) else {
        return false;
    };
    terms <= MAX_SOS_TOTAL_POLY_TERMS
        && budget.charge(
            terms * budget::MAX_SOS_POLY_DEGREE * (budget::MAX_SOS_POLY_TERMS + MAX_VARS + 4),
            0,
        )
        && constraints
            .iter()
            .all(|constraint| polynomial_fits(&constraint.poly, vars))
}

fn check_inputs(
    cert: &SosCertificate,
    constraints: &[MultiConstraint],
    budget: &mut SosPolynomialBudget<'_>,
) -> Result<(), SosError> {
    if !budget.poll() {
        return Err(SosError::ResourceLimit);
    }
    if cert.basis.len() > MAX_BASIS || cert.terms.len() > MAX_LP_COLS {
        return Err(SosError::ResourceLimit);
    }
    let n = cert.basis.len();
    if cert.gram.len() != n || cert.gram.iter().any(|row| row.len() != n) {
        return Err(SosError::GramShape);
    }
    if !budget.charge(n * n + cert.terms.len() + 1, 0)
        || !source_fits(constraints, None, budget)
        || !rational_fits(&cert.rhs)
        || !cert.gram.iter().flatten().all(rational_fits)
        || !cert
            .terms
            .iter()
            .all(|term| rational_fits(&term.multiplier))
    {
        return Err(SosError::ResourceLimit);
    }
    if !budget.charge_array::<TermId>(MAX_VARS) {
        return Err(SosError::ResourceLimit);
    }
    let mut vars = Vec::with_capacity(MAX_VARS);
    for var in constraints
        .iter()
        .flat_map(|constraint| &constraint.poly.terms)
        .flat_map(|(monomial, _)| monomial)
    {
        if !budget.charge(MAX_VARS, 0) {
            return Err(SosError::ResourceLimit);
        }
        if !vars.contains(var) {
            if vars.len() == MAX_VARS {
                return Err(SosError::ResourceLimit);
            }
            vars.push(*var);
        }
    }
    if cert
        .basis
        .first()
        .is_none_or(|monomial| !monomial.is_empty())
        || cert.basis.iter().enumerate().any(|(index, monomial)| {
            monomial.len() > 2
                || monomial
                    .windows(2)
                    .any(|pair| matches!(pair, [left, right] if left > right))
                || monomial.iter().any(|var| !vars.contains(var))
                || cert
                    .basis
                    .get(..index)
                    .is_some_and(|prior| prior.contains(monomial))
        })
    {
        return Err(SosError::InvalidBasis);
    }
    Ok(())
}

/// Exact Schur-complement PSD check; zero pivots require an all-zero tail.
#[allow(clippy::needless_range_loop)] // Matrix indices denote pivot/row/column identities.
fn is_psd_bounded(
    matrix: &[Vec<BigRational>],
    budget: &mut SosLpBudget<'_>,
) -> Result<bool, SosError> {
    let n = matrix.len();
    if n > MAX_BASIS {
        return Err(SosError::ResourceLimit);
    }
    if matrix.iter().any(|row| row.len() != n) {
        return Ok(false);
    }
    if !matrix.iter().flatten().all(rational_fits) {
        return Err(SosError::ResourceLimit);
    }
    if !budget.charge_array::<Vec<BigRational>>(n) || !budget.charge_array::<BigRational>(n * n) {
        return Err(SosError::ResourceLimit);
    }
    for coefficient in matrix.iter().flatten() {
        if !budget.charge_rational_clone(coefficient) {
            return Err(SosError::ResourceLimit);
        }
    }
    let mut work = matrix.to_vec();
    for pivot_index in 0..n {
        if !budget.charge_rational_clone(&work[pivot_index][pivot_index]) {
            return Err(SosError::ResourceLimit);
        }
        let pivot = work[pivot_index][pivot_index].clone();
        if pivot.is_negative() {
            return Ok(false);
        }
        if pivot.is_zero() {
            if !budget.charge(n - pivot_index, 0) {
                return Err(SosError::ResourceLimit);
            }
            if ((pivot_index + 1)..n).any(|index| {
                !work[pivot_index][index].is_zero() || !work[index][pivot_index].is_zero()
            }) {
                return Ok(false);
            }
            continue;
        }
        for row in (pivot_index + 1)..n {
            if !budget.charge(1, 0) {
                return Err(SosError::ResourceLimit);
            }
            if work[row][pivot_index].is_zero() {
                continue;
            }
            let factor =
                lp_div(&work[row][pivot_index], &pivot, budget).ok_or(SosError::ResourceLimit)?;
            for column in (pivot_index + 1)..n {
                let delta = lp_mul(&factor, &work[pivot_index][column], budget)
                    .ok_or(SosError::ResourceLimit)?;
                work[row][column] =
                    lp_sub(&work[row][column], &delta, budget).ok_or(SosError::ResourceLimit)?;
            }
        }
    }
    budget.poll().then_some(true).ok_or(SosError::ResourceLimit)
}

#[cfg(test)]
pub(super) fn is_psd(matrix: &[Vec<BigRational>]) -> bool {
    is_psd_bounded(matrix, &mut SosLpBudget::default()).unwrap_or(false)
}

fn derive_oriented(
    origin: CertOrigin,
    constraints: &[MultiConstraint],
    budget: &mut SosPolynomialBudget<'_>,
) -> Result<(MultiPoly, OrientedKind), SosError> {
    match origin {
        CertOrigin::Constraint(index) => {
            let source = constraints.get(index).ok_or(SosError::BadConstraintIndex)?;
            if !budget.charge_polynomial(&source.poly) {
                return Err(SosError::ResourceLimit);
            }
            orient(source).ok_or(SosError::NotOrientable)
        }
        CertOrigin::Product(left, right) => {
            let left = constraints.get(left).ok_or(SosError::BadConstraintIndex)?;
            let right = constraints.get(right).ok_or(SosError::BadConstraintIndex)?;
            if !budget.charge_polynomial(&left.poly) || !budget.charge_polynomial(&right.poly) {
                return Err(SosError::ResourceLimit);
            }
            let (left, left_kind) = orient(left).ok_or(SosError::NotOrientable)?;
            let (right, right_kind) = orient(right).ok_or(SosError::NotOrientable)?;
            if !left_kind.is_inequality()
                || !right_kind.is_inequality()
                || poly_degree(&left)
                    .checked_add(poly_degree(&right))
                    .is_none_or(|total| total > 4)
            {
                return Err(SosError::NotOrientable);
            }
            let kind = if left_kind.is_strict() && right_kind.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            let product = checked_poly_mul(&left, &right, budget).ok_or(SosError::ResourceLimit)?;
            Ok((product, kind))
        }
    }
}

fn sigma0_poly(
    cert: &SosCertificate,
    budget: &mut SosPolynomialBudget<'_>,
) -> Result<MultiPoly, SosError> {
    let mut result = MultiPoly::zero();
    for (row, left) in cert.basis.iter().enumerate() {
        for (column, right) in cert.basis.iter().enumerate() {
            if !budget.charge(1, 0) {
                return Err(SosError::ResourceLimit);
            }
            let coefficient = &cert.gram[row][column];
            if coefficient.is_zero() {
                continue;
            }
            let width = left
                .len()
                .checked_add(right.len())
                .ok_or(SosError::ResourceLimit)?;
            if !budget.charge_array::<TermId>(width)
                || !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
                || !budget.charge_rational_clone(coefficient)
            {
                return Err(SosError::ResourceLimit);
            }
            // Fallible reservation: a product monomial that cannot be held is
            // a resource limit, never an abort of the replay.
            let mut monomial = Vec::new();
            monomial
                .try_reserve_exact(width)
                .map_err(|_| SosError::ResourceLimit)?;
            monomial.extend_from_slice(left);
            monomial.extend_from_slice(right);
            monomial.sort_unstable();
            let term = MultiPoly {
                terms: vec![(monomial, coefficient.clone())],
            };
            result = checked_poly_add(&result, &term, budget).ok_or(SosError::ResourceLimit)?;
        }
    }
    Ok(result)
}

impl SosCertificate {
    /// Re-derive source products, check exact PSD and signs, and match the
    /// polynomial identity. Resource exhaustion is rejection, never evidence.
    #[cfg(test)]
    pub(crate) fn verify(&self, constraints: &[MultiConstraint]) -> Result<(), SosError> {
        let mut allow = |_, _| true;
        self.verify_with_progress(constraints, &mut SosProgress::new(&mut allow))
    }

    pub(crate) fn verify_with_progress(
        &self,
        constraints: &[MultiConstraint],
        progress: &mut SosProgress<'_>,
    ) -> Result<(), SosError> {
        check_inputs(
            self,
            constraints,
            &mut SosPolynomialBudget::with_progress(progress),
        )?;
        let mut arithmetic = SosLpBudget::with_progress(progress);
        let n = self.basis.len();
        for row in 0..n {
            for column in 0..n {
                if !arithmetic
                    .charge_rational_operation(&self.gram[row][column], &self.gram[column][row])
                {
                    return Err(SosError::ResourceLimit);
                }
                if self.gram[row][column] != self.gram[column][row] {
                    return Err(SosError::GramAsymmetric);
                }
            }
        }
        if !is_psd_bounded(&self.gram, &mut arithmetic)? {
            return Err(SosError::GramNotPsd);
        }
        if self.rhs.is_positive() {
            return Err(SosError::PositiveRhs);
        }
        let mut budget = SosPolynomialBudget::with_progress(progress);
        let mut lhs = sigma0_poly(self, &mut budget)?;
        let mut has_strict_positive = false;
        for term in &self.terms {
            if !budget.poll() {
                return Err(SosError::ResourceLimit);
            }
            let (poly, kind) = derive_oriented(term.origin, constraints, &mut budget)?;
            if kind.is_inequality() && term.multiplier.is_negative() {
                return Err(SosError::NegativeMultiplier);
            }
            has_strict_positive |= kind.is_strict() && term.multiplier.is_positive();
            if !budget.charge_rational_clone(&term.multiplier)
                || !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
            {
                return Err(SosError::ResourceLimit);
            }
            let scaled = checked_poly_mul(
                &poly,
                &MultiPoly::constant(term.multiplier.clone()),
                &mut budget,
            )
            .ok_or(SosError::ResourceLimit)?;
            lhs = checked_poly_add(&lhs, &scaled, &mut budget).ok_or(SosError::ResourceLimit)?;
        }
        if self.rhs.is_zero() && !has_strict_positive {
            return Err(SosError::NonStrictZeroRhs);
        }
        if !budget.charge_rational_clone(&self.rhs)
            || !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
        {
            return Err(SosError::ResourceLimit);
        }
        let difference =
            checked_poly_sub(&lhs, &MultiPoly::constant(self.rhs.clone()), &mut budget)
                .ok_or(SosError::ResourceLimit)?;
        if !difference.is_zero() {
            return Err(SosError::IdentityMismatch);
        }
        budget.poll().then_some(()).ok_or(SosError::ResourceLimit)
    }
}
