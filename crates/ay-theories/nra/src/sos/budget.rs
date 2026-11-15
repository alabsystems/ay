// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic resource limits for NRA SOS construction, search, and replay.
//!
//! Limits only restrict completeness: exhaustion declines the SOS lane and
//! never licenses an algebraic identity or an UNSAT verdict. The accounting
//! follows the established NIA SOS implementation without coupling the crates.

use ay_core::term::TermId;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::MultiPoly;

mod progress;
use progress::ProgressHandle;
pub(crate) use progress::SosProgress;

pub(crate) const MAX_SOS_ASSERTED_LITERALS: usize = 1_024;
pub(crate) const MAX_SOS_TERM_VISITS: usize = 100_000;
pub(crate) const MAX_SOS_TERM_DEPTH: usize = 256;
pub(crate) const MAX_SOS_POLY_TERMS: usize = 256;
pub(crate) const MAX_SOS_MONOMIAL_WORK: usize = 100_000;
pub(crate) const MAX_SOS_TERM_PRODUCTS: usize = 100_000;
pub(crate) const MAX_SOS_TOTAL_POLY_TERMS: usize = 8_192;
pub(crate) const MAX_SOS_POLY_DEGREE: usize = 4;
/// Both operands and retained results must fit this exact-rational envelope.
/// A single arithmetic operation can temporarily use at most the combined
/// operand widths; repeated elimination cannot retain growing integers.
pub(crate) const MAX_SOS_COEFFICIENT_BITS: u64 = 1_024;
pub(crate) const MAX_SOS_LP_UPDATES: usize = 10_000_000;
pub(crate) const MAX_SOS_LP_PIVOTS: usize = 4_096;
pub(crate) const MAX_SOS_LP_CELLS: usize = 65_536;

/// Shared deterministic work meter for polynomial construction.
#[derive(Debug, Default)]
pub(crate) struct SosPolynomialBudget<'a> {
    term_visits: usize,
    monomial_work: usize,
    term_products: usize,
    progress: ProgressHandle<'a>,
}

impl<'a> SosPolynomialBudget<'a> {
    pub(crate) fn with_progress(progress: &'a mut SosProgress<'_>) -> Self {
        Self {
            progress: ProgressHandle::new(progress),
            ..Self::default()
        }
    }

    pub(crate) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        self.progress.charge(work, bytes)
    }

    pub(crate) fn poll(&mut self) -> bool {
        self.charge(0, 0)
    }

    pub(crate) fn charge_array<T>(&mut self, count: usize) -> bool {
        self.progress.array::<T>(count)
    }

    pub(crate) fn charge_polynomial(&mut self, poly: &MultiPoly) -> bool {
        self.progress.polynomial(poly)
    }

    pub(crate) fn charge_rational_clone(&mut self, value: &BigRational) -> bool {
        self.progress.rational_clone(value)
    }

    pub(crate) fn charge_rational_operation(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> bool {
        self.progress.rational_operation(left, right)
    }

    pub(crate) fn visit_term(&mut self, depth: usize) -> bool {
        if !self.charge(1, std::mem::size_of::<(TermId, usize)>())
            || depth > MAX_SOS_TERM_DEPTH
            || self.term_visits >= MAX_SOS_TERM_VISITS
        {
            return false;
        }
        self.term_visits += 1;
        true
    }

    pub(crate) fn charge_monomial(&mut self) -> bool {
        if !self.charge(MAX_SOS_POLY_TERMS * MAX_SOS_POLY_DEGREE, 0)
            || self.monomial_work >= MAX_SOS_MONOMIAL_WORK
        {
            return false;
        }
        self.monomial_work += 1;
        true
    }

    pub(crate) fn charge_product(&mut self) -> bool {
        if !self.charge(MAX_SOS_POLY_DEGREE, 0) || self.term_products >= MAX_SOS_TERM_PRODUCTS {
            return false;
        }
        self.term_products += 1;
        true
    }
}

/// Reject malformed raw rationals before any arithmetic can divide by zero or
/// rely on the positive-denominator invariant of `BigRational`.
pub(crate) fn rational_fits(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_SOS_COEFFICIENT_BITS
        && value.denom().bits() <= MAX_SOS_COEFFICIENT_BITS
        && value.denom().is_positive()
}

/// Validate sparse-polynomial invariants before cloning or expansion. Stored
/// terms need not be ordered, but each monomial must be sorted and unique.
pub(crate) fn polynomial_fits(poly: &MultiPoly, vars: Option<&[TermId]>) -> bool {
    if poly.terms.len() > MAX_SOS_POLY_TERMS
        || vars.is_some_and(|allowed| allowed.len() > MAX_SOS_POLY_TERMS)
    {
        return false;
    }
    poly.terms
        .iter()
        .enumerate()
        .all(|(index, (monomial, coefficient))| {
            rational_fits(coefficient)
                && !coefficient.is_zero()
                && monomial.len() <= MAX_SOS_POLY_DEGREE
                && monomial
                    .windows(2)
                    .all(|pair| matches!(pair, [first, second] if first <= second))
                && vars.is_none_or(|allowed| monomial.iter().all(|var| allowed.contains(var)))
                && poly.terms.get(..index).is_some_and(|earlier_terms| {
                    earlier_terms.iter().all(|(earlier, _)| earlier != monomial)
                })
        })
}

fn add_term(
    poly: &mut MultiPoly,
    monomial: Vec<TermId>,
    coefficient: BigRational,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<()> {
    if !budget.charge_monomial()
        || !rational_fits(&coefficient)
        || monomial.len() > MAX_SOS_POLY_DEGREE
    {
        return None;
    }
    if coefficient.is_zero() {
        return Some(());
    }
    if let Some(index) = poly
        .terms
        .iter()
        .position(|(existing, _)| existing == &monomial)
    {
        if !budget.charge_rational_operation(&poly.terms[index].1, &coefficient) {
            return None;
        }
        let combined = &poly.terms[index].1 + coefficient;
        if !rational_fits(&combined) {
            return None;
        }
        if combined.is_zero() {
            poly.terms.remove(index);
        } else {
            poly.terms[index].1 = combined;
        }
        return Some(());
    }
    if poly.terms.len() >= MAX_SOS_POLY_TERMS {
        return None;
    }
    poly.terms.push((monomial, coefficient));
    Some(())
}

pub(crate) fn checked_poly_add(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.charge_polynomial(left) || !budget.charge_polynomial(right) {
        return None;
    }
    let mut result = MultiPoly::zero();
    for (monomial, coefficient) in left.terms.iter().chain(&right.terms) {
        add_term(&mut result, monomial.clone(), coefficient.clone(), budget)?;
    }
    budget.poll().then_some(result)
}

pub(crate) fn checked_poly_neg(
    poly: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.charge_polynomial(poly) {
        return None;
    }
    let mut result = MultiPoly::zero();
    for (monomial, coefficient) in &poly.terms {
        add_term(&mut result, monomial.clone(), -coefficient, budget)?;
    }
    budget.poll().then_some(result)
}

pub(crate) fn checked_poly_sub(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.poll() || !polynomial_fits(left, None) {
        return None;
    }
    let negated = checked_poly_neg(right, budget)?;
    checked_poly_add(left, &negated, budget)
}

pub(crate) fn checked_poly_mul(
    left: &MultiPoly,
    right: &MultiPoly,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<MultiPoly> {
    if !budget.charge_polynomial(left) || !budget.charge_polynomial(right) {
        return None;
    }
    let mut result = MultiPoly::zero();
    for (left_monomial, left_coefficient) in &left.terms {
        for (right_monomial, right_coefficient) in &right.terms {
            if !budget.charge_product() {
                return None;
            }
            let degree = left_monomial.len().checked_add(right_monomial.len())?;
            if degree > MAX_SOS_POLY_DEGREE
                || !budget.charge_array::<TermId>(degree)
                || !budget.charge_array::<(Vec<TermId>, BigRational)>(1)
                || !budget.charge_rational_operation(left_coefficient, right_coefficient)
            {
                return None;
            }
            let mut monomial = left_monomial.clone();
            monomial.extend_from_slice(right_monomial);
            monomial.sort_unstable();
            add_term(
                &mut result,
                monomial,
                left_coefficient * right_coefficient,
                budget,
            )?;
        }
    }
    budget.poll().then_some(result)
}

/// Checked accumulator used for exact LP/replay arithmetic and pivots.
#[derive(Debug)]
pub(crate) struct SosLpBudget<'a> {
    updates_left: usize,
    pivots_left: usize,
    progress: ProgressHandle<'a>,
}

impl Default for SosLpBudget<'_> {
    fn default() -> Self {
        Self {
            updates_left: MAX_SOS_LP_UPDATES,
            pivots_left: MAX_SOS_LP_PIVOTS,
            progress: ProgressHandle::default(),
        }
    }
}

impl<'a> SosLpBudget<'a> {
    pub(crate) fn with_progress(progress: &'a mut SosProgress<'_>) -> Self {
        Self {
            progress: ProgressHandle::new(progress),
            ..Self::default()
        }
    }

    pub(crate) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        self.progress.charge(work, bytes)
    }

    pub(crate) fn poll(&mut self) -> bool {
        self.charge(0, 0)
    }

    pub(crate) fn charge_array<T>(&mut self, count: usize) -> bool {
        self.progress.array::<T>(count)
    }

    pub(crate) fn charge_rational_clone(&mut self, value: &BigRational) -> bool {
        self.progress.rational_clone(value)
    }

    pub(crate) fn charge_rational_operation(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> bool {
        self.progress.rational_operation(left, right)
    }

    pub(crate) fn charge_updates(&mut self, count: usize) -> bool {
        if !self.charge(count, 0) {
            return false;
        }
        let Some(left) = self.updates_left.checked_sub(count) else {
            return false;
        };
        self.updates_left = left;
        true
    }

    pub(crate) fn charge_pivot(&mut self) -> bool {
        if !self.charge(1, 0) {
            return false;
        }
        let Some(left) = self.pivots_left.checked_sub(1) else {
            return false;
        };
        self.pivots_left = left;
        true
    }
}

/// Check *before* allocating either the input matrix or the artificial-variable
/// tableau. The separate column cap bounds a zero-row solution vector too.
pub(crate) fn lp_dimensions_fit(rows: usize, structural_columns: usize) -> bool {
    if structural_columns > MAX_SOS_LP_CELLS {
        return false;
    }
    structural_columns
        .checked_add(rows)
        .and_then(|total| total.checked_add(1))
        .and_then(|columns| rows.checked_mul(columns))
        .is_some_and(|cells| cells <= MAX_SOS_LP_CELLS)
}

#[cfg(test)]
mod tests;
