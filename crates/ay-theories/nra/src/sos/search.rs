// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Degree-2-first exact DSOS search with a bounded degree-4 fallback.

use super::budget::{
    checked_poly_mul, lp_dimensions_fit, SosPolynomialBudget, SosProgress, MAX_SOS_TOTAL_POLY_TERMS,
};
use super::checker::source_fits;
use super::*;

mod template;
use template::{try_template, Template};

#[derive(Clone, Copy)]
enum Degree {
    Quadratic,
    Quartic,
}

impl Degree {
    fn bound(self) -> usize {
        match self {
            Self::Quadratic => 2,
            Self::Quartic => 4,
        }
    }
}

struct Atom {
    origin: CertOrigin,
    kind: OrientedKind,
    poly: MultiPoly,
}

struct EqAtom {
    index: usize,
    poly: MultiPoly,
}

struct Square {
    form: Vec<BigRational>,
    poly: MultiPoly,
}

/// Search is not an UNSAT authority: every returned candidate is independently
/// checked against the original, position-preserving source constraints.
pub(crate) fn search(constraints: &[MultiConstraint], vars: &[TermId]) -> Option<SosCertificate> {
    let mut allow = |_, _| true;
    search_with_progress(constraints, vars, &mut SosProgress::new(&mut allow))
}

pub(crate) fn search_with_progress(
    constraints: &[MultiConstraint],
    vars: &[TermId],
    progress: &mut SosProgress<'_>,
) -> Option<SosCertificate> {
    if !progress.poll()
        || vars.is_empty()
        || vars.len() > MAX_VARS
        || !progress.charge(vars.len() * vars.len(), 0)
        || vars
            .iter()
            .enumerate()
            .any(|(index, var)| vars.get(..index).is_some_and(|prior| prior.contains(var)))
        || !source_fits(
            constraints,
            Some(vars),
            &mut SosPolynomialBudget::with_progress(progress),
        )
    {
        return None;
    }
    search_degree(constraints, vars, Degree::Quadratic, progress)
        .or_else(|| search_degree(constraints, vars, Degree::Quartic, progress))
}

fn search_degree(
    constraints: &[MultiConstraint],
    vars: &[TermId],
    degree: Degree,
    progress: &mut SosProgress<'_>,
) -> Option<SosCertificate> {
    let mut budget = SosPolynomialBudget::with_progress(progress);
    if !budget.poll() {
        return None;
    }
    let basis = make_basis(vars, degree, &mut budget)?;
    let first = match degree {
        Degree::Quadratic => 1, // Preserve the original homogeneous dictionary.
        Degree::Quartic => 0,   // Also include constant and shifted squares.
    };
    let dictionary_len = basis.len().checked_sub(first)?.checked_pow(2)?;
    if dictionary_len > MAX_LP_COLS {
        return None;
    }
    // The complete quartic dictionary generates every monomial of degree <=4.
    // Reject its unavoidable minimum tableau before allocating any squares.
    if matches!(degree, Degree::Quartic)
        && !lp_dimensions_fit(quartic_support_size(vars.len())?, dictionary_len)
    {
        return None;
    }
    let (atoms, eqs) = collect_atoms(constraints, degree, &mut budget)?;
    let squares = make_squares(&basis, first, &mut budget)?;
    // Polynomial phase counters end here; the shared control ledger survives.
    for template in [Template::Negative, Template::Strict] {
        if !progress.poll() {
            return None;
        }
        if matches!(template, Template::Strict) && !atoms.iter().any(|atom| atom.kind.is_strict()) {
            continue;
        }
        if let Some(cert) = try_template(&basis, &squares, &atoms, &eqs, template, progress) {
            if cert.verify_with_progress(constraints, progress).is_ok() && progress.poll() {
                return Some(cert);
            }
        }
    }
    None
}

fn make_basis(
    vars: &[TermId],
    degree: Degree,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<Vec<Vec<TermId>>> {
    if !budget.charge_array::<Vec<TermId>>(MAX_BASIS) {
        return None;
    }
    let mut basis = Vec::with_capacity(MAX_BASIS);
    basis.push(Vec::new());
    for &var in vars {
        if !budget.charge_array::<TermId>(1) {
            return None;
        }
        basis.push(vec![var]);
    }
    if matches!(degree, Degree::Quartic) {
        for (index, &left) in vars.iter().enumerate() {
            for &right in vars.get(index..)? {
                if !budget.charge_array::<TermId>(2) {
                    return None;
                }
                let mut monomial = vec![left, right];
                monomial.sort_unstable();
                basis.push(monomial);
            }
        }
    }
    budget.poll().then_some(basis)
}

fn quartic_support_size(vars: usize) -> Option<usize> {
    // C(vars+4, 4), with exact division at each combinatorial recurrence.
    (1..=4).try_fold(1usize, |count, offset| {
        count
            .checked_mul(vars.checked_add(offset)?)?
            .checked_div(offset)
    })
}

fn collect_atoms(
    constraints: &[MultiConstraint],
    degree: Degree,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<(Vec<Atom>, Vec<EqAtom>)> {
    let mut atoms = Vec::new();
    let mut eqs = Vec::new();
    let mut retained_terms = 0usize;
    for (index, constraint) in constraints.iter().enumerate() {
        if !budget.charge(1, 0) {
            return None;
        }
        if poly_degree(&constraint.poly) > degree.bound() {
            continue;
        }
        if !budget.charge_polynomial(&constraint.poly) {
            return None;
        }
        let Some((poly, kind)) = orient(constraint) else {
            continue;
        };
        retained_terms = retained_terms.checked_add(poly.terms.len())?;
        if retained_terms > MAX_SOS_TOTAL_POLY_TERMS {
            return None;
        }
        match kind {
            OrientedKind::Eq => {
                if eqs.len() >= MAX_LP_COLS / 2 {
                    return None;
                }
                if !budget.charge_array::<EqAtom>(1) {
                    return None;
                }
                eqs.push(EqAtom { index, poly });
            }
            OrientedKind::Ge | OrientedKind::Gt => {
                if atoms.len() >= MAX_ATOMS {
                    return None;
                }
                if !budget.charge_array::<Atom>(1) {
                    return None;
                }
                atoms.push(Atom {
                    origin: CertOrigin::Constraint(index),
                    kind,
                    poly,
                });
            }
        }
    }
    add_products(&mut atoms, degree, budget, &mut retained_terms)?;
    Some((atoms, eqs))
}

fn add_products(
    atoms: &mut Vec<Atom>,
    degree: Degree,
    budget: &mut SosPolynomialBudget<'_>,
    retained_terms: &mut usize,
) -> Option<()> {
    let original_count = atoms.len();
    for left in 0..original_count {
        for right in left..original_count {
            if !budget.charge(1, 0) {
                return None;
            }
            if atoms.len() >= MAX_ATOMS {
                return Some(()); // Same deterministic prefix as the degree-2 lane.
            }
            let left_degree = poly_degree(&atoms[left].poly);
            let right_degree = poly_degree(&atoms[right].poly);
            let admissible = match degree {
                Degree::Quadratic => left_degree <= 1 && right_degree <= 1,
                Degree::Quartic => left_degree
                    .checked_add(right_degree)
                    .is_some_and(|total| total <= 4),
            };
            if !admissible {
                continue;
            }
            let (CertOrigin::Constraint(left_index), CertOrigin::Constraint(right_index)) =
                (atoms[left].origin, atoms[right].origin)
            else {
                return None;
            };
            let poly = checked_poly_mul(&atoms[left].poly, &atoms[right].poly, budget)?;
            *retained_terms = retained_terms.checked_add(poly.terms.len())?;
            if *retained_terms > MAX_SOS_TOTAL_POLY_TERMS {
                return None;
            }
            let kind = if atoms[left].kind.is_strict() && atoms[right].kind.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            if !budget.charge_array::<Atom>(1) {
                return None;
            }
            atoms.push(Atom {
                origin: CertOrigin::Product(left_index, right_index),
                kind,
                poly,
            });
        }
    }
    Some(())
}

fn make_squares(
    basis: &[Vec<TermId>],
    first: usize,
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<Vec<Square>> {
    let count = basis.len().checked_sub(first)?.checked_pow(2)?;
    if count > MAX_LP_COLS || !budget.charge_array::<Square>(count) {
        return None;
    }
    let mut squares = Vec::with_capacity(count);
    for index in first..basis.len() {
        if !budget.charge_array::<BigRational>(basis.len()) {
            return None;
        }
        let mut form = vec![zero(); basis.len()];
        form[index] = one();
        squares.push(make_square(form, basis, budget)?);
    }
    for left in first..basis.len() {
        // `left < basis.len()`, so the saturating bound is exactly `left + 1`.
        for right in left.saturating_add(1)..basis.len() {
            if !budget.charge_array::<BigRational>(2) {
                return None;
            }
            for sign in [one(), -one()] {
                if !budget.charge_array::<BigRational>(basis.len()) {
                    return None;
                }
                let mut form = vec![zero(); basis.len()];
                form[left] = one();
                form[right] = sign;
                squares.push(make_square(form, basis, budget)?);
            }
        }
    }
    budget.poll().then_some(squares)
}

fn make_square(
    form: Vec<BigRational>,
    basis: &[Vec<TermId>],
    budget: &mut SosPolynomialBudget<'_>,
) -> Option<Square> {
    if !budget.charge_array::<(Vec<TermId>, BigRational)>(form.len()) {
        return None;
    }
    for (index, coefficient) in form.iter().enumerate() {
        if !budget.charge(1, 0) {
            return None;
        }
        if coefficient.is_zero() {
            continue;
        }
        // A nonzero coefficient outside the basis names no monomial: decline.
        let monomial = basis.get(index)?;
        if !budget.charge_array::<TermId>(monomial.len())
            || !budget.charge_rational_clone(coefficient)
        {
            return None;
        }
    }
    let polynomial = MultiPoly {
        terms: form
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(index, coefficient)| Some((basis.get(index)?.clone(), coefficient.clone())))
            .collect::<Option<_>>()?,
    };
    let poly = checked_poly_mul(&polynomial, &polynomial, budget)?;
    Some(Square { form, poly })
}

#[cfg(test)]
mod tests;
