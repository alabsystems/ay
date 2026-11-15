// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded coefficient matching and Gram reconstruction for the two templates.

use super::super::budget::{lp_dimensions_fit, SosLpBudget, SosProgress};
use super::super::lp::{lp_add, lp_mul, lp_phase1_feasible_with_progress, lp_sub};
use super::*;

#[derive(Clone, Copy)]
pub(super) enum Template {
    Negative,
    Strict,
}

impl Template {
    fn extra_rows(self) -> usize {
        usize::from(matches!(self, Self::Strict))
    }

    fn rhs(self) -> BigRational {
        match self {
            Self::Negative => -one(),
            Self::Strict => zero(),
        }
    }
}

struct Layout {
    atoms: usize,
    surplus: usize,
    equalities: usize,
    columns: usize,
    rhs: BigRational,
}

impl Layout {
    fn new(squares: usize, atoms: usize, equalities: usize, template: Template) -> Option<Self> {
        let surplus = squares.checked_add(atoms)?;
        let equality_start = surplus.checked_add(template.extra_rows())?;
        let columns = equality_start.checked_add(equalities.checked_mul(2)?)?;
        (columns <= MAX_LP_COLS).then_some(Self {
            atoms: squares,
            surplus,
            equalities: equality_start,
            columns,
            rhs: template.rhs(),
        })
    }
}

pub(super) fn try_template(
    basis: &[Vec<TermId>],
    squares: &[Square],
    atoms: &[Atom],
    equalities: &[EqAtom],
    template: Template,
    progress: &mut SosProgress<'_>,
) -> Option<SosCertificate> {
    let mut budget = SosLpBudget::with_progress(progress);
    if !budget.charge_array::<BigRational>(1) {
        return None;
    }
    let layout = Layout::new(squares.len(), atoms.len(), equalities.len(), template)?;
    let monos = collect_support(squares, atoms, equalities, &layout, template, &mut budget)?;
    let rows = monos.len().checked_add(template.extra_rows())?;
    // This checks the larger Phase-1 tableau before allocating even its input.
    if !lp_dimensions_fit(rows, layout.columns) {
        return None;
    }
    let mut matrix = coefficient_matrix(&monos, squares, atoms, equalities, &layout, &mut budget)?;
    if !budget.charge_array::<BigRational>(rows) {
        return None;
    }
    let mut rhs = vec![zero(); rows];
    rhs[0] = template.rhs();
    if matches!(template, Template::Strict) {
        // Sum of strict multipliers >=1, using a nonnegative surplus variable.
        // Any strict-positive certificate can be normalized into this template.
        if !budget.charge_array::<BigRational>(layout.columns)
            || !budget.charge_array::<Vec<BigRational>>(1)
        {
            return None;
        }
        let mut strict = vec![zero(); layout.columns];
        for (index, atom) in atoms.iter().enumerate() {
            if !budget.charge(1, 0) {
                return None;
            }
            if atom.kind.is_strict() {
                strict[layout.atoms + index] = one();
            }
        }
        strict[layout.surplus] = -one();
        rhs[monos.len()] = one();
        matrix.push(strict);
    }
    let solution = {
        // The nested LP retains its own legacy update/pivot counters, while
        // forwarding every debit to the SAME sticky outer control ledger.
        let mut forward = |work, bytes| budget.charge(work, bytes);
        lp_phase1_feasible_with_progress(
            matrix,
            rhs,
            layout.columns,
            &mut SosProgress::new(&mut forward),
        )?
    };
    let candidate = reconstruct(
        basis,
        squares,
        atoms,
        equalities,
        &layout,
        &solution,
        &mut budget,
    )?;
    budget.poll().then_some(candidate)
}

fn collect_support(
    squares: &[Square],
    atoms: &[Atom],
    equalities: &[EqAtom],
    layout: &Layout,
    template: Template,
    budget: &mut SosLpBudget<'_>,
) -> Option<Vec<Vec<TermId>>> {
    if !budget.charge_array::<Vec<TermId>>(1) {
        return None;
    }
    let mut monos = vec![Vec::new()];
    for poly in squares
        .iter()
        .map(|square| &square.poly)
        .chain(atoms.iter().map(|atom| &atom.poly))
        .chain(equalities.iter().map(|atom| &atom.poly))
    {
        for (monomial, _) in &poly.terms {
            if !budget.charge(monos.len().saturating_mul(4).saturating_add(1), 0) {
                return None;
            }
            if !monos.contains(monomial) {
                let rows = monos
                    .len()
                    .checked_add(1)?
                    .checked_add(template.extra_rows())?;
                if !lp_dimensions_fit(rows, layout.columns) {
                    return None;
                }
                if !budget.charge_array::<Vec<TermId>>(1)
                    || !budget.charge_array::<TermId>(monomial.len())
                {
                    return None;
                }
                monos.push(monomial.clone());
            }
        }
    }
    Some(monos)
}

fn coefficient_matrix(
    monos: &[Vec<TermId>],
    squares: &[Square],
    atoms: &[Atom],
    equalities: &[EqAtom],
    layout: &Layout,
    budget: &mut SosLpBudget<'_>,
) -> Option<Vec<Vec<BigRational>>> {
    if !budget.charge_array::<BigRational>(monos.len().checked_mul(layout.columns)?)
        || !budget.charge_array::<Vec<BigRational>>(monos.len())
    {
        return None;
    }
    let mut matrix = vec![vec![zero(); layout.columns]; monos.len()];
    let row_of = |monomial: &[TermId]| monos.iter().position(|item| item.as_slice() == monomial);
    for (column, poly) in squares
        .iter()
        .map(|square| &square.poly)
        .chain(atoms.iter().map(|atom| &atom.poly))
        .enumerate()
    {
        for (monomial, coefficient) in &poly.terms {
            if !budget.charge(monos.len().saturating_mul(4), 0) {
                return None;
            }
            let row = row_of(monomial)?;
            matrix[row][column] = lp_add(&matrix[row][column], coefficient, budget)?;
        }
    }
    for (index, equality) in equalities.iter().enumerate() {
        let positive = layout.equalities + 2 * index;
        for (monomial, coefficient) in &equality.poly.terms {
            if !budget.charge(monos.len().saturating_mul(4), 0) {
                return None;
            }
            let row = row_of(monomial)?;
            matrix[row][positive] = lp_add(&matrix[row][positive], coefficient, budget)?;
            matrix[row][positive + 1] = lp_sub(&matrix[row][positive + 1], coefficient, budget)?;
        }
    }
    Some(matrix)
}

fn reconstruct(
    basis: &[Vec<TermId>],
    squares: &[Square],
    atoms: &[Atom],
    equalities: &[EqAtom],
    layout: &Layout,
    solution: &[BigRational],
    budget: &mut SosLpBudget<'_>,
) -> Option<SosCertificate> {
    if basis.len() > MAX_BASIS || solution.len() != layout.columns {
        return None;
    }
    let gram = reconstruct_gram(basis.len(), squares, solution, budget)?;
    if !budget.charge_array::<CertTerm>(atoms.len().checked_add(equalities.len())?)
        || !budget.charge_array::<Vec<TermId>>(basis.len())
        || !budget.charge_rational_clone(&layout.rhs)
    {
        return None;
    }
    for monomial in basis {
        if !budget.charge_array::<TermId>(monomial.len()) {
            return None;
        }
    }
    let mut terms = Vec::new();
    for (index, atom) in atoms.iter().enumerate() {
        let multiplier = &solution[layout.atoms + index];
        if !budget.charge(1, 0) {
            return None;
        }
        if !multiplier.is_zero() {
            if !budget.charge_rational_clone(multiplier) {
                return None;
            }
            terms.push(CertTerm {
                origin: atom.origin,
                multiplier: multiplier.clone(),
            });
        }
    }
    for (index, equality) in equalities.iter().enumerate() {
        let positive = layout.equalities + 2 * index;
        let multiplier = lp_sub(&solution[positive], &solution[positive + 1], budget)?;
        if !multiplier.is_zero() {
            terms.push(CertTerm {
                origin: CertOrigin::Constraint(equality.index),
                multiplier,
            });
        }
    }
    Some(SosCertificate {
        basis: basis.to_vec(),
        gram,
        terms,
        rhs: layout.rhs.clone(),
    })
}

fn reconstruct_gram(
    size: usize,
    squares: &[Square],
    solution: &[BigRational],
    budget: &mut SosLpBudget<'_>,
) -> Option<Vec<Vec<BigRational>>> {
    if !budget.charge_array::<BigRational>(size.checked_mul(size)?)
        || !budget.charge_array::<Vec<BigRational>>(size)
    {
        return None;
    }
    let mut gram = vec![vec![zero(); size]; size];
    for (index, square) in squares.iter().enumerate() {
        if !budget.charge(1, 0) {
            return None;
        }
        let scale = &solution[index];
        if scale.is_zero() {
            continue;
        }
        for (row, left) in square.form.iter().enumerate() {
            if !budget.charge(1, 0) {
                return None;
            }
            if left.is_zero() {
                continue;
            }
            for (column, right) in square.form.iter().enumerate() {
                if !budget.charge(1, 0) {
                    return None;
                }
                if !right.is_zero() {
                    let scaled = lp_mul(scale, left, budget)?;
                    let delta = lp_mul(&scaled, right, budget)?;
                    gram[row][column] = lp_add(&gram[row][column], &delta, budget)?;
                }
            }
        }
    }
    Some(gram)
}
