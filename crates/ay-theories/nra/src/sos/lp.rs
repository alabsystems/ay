// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded exact-rational Phase-1 feasibility solver for the SOS search.
//!
//! This follows the established NIA SOS Phase-1 implementation. Bland's rule
//! selects entering/leaving variables; deterministic envelopes bound concrete
//! resource use. Infeasibility and resource exhaustion both decline search.

use std::cmp::Ordering;

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::budget::{lp_dimensions_fit, rational_fits, SosLpBudget, SosProgress};
use super::{one, zero};

/// Find a rational solution to `{ A x = b, x >= 0 }`, if the bounded Phase-1
/// search succeeds. `None` is not a proof of infeasibility.
#[cfg(test)]
pub(super) fn lp_phase1_feasible(
    a: Vec<Vec<BigRational>>,
    b: Vec<BigRational>,
    n: usize,
) -> Option<Vec<BigRational>> {
    let mut allow = |_, _| true;
    lp_phase1_feasible_with_progress(a, b, n, &mut SosProgress::new(&mut allow))
}

#[allow(clippy::needless_range_loop)] // Tableau indices retain their exact pivot identities.
pub(super) fn lp_phase1_feasible_with_progress(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
    n: usize,
    progress: &mut SosProgress<'_>,
) -> Option<Vec<BigRational>> {
    let mut budget = SosLpBudget::with_progress(progress);
    let m = a.len();
    if !budget.poll() || !lp_dimensions_fit(m, n) || b.len() != m {
        return None;
    }
    if !budget.charge(m, 0) || a.iter().any(|row| row.len() != n) {
        return None;
    }
    if !budget.charge(m.checked_mul(n)?.checked_add(m)?, 0)
        || !a.iter().flatten().all(rational_fits)
        || !b.iter().all(rational_fits)
    {
        return None;
    }
    if m == 0 {
        if !budget.charge_array::<BigRational>(n) {
            return None;
        }
        let solution = vec![zero(); n];
        return budget.poll().then_some(solution);
    }
    let total = n.checked_add(m)?;
    let tableau_cols = total.checked_add(1)?;
    normalize_rhs(&mut a, &mut b, n, &mut budget)?;

    if !budget.charge_array::<BigRational>(m.checked_mul(tableau_cols)?)
        || !budget.charge_array::<Vec<BigRational>>(m)
        || !budget.charge_array::<usize>(m)
    {
        return None;
    }
    let mut tableau = vec![vec![zero(); tableau_cols]; m];
    for row in 0..m {
        for column in 0..n {
            if !budget.charge_rational_clone(&a[row][column]) {
                return None;
            }
            tableau[row][column] = a[row][column].clone();
        }
        if !budget.charge_rational_clone(&b[row]) {
            return None;
        }
        tableau[row][n + row] = one();
        tableau[row][total] = b[row].clone();
    }
    let mut basis: Vec<usize> = (0..m).map(|row| n + row).collect();
    let mut reduced_costs = initial_reduced_costs(&tableau, n, total, &mut budget)?;

    loop {
        if !budget.charge(reduced_costs.len(), 0) {
            return None;
        }
        let Some(entering) = reduced_costs.iter().position(Signed::is_negative) else {
            break;
        };
        if !budget.charge_pivot() {
            return None;
        }
        let leaving = choose_leaving_row(&tableau, &basis, entering, total, &mut budget)?;
        pivot_tableau(
            &mut tableau,
            &mut reduced_costs,
            leaving,
            entering,
            total,
            &mut budget,
        )?;
        basis[leaving] = entering;
    }

    extract_feasible_solution(&tableau, &basis, n, total, &mut budget)
}

/// A zero Phase-1 artificial objective licenses a feasible candidate, not an
/// infeasibility verdict. Charge every returned coefficient before copying it.
fn extract_feasible_solution(
    tableau: &[Vec<BigRational>],
    basis: &[usize],
    n: usize,
    rhs_column: usize,
    budget: &mut SosLpBudget<'_>,
) -> Option<Vec<BigRational>> {
    let mut objective = zero();
    for (row, &variable) in tableau.iter().zip(basis) {
        if !budget.charge(1, 0) {
            return None;
        }
        if variable >= n {
            objective = lp_add(&objective, &row[rhs_column], budget)?;
        }
    }
    if !objective.is_zero() {
        return None;
    }
    if !budget.charge_array::<BigRational>(n) {
        return None;
    }
    let mut solution = vec![zero(); n];
    for (row, &variable) in tableau.iter().zip(basis) {
        if variable < n {
            if !budget.charge_rational_clone(&row[rhs_column]) {
                return None;
            }
            solution[variable] = row[rhs_column].clone();
        }
    }
    budget.poll().then_some(solution)
}

fn normalize_rhs(
    a: &mut [Vec<BigRational>],
    b: &mut [BigRational],
    n: usize,
    budget: &mut SosLpBudget<'_>,
) -> Option<()> {
    for row in 0..a.len() {
        if !budget.charge(1, 0) {
            return None;
        }
        if b[row].is_negative() {
            for coefficient in &mut a[row][..n] {
                *coefficient = lp_neg(coefficient, budget)?;
            }
            b[row] = lp_neg(&b[row], budget)?;
        }
    }
    Some(())
}

fn initial_reduced_costs(
    tableau: &[Vec<BigRational>],
    n: usize,
    total: usize,
    budget: &mut SosLpBudget<'_>,
) -> Option<Vec<BigRational>> {
    if !budget.charge_array::<BigRational>(total) {
        return None;
    }
    let mut costs = Vec::with_capacity(total);
    for column in 0..total {
        let mut cost = if column >= n { one() } else { zero() };
        for row in tableau {
            if !budget.charge(1, 0) {
                return None;
            }
            if !row[column].is_zero() {
                cost = lp_sub(&cost, &row[column], budget)?;
            }
        }
        costs.push(cost);
    }
    Some(costs)
}

fn choose_leaving_row(
    tableau: &[Vec<BigRational>],
    basis: &[usize],
    entering: usize,
    rhs_column: usize,
    budget: &mut SosLpBudget<'_>,
) -> Option<usize> {
    let mut leaving: Option<usize> = None;
    let mut best = None;
    for row in 0..tableau.len() {
        if !budget.charge(1, 0) {
            return None;
        }
        if tableau[row][entering].is_positive() {
            let ratio = lp_div(&tableau[row][rhs_column], &tableau[row][entering], budget)?;
            let take = match &best {
                None => true,
                Some(current) => {
                    if !budget.charge_updates(1)
                        || !budget.charge_rational_operation(&ratio, current)
                    {
                        return None;
                    }
                    match ratio.cmp(current) {
                        Ordering::Less => true,
                        Ordering::Equal => leaving.is_some_and(|old| basis[row] < basis[old]),
                        Ordering::Greater => false,
                    }
                }
            };
            if take {
                best = Some(ratio);
                leaving = Some(row);
            }
        }
    }
    leaving
}

fn pivot_tableau(
    tableau: &mut [Vec<BigRational>],
    reduced_costs: &mut [BigRational],
    leaving: usize,
    entering: usize,
    total: usize,
    budget: &mut SosLpBudget<'_>,
) -> Option<()> {
    if !budget.charge_rational_clone(&tableau[leaving][entering]) {
        return None;
    }
    let columns = total.checked_add(1)?;
    if !budget.charge_array::<usize>(columns) {
        return None;
    }
    let pivot = tableau[leaving][entering].clone();
    if !pivot.is_one() {
        for coefficient in &mut tableau[leaving][..columns] {
            if !budget.charge(1, 0) {
                return None;
            }
            if !coefficient.is_zero() {
                *coefficient = lp_div(coefficient, &pivot, budget)?;
            }
        }
    }
    let support: Vec<usize> = (0..columns)
        .filter(|&column| !tableau[leaving][column].is_zero())
        .collect();
    for row in 0..tableau.len() {
        if !budget.charge(1, 0) {
            return None;
        }
        if row != leaving && !tableau[row][entering].is_zero() {
            if !budget.charge_rational_clone(&tableau[row][entering]) {
                return None;
            }
            let factor = tableau[row][entering].clone();
            for &column in &support {
                let delta = lp_mul(&factor, &tableau[leaving][column], budget)?;
                tableau[row][column] = lp_sub(&tableau[row][column], &delta, budget)?;
            }
        }
    }
    if !reduced_costs[entering].is_zero() {
        if !budget.charge_rational_clone(&reduced_costs[entering]) {
            return None;
        }
        let factor = reduced_costs[entering].clone();
        for &column in &support {
            if column < total {
                let delta = lp_mul(&factor, &tableau[leaving][column], budget)?;
                reduced_costs[column] = lp_sub(&reduced_costs[column], &delta, budget)?;
            }
        }
    }
    budget.poll().then_some(())
}

pub(super) fn lp_add(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget<'_>,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left + right)
}

pub(super) fn lp_sub(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget<'_>,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left - right)
}

pub(super) fn lp_mul(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget<'_>,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left * right)
}

pub(super) fn lp_div(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget<'_>,
) -> Option<BigRational> {
    if right.is_zero() {
        return None;
    }
    bounded_binary(left, right, budget, |left, right| left / right)
}

fn bounded_binary(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget<'_>,
    operation: impl FnOnce(&BigRational, &BigRational) -> BigRational,
) -> Option<BigRational> {
    if !rational_fits(left)
        || !rational_fits(right)
        || !budget.charge_updates(1)
        || !budget.charge_rational_operation(left, right)
    {
        return None;
    }
    let result = operation(left, right);
    (rational_fits(&result) && budget.poll()).then_some(result)
}

fn lp_neg(value: &BigRational, budget: &mut SosLpBudget<'_>) -> Option<BigRational> {
    if !rational_fits(value) || !budget.charge_updates(1) || !budget.charge_rational_clone(value) {
        return None;
    }
    let result = -value;
    budget.poll().then_some(result)
}

#[cfg(test)]
mod tests;
