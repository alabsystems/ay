// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded exact-rational Phase-1 feasibility solver for the SOS search.

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::budget::{rational_fits, SosLpBudget, MAX_SOS_LP_CELLS};
use super::{one, zero};

/// Decide feasibility of `{ A x = b, x >= 0 }` over the rationals.
///
/// Bland's rule guarantees algorithmic termination; the explicit pivot,
/// rational-update, coefficient-size, and tableau-size limits bound concrete
/// resource use. Exhaustion returns `None` and cannot produce a certificate.
#[allow(clippy::needless_range_loop)] // Tableau pivoting uses row/column identities.
pub(super) fn lp_phase1_feasible(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
    n: usize,
) -> Option<Vec<BigRational>> {
    let m = a.len();
    if b.len() != m
        || n > MAX_SOS_LP_CELLS
        || a.iter().any(|row| row.len() != n)
        || !a.iter().flatten().all(rational_fits)
        || !b.iter().all(rational_fits)
    {
        return None;
    }
    let total = n.checked_add(m)?;
    let tableau_cols = total.checked_add(1)?;
    if m.checked_mul(tableau_cols)? > MAX_SOS_LP_CELLS {
        return None;
    }
    if m == 0 {
        return Some(vec![zero(); n]);
    }
    let mut budget = SosLpBudget::default();
    normalize_rhs(&mut a, &mut b, n, &mut budget)?;

    let mut tableau = vec![vec![zero(); tableau_cols]; m];
    for row in 0..m {
        for column in 0..n {
            tableau[row][column] = a[row][column].clone();
        }
        tableau[row][n + row] = one();
        tableau[row][total] = b[row].clone();
    }
    let mut basis: Vec<usize> = (0..m).map(|row| n + row).collect();
    let is_artificial = |column: usize| column >= n;
    let mut reduced_costs = initial_reduced_costs(&tableau, total, is_artificial, &mut budget)?;

    let mut pivots = 0usize;
    loop {
        let Some(entering) = reduced_costs.iter().position(Signed::is_negative) else {
            if ay_core::debug_channel_active(ay_core::DebugChannel::Nia) {
                safe_eprintln!("[NIA] SOS LP pivots={pivots} m={m} n={n} total={total}");
            }
            break;
        };
        if !budget.charge_pivot() {
            return None;
        }
        pivots += 1;
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

    let mut objective = zero();
    for row in 0..m {
        if is_artificial(basis[row]) {
            objective = lp_add(&objective, &tableau[row][total], &mut budget)?;
        }
    }
    if !objective.is_zero() {
        return None;
    }
    let mut solution = vec![zero(); n];
    for row in 0..m {
        if basis[row] < n {
            solution[basis[row]] = tableau[row][total].clone();
        }
    }
    Some(solution)
}

fn normalize_rhs(
    a: &mut [Vec<BigRational>],
    b: &mut [BigRational],
    n: usize,
    budget: &mut SosLpBudget,
) -> Option<()> {
    for row in 0..a.len() {
        if b[row].is_negative() {
            for column in 0..n {
                a[row][column] = lp_neg(&a[row][column], budget)?;
            }
            b[row] = lp_neg(&b[row], budget)?;
        }
    }
    Some(())
}

fn initial_reduced_costs(
    tableau: &[Vec<BigRational>],
    total: usize,
    is_artificial: impl Fn(usize) -> bool,
    budget: &mut SosLpBudget,
) -> Option<Vec<BigRational>> {
    let mut costs = Vec::with_capacity(total);
    for column in 0..total {
        let mut cost = if is_artificial(column) { one() } else { zero() };
        for row in tableau {
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
    budget: &mut SosLpBudget,
) -> Option<usize> {
    let mut leaving = None;
    let mut best = None;
    for row in 0..tableau.len() {
        if tableau[row][entering].is_positive() {
            let ratio = lp_div(&tableau[row][rhs_column], &tableau[row][entering], budget)?;
            let take = match &best {
                None => true,
                Some(current) => {
                    ratio < *current
                        || (ratio == *current && leaving.is_some_and(|old| basis[row] < basis[old]))
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
    budget: &mut SosLpBudget,
) -> Option<()> {
    let pivot = tableau[leaving][entering].clone();
    if !pivot.is_one() {
        for column in 0..=total {
            if !tableau[leaving][column].is_zero() {
                tableau[leaving][column] = lp_div(&tableau[leaving][column], &pivot, budget)?;
            }
        }
    }
    let support: Vec<usize> = (0..=total)
        .filter(|&column| !tableau[leaving][column].is_zero())
        .collect();
    for row in 0..tableau.len() {
        if row != leaving && !tableau[row][entering].is_zero() {
            let factor = tableau[row][entering].clone();
            for &column in &support {
                let delta = lp_mul(&factor, &tableau[leaving][column], budget)?;
                tableau[row][column] = lp_sub(&tableau[row][column], &delta, budget)?;
            }
        }
    }
    if !reduced_costs[entering].is_zero() {
        let factor = reduced_costs[entering].clone();
        for &column in &support {
            if column < total {
                let delta = lp_mul(&factor, &tableau[leaving][column], budget)?;
                reduced_costs[column] = lp_sub(&reduced_costs[column], &delta, budget)?;
            }
        }
    }
    Some(())
}

pub(super) fn lp_add(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left + right)
}

pub(super) fn lp_sub(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left - right)
}

pub(super) fn lp_mul(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget,
) -> Option<BigRational> {
    bounded_binary(left, right, budget, |left, right| left * right)
}

fn lp_div(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget,
) -> Option<BigRational> {
    if right.is_zero() {
        return None;
    }
    bounded_binary(left, right, budget, |left, right| left / right)
}

fn bounded_binary(
    left: &BigRational,
    right: &BigRational,
    budget: &mut SosLpBudget,
    operation: impl FnOnce(&BigRational, &BigRational) -> BigRational,
) -> Option<BigRational> {
    if !budget.charge_updates(1) {
        return None;
    }
    let result = operation(left, right);
    rational_fits(&result).then_some(result)
}

fn lp_neg(value: &BigRational, budget: &mut SosLpBudget) -> Option<BigRational> {
    if !budget.charge_updates(1) {
        return None;
    }
    let result = -value;
    rational_fits(&result).then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sos::budget::{MAX_SOS_COEFFICIENT_BITS, MAX_SOS_LP_CELLS};
    use num_bigint::BigInt;

    #[test]
    fn oversized_tableau_declines_before_allocation() {
        let rows = 256usize;
        let columns = 1usize;
        assert!(rows * (columns + rows + 1) > MAX_SOS_LP_CELLS);
        assert!(lp_phase1_feasible(
            vec![vec![zero(); columns]; rows],
            vec![zero(); rows],
            columns,
        )
        .is_none());
    }

    #[test]
    fn empty_tableau_rejects_unbounded_solution_dimension() {
        assert!(lp_phase1_feasible(Vec::new(), Vec::new(), usize::MAX).is_none());
    }

    #[test]
    fn overwide_input_coefficient_declines() {
        let over_limit =
            BigRational::from_integer(BigInt::from(1u8) << MAX_SOS_COEFFICIENT_BITS as usize);
        assert!(lp_phase1_feasible(vec![vec![over_limit]], vec![zero()], 1).is_none());
    }
}
