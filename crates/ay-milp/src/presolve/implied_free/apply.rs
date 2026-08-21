// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn apply_candidate(
    work: &mut Work,
    candidate: Candidate,
    guard: &ResourceGuard,
) -> Option<()> {
    if guard.stopped() {
        return None;
    }
    let pivot_objective = work.objective[candidate.pivot].clone();
    let next_recovery_terms = work.recovery_terms.checked_add(candidate.terms.len())?;
    if next_recovery_terms > work.recovery_term_cap {
        return None;
    }
    let next_delta = &work.const_delta + &pivot_objective * &candidate.constant;
    if !rational_fits(&next_delta) {
        return None;
    }
    let objective_updates = objective_updates(work, &candidate, &pivot_objective, guard)?;
    let (row_updates, next_nnz) = row_updates(work, &candidate, guard)?;

    work.rows[candidate.row].active = false;
    work.rows[candidate.row].coeffs.clear();
    for (row_index, row) in row_updates {
        work.rows[row_index] = row;
    }
    for (column, value) in objective_updates {
        work.objective[column] = value;
    }
    work.objective[candidate.pivot] = BigRational::zero();
    work.cols[candidate.pivot].active = false;
    work.active_nnz = next_nnz;
    work.const_delta = next_delta;
    work.recovery_terms = next_recovery_terms;
    work.recover.push(AffineRecovery::Equality {
        row: candidate.row,
        col: candidate.pivot,
        constant: candidate.constant,
        terms: candidate.terms,
    });
    Some(())
}

fn objective_updates(
    work: &Work,
    candidate: &Candidate,
    pivot_objective: &BigRational,
    guard: &ResourceGuard,
) -> Option<Vec<(usize, BigRational)>> {
    let mut updates = Vec::new();
    updates.try_reserve_exact(candidate.terms.len()).ok()?;
    for (term_index, (column, coefficient)) in candidate.terms.iter().enumerate() {
        if term_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        let value = &work.objective[*column] + pivot_objective * coefficient;
        if !rational_fits(&value) || (!value.is_zero() && exact_f64(&value).is_none()) {
            return None;
        }
        updates.push((*column, value));
    }
    Some(updates)
}

fn row_updates(
    work: &Work,
    candidate: &Candidate,
    guard: &ResourceGuard,
) -> Option<(Vec<(usize, WorkRow)>, usize)> {
    let mut updates = Vec::new();
    updates.try_reserve(work.rows.len()).ok()?;
    let mut next_nnz = work
        .active_nnz
        .checked_sub(work.rows[candidate.row].coeffs.len())?;
    for (row_index, row) in work.rows.iter().enumerate() {
        if row_index.is_multiple_of(128) && guard.stopped() {
            return None;
        }
        if row_index == candidate.row || !row.active {
            continue;
        }
        let Ok(position) = row
            .coeffs
            .binary_search_by_key(&candidate.pivot, |&(column, _)| column)
        else {
            continue;
        };
        let rewritten = rewrite_row(row, candidate, &row.coeffs[position].1, guard)?;
        next_nnz = next_nnz
            .checked_sub(row.coeffs.len())?
            .checked_add(rewritten.coeffs.len())?;
        if next_nnz > work.nnz_cap {
            return None;
        }
        updates.push((row_index, rewritten));
    }
    Some((updates, next_nnz))
}

fn rewrite_row(
    row: &WorkRow,
    candidate: &Candidate,
    pivot_coefficient: &BigRational,
    guard: &ResourceGuard,
) -> Option<WorkRow> {
    let constant_shift = pivot_coefficient * &candidate.constant;
    if !rational_fits(&constant_shift) {
        return None;
    }
    let mut lower = row.lower.clone();
    let mut upper = row.upper.clone();
    shift_bound(&mut lower, &constant_shift)?;
    shift_bound(&mut upper, &constant_shift)?;
    let coeffs = merged_coefficients(row, candidate, pivot_coefficient, guard)?;
    if coeffs.iter().any(|(_, value)| exact_f64(value).is_none())
        || lower
            .as_ref()
            .is_some_and(|value| exact_f64(value).is_none())
        || upper
            .as_ref()
            .is_some_and(|value| exact_f64(value).is_none())
    {
        return None;
    }
    let active = if coeffs.is_empty() {
        zero_satisfies(&lower, &upper).then_some(false)?
    } else {
        true
    };
    Some(WorkRow {
        active,
        lower,
        upper,
        coeffs,
    })
}

fn merged_coefficients(
    row: &WorkRow,
    candidate: &Candidate,
    pivot_coefficient: &BigRational,
    guard: &ResourceGuard,
) -> Option<Vec<(usize, BigRational)>> {
    let mut merged = BTreeMap::new();
    for (term_index, &(column, ref coefficient)) in row.coeffs.iter().enumerate() {
        if term_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        if column != candidate.pivot {
            merged.insert(column, coefficient.clone());
        }
    }
    for (term_index, (column, coefficient)) in candidate.terms.iter().enumerate() {
        if term_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        let addition = pivot_coefficient * coefficient;
        let value = merged
            .remove(column)
            .map_or_else(|| addition.clone(), |old| old + &addition);
        if !rational_fits(&value) {
            return None;
        }
        if !value.is_zero() {
            merged.insert(*column, value);
        }
    }
    (merged.len() <= MAX_ROW_TERMS).then(|| merged.into_iter().collect())
}
