// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hoisted equation basis for the affine implication accelerator
//! (#affine-rref-hoist).
//!
//! `check_affine_disequality_implication` used to redo BOTH exact
//! eliminations — the equation rows, and the equation rows plus the target —
//! for every disequality on every theory check, although the equation rows
//! are the same for all of them. Measured on the deductive-checks set-fold
//! obligation (`C_sets/87167-00066`, BV/LIA bridge lane, deductive-checks posture:
//! cores on, proofs off) that was ~95% of a 16 s stretch that never found an
//! implication, and pushed the refutation past deductive-checks's 30 s deadline.
//!
//! Here the equation rows are reduced ONCE to a reduced row-echelon basis
//! and each target is only REDUCED against it — an exact span test used
//! purely as a FILTER: a target proved outside the span cannot pass the
//! trusted `rank(rows) == rank(rows + target)` test either, and every
//! emitted conflict is still decided by that unchanged trusted test.

use super::*;

/// Equation variables (sorted by term id) and the reduced pivot rows over
/// them as `(pivot column, row)` pairs (last column: the constant).
pub(super) type AffineBasis = (Vec<TermId>, Vec<(usize, Vec<BigRational>)>);

impl LiaSolver<'_> {
    /// The reduced row-echelon basis of `equations` over their own variables,
    /// or `None` when it is not computed under the same structural,
    /// coefficient-size and fuel bounds the trusted rank test applies.
    /// `None` only disables the filter.
    pub(super) fn affine_equation_basis(
        &self,
        equations: &[AffineEquation],
    ) -> Option<AffineBasis> {
        if equations.iter().any(|equation| {
            !Self::integer_is_bounded(&equation.constant)
                || equation
                    .coeffs
                    .values()
                    .any(|coefficient| !Self::integer_is_bounded(coefficient))
        }) {
            return None;
        }
        let mut vars: Vec<TermId> = equations
            .iter()
            .flat_map(|equation| equation.coeffs.keys().copied())
            .collect::<HashSet<TermId>>()
            .into_iter()
            .collect();
        if vars.len() > MAX_AFFINE_VARS {
            return None;
        }
        vars.sort_unstable_by_key(|term| term.0);
        let rows: Vec<Vec<BigRational>> = equations
            .iter()
            .map(|equation| Self::affine_row(&vars, &equation.coeffs, &equation.constant))
            .collect();
        let mut fuel = AFFINE_RANK_FUEL;
        let mut should_abort = || self.should_timeout();
        let basis = Self::rational_rref(rows, &mut fuel, &mut should_abort)?;
        Some((vars, basis))
    }

    /// Whether the disequality's row `coeffs · x + constant = 0` is
    /// PROVABLY outside the span of the equation basis, so the trusted
    /// implication test cannot succeed for it. `false` means "possibly
    /// implied" — including every undecided reduction and a missing basis —
    /// and the caller then runs the trusted test exactly as before.
    pub(super) fn affine_basis_excludes(
        &self,
        basis: Option<&AffineBasis>,
        target: &AffineDisequality,
    ) -> bool {
        let Some((vars, basis)) = basis else {
            return false;
        };
        let (target_coeffs, target_constant) = (&target.coeffs, &target.constant);
        // A variable no equation mentions has an all-zero basis column, so a
        // nonzero target coefficient on it can never be cancelled.
        if target_coeffs.iter().any(|(var, coeff)| {
            !coeff.is_zero() && vars.binary_search_by_key(&var.0, |v| v.0).is_err()
        }) {
            return true;
        }
        if !Self::integer_is_bounded(target_constant)
            || target_coeffs
                .values()
                .any(|coefficient| !Self::integer_is_bounded(coefficient))
        {
            return false;
        }
        let row = Self::affine_row(vars, target_coeffs, target_constant);
        let mut fuel = AFFINE_RANK_FUEL;
        let mut should_abort = || self.should_timeout();
        Self::affine_basis_spans(basis, &row, &mut fuel, &mut should_abort) == Some(false)
    }

    /// The Gauss-Jordan elimination behind [`Self::rational_rank`], returning
    /// the fully reduced pivot rows as `(pivot column, row)` pairs in pivot
    /// order. Every pivot row is normalized (`row[col] == 1`) and is zero in
    /// every OTHER pivot column — the reduced-row-echelon invariant
    /// [`Self::affine_basis_spans`] relies on. `None` means "not computed"
    /// (cancellation, fuel, coefficient growth, shape mismatch).
    pub(crate) fn rational_rref<F: FnMut() -> bool>(
        mut rows: Vec<Vec<BigRational>>,
        fuel: &mut usize,
        should_abort: &mut F,
    ) -> Option<Vec<(usize, Vec<BigRational>)>> {
        if should_abort() {
            return None;
        }
        if rows.is_empty() {
            return Some(Vec::new());
        }

        let row_count = rows.len();
        let col_count = rows[0].len();
        if rows.iter().any(|row| row.len() != col_count)
            || !rows.iter().flatten().all(Self::rational_is_bounded)
        {
            return None;
        }
        let mut rank = 0;
        let mut pivot_columns = Vec::new();

        for col in 0..col_count {
            if should_abort() {
                return None;
            }
            let Some(pivot) = (rank..row_count).find(|&row| !rows[row][col].is_zero()) else {
                continue;
            };
            rows.swap(rank, pivot);
            pivot_columns.push(col);

            let pivot_value = rows[rank][col].clone();
            for cell in rows[rank].iter_mut().take(col_count).skip(col) {
                if !Self::affine_step_allowed(fuel, should_abort) {
                    return None;
                }
                *cell = Self::bounded_rational_div(cell, &pivot_value)?;
            }
            let pivot_tail: Vec<_> = rows[rank][col..col_count].to_vec();

            for (row, row_values) in rows.iter_mut().enumerate().take(row_count) {
                if should_abort() {
                    return None;
                }
                if row == rank || row_values[col].is_zero() {
                    continue;
                }
                let factor = row_values[col].clone();
                for (cell, pivot_cell) in row_values
                    .iter_mut()
                    .take(col_count)
                    .skip(col)
                    .zip(&pivot_tail)
                {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_sub(cell, &factor, pivot_cell)?;
                }
            }

            rank += 1;
            if rank == row_count {
                break;
            }
        }

        // Rows past `rank` are zero (or were never reached because every row
        // already holds a pivot).
        rows.truncate(rank);
        Some(pivot_columns.into_iter().zip(rows).collect())
    }

    /// Whether `target` lies in the row span of the reduced basis `basis`
    /// (as produced by [`Self::rational_rref`] over rows of the same width).
    ///
    /// Subtracting `target[col] * row` for each pivot leaves every pivot
    /// column of the target zero (each pivot row is 1 in its own pivot column
    /// and 0 in every other one), so the remainder is zero iff the target is
    /// a linear combination of the basis rows — i.e. iff appending it would
    /// not raise the rank. `None` means "not decided" (fuel, cancellation,
    /// coefficient growth, shape mismatch), never "not in span".
    pub(crate) fn affine_basis_spans<F: FnMut() -> bool>(
        basis: &[(usize, Vec<BigRational>)],
        target: &[BigRational],
        fuel: &mut usize,
        should_abort: &mut F,
    ) -> Option<bool> {
        if should_abort()
            || basis
                .iter()
                .any(|(col, row)| row.len() != target.len() || *col >= row.len())
            || !target.iter().all(Self::rational_is_bounded)
        {
            return None;
        }
        let mut remainder = target.to_vec();
        for (col, row) in basis {
            let factor = remainder[*col].clone();
            if factor.is_zero() {
                continue;
            }
            for (cell, pivot_cell) in remainder.iter_mut().zip(row) {
                if !Self::affine_step_allowed(fuel, should_abort) {
                    return None;
                }
                *cell = Self::bounded_rational_scaled_sub(cell, &factor, pivot_cell)?;
            }
        }
        Some(remainder.iter().all(Zero::is_zero))
    }
}
