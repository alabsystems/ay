// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_rational::Rational64;

pub(super) type Matrix = Vec<Vec<Rational64>>;

fn get_pivot_row(matrix: &Matrix, pivot_col: usize, start_row: usize) -> usize {
    matrix[start_row..]
        .iter()
        .position(|row| row[pivot_col] != Rational64::from_integer(0))
        .map_or(matrix.len(), |pos| pos + start_row)
}

fn add_row_with_coeff(to: &mut [Rational64], from: &[Rational64], coeff: Rational64) {
    assert_eq!(
        to.len(),
        from.len(),
        "BUG: row length mismatch in add_row_with_coeff"
    );
    for (dst, src) in to.iter_mut().zip(from.iter()) {
        *dst += coeff * *src;
    }
}

pub(super) fn gaussian_elimination(matrix: &mut Matrix) {
    if matrix.is_empty() || matrix[0].is_empty() {
        return;
    }

    let cols = matrix[0].len();
    assert!(
        matrix.iter().all(|row| row.len() == cols),
        "BUG: matrix rows have inconsistent lengths"
    );
    let mut pivot_row = 0usize;
    let mut pivot_col = 0usize;

    while pivot_col < cols && pivot_row < matrix.len() {
        let next_row = get_pivot_row(matrix, pivot_col, pivot_row);
        if next_row == matrix.len() {
            pivot_col += 1;
            continue;
        }
        if next_row != pivot_row {
            matrix.swap(pivot_row, next_row);
        }

        let pivot_val = matrix[pivot_row][pivot_col];
        let pivot_snapshot = matrix[pivot_row].clone();

        for row in &mut matrix[(pivot_row + 1)..] {
            if row[pivot_col] == Rational64::from_integer(0) {
                continue;
            }
            let factor = -(row[pivot_col] / pivot_val);
            add_row_with_coeff(row, &pivot_snapshot, factor);
        }

        pivot_row += 1;
        pivot_col += 1;
    }
}

fn normalize_row(row: &mut [Rational64], pivot_col: usize) {
    assert!(
        row[pivot_col] != Rational64::from_integer(0),
        "BUG: normalizing row with zero pivot"
    );
    let inv = row[pivot_col].recip();
    for value in &mut row[pivot_col..] {
        *value *= inv;
    }
}

pub(super) fn to_reduced_row_echelon_form(matrix: &mut Matrix) {
    if matrix.is_empty() || matrix[0].is_empty() {
        return;
    }

    let cols = matrix[0].len();
    assert!(
        matrix.iter().all(|row| row.len() == cols),
        "BUG: matrix rows have inconsistent lengths in RREF"
    );

    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut column = 0usize;

    for row in matrix.iter_mut() {
        if column >= row.len() {
            break;
        }
        let pivot_col = (column..row.len()).find(|&idx| row[idx] != Rational64::from_integer(0));
        let Some(pivot_col) = pivot_col else {
            continue;
        };
        column = pivot_col;
        pivot_cols.push(column);
        if row[column] != Rational64::from_integer(1) {
            normalize_row(row, column);
        }
    }

    let mut pivot_idx = pivot_cols.len();
    for row_idx in (0..matrix.len()).rev() {
        if pivot_idx == 0 {
            break;
        }
        let pivot_col = pivot_cols[pivot_idx - 1];
        if matrix[row_idx][pivot_col] == Rational64::from_integer(0) {
            continue;
        }
        pivot_idx -= 1;

        let pivot_snapshot = matrix[row_idx].clone();
        for upper_row_idx in (0..row_idx).rev() {
            let factor = matrix[upper_row_idx][pivot_col];
            if factor == Rational64::from_integer(0) {
                continue;
            }
            add_row_with_coeff(&mut matrix[upper_row_idx], &pivot_snapshot, -factor);
        }
    }
}

pub(super) fn matrix_nullity(matrix: &Matrix) -> usize {
    if matrix.is_empty() {
        return 0;
    }
    let rank = matrix
        .iter()
        .filter(|row| row.iter().any(|x| *x != Rational64::from_integer(0)))
        .count();
    matrix[0].len().saturating_sub(rank)
}

pub(super) fn get_pivot_cols_bitmap(matrix: &Matrix) -> Vec<bool> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Vec::new();
    }

    let cols = matrix[0].len();
    let mut pivot_cols = vec![false; cols];
    let mut row = 0usize;
    for col in 0..cols {
        if row == matrix.len() || matrix[row][col] == Rational64::from_integer(0) {
            pivot_cols[col] = false;
        } else {
            pivot_cols[col] = true;
            row += 1;
        }
    }
    pivot_cols
}

pub(super) fn get_null_basis(matrix: &Matrix) -> Vec<Vec<Rational64>> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Vec::new();
    }

    let pivot_cols = get_pivot_cols_bitmap(matrix);
    let cols = matrix[0].len();
    let mut basis = Vec::new();

    for free_col in 0..cols {
        if pivot_cols[free_col] {
            continue;
        }
        let mut base_vec = Vec::with_capacity(cols);
        let mut pivot_row = 0usize;
        for (col, is_pivot_col) in pivot_cols.iter().enumerate().take(cols) {
            if *is_pivot_col {
                base_vec.push(-matrix[pivot_row][free_col]);
                pivot_row += 1;
            } else if col == free_col {
                base_vec.push(Rational64::from_integer(1));
            } else {
                base_vec.push(Rational64::from_integer(0));
            }
        }
        basis.push(base_vec);
    }

    basis
}

pub(super) fn get_alphas(all_farkas_coeffs: &[Rational64], pivot_cols: &[bool]) -> Vec<Rational64> {
    assert_eq!(
        all_farkas_coeffs.len(),
        pivot_cols.len(),
        "BUG: all_farkas_coeffs length ({}) != pivot_cols length ({})",
        all_farkas_coeffs.len(),
        pivot_cols.len()
    );
    let mut alphas = Vec::new();
    for (idx, coeff) in all_farkas_coeffs.iter().enumerate() {
        if !pivot_cols[idx] {
            alphas.push(*coeff);
        }
    }
    alphas
}

pub(super) fn is_decomposition(
    basis: &[Vec<Rational64>],
    coordinates: &[Rational64],
    original: &[Rational64],
) -> bool {
    assert_eq!(coordinates.len(), basis.len());
    assert!(basis.iter().all(|v| v.len() == original.len()));
    let zero = Rational64::from_integer(0);
    for (i, orig) in original.iter().enumerate() {
        let sum: Rational64 = basis
            .iter()
            .zip(coordinates.iter())
            .fold(zero, |acc, (base_vec, coord)| acc + base_vec[i] * *coord);
        if sum != *orig {
            return false;
        }
    }
    true
}

fn ensure_non_negative_vec(
    base_vec: &mut [Rational64],
    base_vec_index: usize,
    coordinates: &mut [Rational64],
    vec_to_decompose: &[Rational64],
) -> bool {
    for i in 0..base_vec.len() {
        if base_vec[i] < Rational64::from_integer(0) {
            let denom = vec_to_decompose[i];
            if denom <= Rational64::from_integer(0) {
                return false;
            }
            let coeff = (-base_vec[i]) / denom;
            for j in 0..base_vec.len() {
                base_vec[j] += coeff * vec_to_decompose[j];
            }
            let divisor = Rational64::from_integer(1) + (coeff * coordinates[base_vec_index]);
            if divisor == Rational64::from_integer(0) {
                return false;
            }
            for coordinate in coordinates.iter_mut() {
                *coordinate /= divisor;
            }
        }
    }
    true
}

pub(super) fn ensure_non_negative_decomposition(
    basis: &mut [Vec<Rational64>],
    coordinates: &mut [Rational64],
    vec_to_decompose: &[Rational64],
) -> bool {
    assert_eq!(basis.len(), coordinates.len());
    assert!(basis.iter().all(|v| v.len() == vec_to_decompose.len()));
    for (idx, base_vec) in basis.iter_mut().enumerate() {
        if !ensure_non_negative_vec(base_vec, idx, coordinates, vec_to_decompose) {
            return false;
        }
    }
    true
}
