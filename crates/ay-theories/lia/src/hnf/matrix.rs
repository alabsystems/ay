// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dense integer matrix for HNF computation.

use num_bigint::BigInt;
use num_traits::Zero;

/// A dense integer matrix for HNF computation
#[derive(Debug, Clone)]
pub(crate) struct IntMatrix {
    /// Row-major storage
    data: Vec<BigInt>,
    /// Number of rows
    rows: usize,
    /// Number of columns
    cols: usize,
    /// Row permutation tracking (for basis identification)
    row_perm: Vec<usize>,
    /// Column permutation tracking
    col_perm: Vec<usize>,
}

impl IntMatrix {
    /// Create a zero matrix
    pub(crate) fn new(rows: usize, cols: usize) -> Self {
        Self {
            data: vec![BigInt::zero(); rows * cols],
            rows,
            cols,
            row_perm: (0..rows).collect(),
            col_perm: (0..cols).collect(),
        }
    }

    /// Get element at (row, col)
    pub(crate) fn get(&self, row: usize, col: usize) -> &BigInt {
        &self.data[row * self.cols + col]
    }

    /// Set element at (row, col)
    pub(crate) fn set(&mut self, row: usize, col: usize, val: BigInt) {
        self.data[row * self.cols + col] = val;
    }

    /// Number of rows
    pub(crate) fn row_count(&self) -> usize {
        self.rows
    }

    /// Number of columns
    pub(crate) fn col_count(&self) -> usize {
        self.cols
    }

    /// Transpose rows i and j
    pub(crate) fn transpose_rows(&mut self, i: usize, j: usize) {
        if i == j {
            return;
        }
        for col in 0..self.cols {
            let idx_i = i * self.cols + col;
            let idx_j = j * self.cols + col;
            self.data.swap(idx_i, idx_j);
        }
        self.row_perm.swap(i, j);
    }

    /// Transpose columns i and j
    pub(crate) fn transpose_columns(&mut self, i: usize, j: usize) {
        if i == j {
            return;
        }
        for row in 0..self.rows {
            let idx_i = row * self.cols + i;
            let idx_j = row * self.cols + j;
            self.data.swap(idx_i, idx_j);
        }
        self.col_perm.swap(i, j);
    }

    /// Get the original row index after permutations
    pub(crate) fn adjust_row(&self, i: usize) -> usize {
        self.row_perm[i]
    }

    /// Get the original column index after permutations
    pub(crate) fn adjust_col(&self, i: usize) -> usize {
        self.col_perm[i]
    }

    /// Shrink matrix to only the specified rows
    pub(crate) fn shrink_to_rows(&mut self, basis_rows: &[usize]) {
        let new_rows = basis_rows.len();
        let mut new_data = vec![BigInt::zero(); new_rows * self.cols];
        let mut new_perm = Vec::with_capacity(new_rows);

        for (new_i, &old_i) in basis_rows.iter().enumerate() {
            for col in 0..self.cols {
                new_data[new_i * self.cols + col].clone_from(&self.data[old_i * self.cols + col]);
            }
            new_perm.push(self.row_perm[old_i]);
        }

        self.data = new_data;
        self.rows = new_rows;
        self.row_perm = new_perm;
    }
}
