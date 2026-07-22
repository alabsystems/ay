// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Matrix of rational numbers with Gaussian elimination and kernel computation.
//!
//! Used by `ConvexClosure` to discover linear dependencies across data points.
//! Reference: Z3 Spacer's spacer_arith_kernel.cpp (kernel_ffe).

use ay_core::kani_compat::DetHashSet as FxHashSet;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::rational::Rational;

/// Matrix of rational numbers
#[derive(Debug, Clone)]
pub(crate) struct Matrix {
    rows: Vec<Vec<Rational>>,
    num_cols: usize,
}

impl Matrix {
    /// Create a new empty matrix with the specified number of columns
    pub(crate) fn new(num_cols: usize) -> Self {
        Self {
            rows: Vec::new(),
            num_cols,
        }
    }

    pub(crate) fn num_rows(&self) -> usize {
        self.rows.len()
    }

    pub(crate) fn add_row(&mut self, row: Vec<Rational>) {
        assert_eq!(row.len(), self.num_cols);
        self.rows.push(row);
    }

    pub(crate) fn get_row(&self, row: usize) -> &[Rational] {
        &self.rows[row]
    }

    /// Get a column as a vector
    pub(crate) fn get_col(&self, col: usize) -> Vec<Rational> {
        self.rows.iter().map(|r| r[col]).collect()
    }

    /// Reset the matrix to have a new number of columns, clearing all rows
    pub(crate) fn reset(&mut self, num_cols: usize) {
        self.num_cols = num_cols;
        self.rows.clear();
    }

    /// Perform Gaussian elimination to compute row echelon form
    /// Returns the rank of the matrix
    /// Part of full matrix library (tested but not used in production - uses compute_linear_deps instead)
    #[cfg(test)]
    pub(crate) fn gaussian_elimination(&mut self) -> usize {
        if self.rows.is_empty() || self.num_cols == 0 {
            return 0;
        }

        let mut pivot_row = 0;
        let mut pivot_col = 0;

        while pivot_row < self.rows.len() && pivot_col < self.num_cols {
            // Find the row with largest absolute value in this column
            let mut max_row = pivot_row;
            let mut max_val = self.rows[pivot_row][pivot_col].abs();

            for row in (pivot_row + 1)..self.rows.len() {
                let abs_val = self.rows[row][pivot_col].abs();
                if abs_val > max_val {
                    max_val = abs_val;
                    max_row = row;
                }
            }

            if max_val.is_zero() {
                // This column is all zeros below the pivot, skip it
                pivot_col += 1;
                continue;
            }

            // Swap rows
            self.rows.swap(pivot_row, max_row);

            // Normalize the pivot row
            let pivot = self.rows[pivot_row][pivot_col];
            if !pivot.is_one() {
                for col in 0..self.num_cols {
                    self.rows[pivot_row][col] = self.rows[pivot_row][col] / pivot;
                }
            }

            // Eliminate this column in all other rows
            for row in 0..self.rows.len() {
                if row != pivot_row {
                    let factor = self.rows[row][pivot_col];
                    if !factor.is_zero() {
                        for col in 0..self.num_cols {
                            let sub = factor * self.rows[pivot_row][col];
                            self.rows[row][col] = self.rows[row][col] - sub;
                        }
                    }
                }
            }

            pivot_row += 1;
            pivot_col += 1;
        }

        pivot_row // rank
    }

    /// Compute linear dependencies (kernel/nullspace) using true RREF-based algorithm.
    /// Uses BigRational for arbitrary precision to avoid overflow.
    ///
    /// Returns a matrix where each row represents an affine equality:
    /// `row[0]*v_0 + row[1]*v_1 + ... + row[n] = 0` (last entry is the constant term)
    ///
    /// Algorithm: Compute RREF of the matrix, then extract kernel basis from free columns.
    /// Reference: Z3 Spacer's spacer_arith_kernel.cpp (kernel_ffe)
    ///
    /// Note: The input matrix should already contain the constant column (column of 1s)
    /// if affine equalities are desired. This is handled by ConvexClosure::add_data_point.
    #[allow(clippy::needless_range_loop)] // Matrix operations use index for multi-array access
    pub(crate) fn compute_linear_deps(&self) -> Option<Self> {
        if self.rows.len() < 2 {
            return None;
        }

        // Convert to BigRational matrix (no additional columns - data already has constant column)
        let num_cols = self.num_cols;

        let mut aug: Vec<Vec<BigRational>> = self
            .rows
            .iter()
            .map(|row| {
                row.iter()
                    .map(|rat| BigRational::new(BigInt::from(rat.num), BigInt::from(rat.den)))
                    .collect()
            })
            .collect();

        let num_rows = aug.len();

        // Gaussian elimination to RREF with partial pivoting
        let mut pivot_cols: Vec<usize> = Vec::new();
        let mut pivot_row = 0;

        for col in 0..num_cols {
            if pivot_row >= num_rows {
                break;
            }

            // Find pivot (largest absolute value in this column below pivot_row)
            let mut max_row = pivot_row;
            let mut max_val = aug[pivot_row][col].abs();
            for row in (pivot_row + 1)..num_rows {
                let val = aug[row][col].abs();
                if val > max_val {
                    max_val = val;
                    max_row = row;
                }
            }

            if max_val.is_zero() {
                // No pivot in this column - it's a free column
                continue;
            }

            // Swap rows
            aug.swap(pivot_row, max_row);

            // Normalize pivot row
            let pivot_val = aug[pivot_row][col].clone();
            for c in 0..num_cols {
                aug[pivot_row][c] = &aug[pivot_row][c] / &pivot_val;
            }

            // Eliminate other rows
            for row in 0..num_rows {
                if row != pivot_row {
                    let factor = aug[row][col].clone();
                    if !factor.is_zero() {
                        for c in 0..num_cols {
                            let sub = &factor * &aug[pivot_row][c];
                            aug[row][c] = &aug[row][c] - &sub;
                        }
                    }
                }
            }

            pivot_cols.push(col);
            pivot_row += 1;
        }

        // Identify free columns (non-pivot columns).
        // Use HashSet for O(1) lookup instead of Vec::contains O(n) (#2956 Finding 7).
        let pivot_set: FxHashSet<usize> = pivot_cols.iter().copied().collect();
        let free_cols: Vec<usize> = (0..num_cols).filter(|c| !pivot_set.contains(c)).collect();

        if free_cols.is_empty() {
            // Full rank - no kernel vectors
            return None;
        }

        // For each free column, construct a kernel basis vector
        let mut deps = Self::new(num_cols);

        for &free_col in &free_cols {
            let mut kernel_vec: Vec<BigRational> = vec![BigRational::zero(); num_cols];
            kernel_vec[free_col] = BigRational::one();

            // For each pivot column, compute its value from RREF
            for (i, &pivot_col) in pivot_cols.iter().enumerate() {
                // Row i has pivot at pivot_col
                // x_{pivot_col} = - sum_{j in free_cols} aug[i][j] * x_j
                let mut val = BigRational::zero();
                for &fc in &free_cols {
                    if !aug[i][fc].is_zero() {
                        val -= &aug[i][fc] * &kernel_vec[fc];
                    }
                }
                kernel_vec[pivot_col] = val;
            }

            // Debug: verify kernel vector satisfies A * x = 0 for all rows
            #[cfg(debug_assertions)]
            {
                for row in &self.rows {
                    let dot: BigRational = row
                        .iter()
                        .zip(kernel_vec.iter())
                        .map(|(a, x)| {
                            let a_big = BigRational::new(BigInt::from(a.num), BigInt::from(a.den));
                            &a_big * x
                        })
                        .fold(BigRational::zero(), |acc, v| acc + v);
                    debug_assert!(
                        dot.is_zero(),
                        "Kernel vector does not satisfy A*x=0: dot={dot:?}"
                    );
                }
            }

            // Normalize to integers: multiply by LCM of denominators, then divide by GCD
            let kernel_int = Self::normalize_kernel_to_integers(&kernel_vec);

            // Convert back to Rational, skipping if any coefficient overflows i64
            let row: Option<Vec<Rational>> = kernel_int
                .iter()
                .map(|bi| {
                    // Use TryFrom for safe conversion; skip kernel vector if overflow
                    i64::try_from(bi).ok().map(Rational::from_int)
                })
                .collect();

            // Skip if conversion failed (coefficients too large) or trivial (all-zero)
            if let Some(row) = row {
                if !row.iter().all(Rational::is_zero) {
                    deps.add_row(row);
                }
            }
            // Note: If conversion fails, this kernel vector is skipped. This can happen
            // with extreme values, but GCD normalization should keep coefficients small.
        }

        if deps.num_rows() > 0 {
            Some(deps)
        } else {
            None
        }
    }

    /// Normalize a kernel vector (BigRational) to integer coefficients.
    fn normalize_kernel_to_integers(vec: &[BigRational]) -> Vec<BigInt> {
        if vec.is_empty() || vec.iter().all(Zero::is_zero) {
            return vec.iter().map(|_| BigInt::zero()).collect();
        }

        // Compute LCM of denominators
        let mut lcm_den = BigInt::one();
        for r in vec {
            if !r.is_zero() {
                lcm_den = num_integer::lcm(lcm_den, r.denom().clone());
            }
        }

        // Multiply each entry by lcm_den (clears denominators)
        let mut int_vec: Vec<BigInt> = vec
            .iter()
            .map(|r| {
                if r.is_zero() {
                    BigInt::zero()
                } else {
                    r.numer() * (&lcm_den / r.denom())
                }
            })
            .collect();

        // Compute GCD of all non-zero entries
        let mut gcd_num = BigInt::zero();
        for bi in &int_vec {
            if !bi.is_zero() {
                gcd_num = num_integer::gcd(gcd_num.clone(), bi.abs());
            }
        }

        // Divide by GCD
        if !gcd_num.is_zero() && gcd_num != BigInt::one() {
            for bi in &mut int_vec {
                *bi = &*bi / &gcd_num;
            }
        }

        // Ensure leading non-zero coefficient is positive for consistency
        if let Some(first_nonzero) = int_vec.iter().find(|bi| !bi.is_zero()) {
            if first_nonzero.is_negative() {
                for bi in &mut int_vec {
                    *bi = -bi.clone();
                }
            }
        }

        int_vec
    }
}
