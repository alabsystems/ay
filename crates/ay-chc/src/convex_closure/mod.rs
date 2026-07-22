// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Convex Closure for multi-lemma generalization
//!
//! This module implements convex closure computation for PDR lemma generalization.
//! Based on Z3 Spacer's approach (spacer_convex_closure.cpp) by Hari Govind and
//! Arie Gurfinkel.
//!
//! The algorithm:
//! 1. Collect substitution data points from multiple lemmas for the same predicate
//! 2. Build a matrix where each row is a data point
//! 3. Compute the kernel (null space) to find linear dependencies
//! 4. Generate explicit constraints (bounds, equalities) from the kernel
//!
//! Rational arithmetic is in `rational.rs`, matrix operations in `matrix.rs`.

mod matrix;
pub(crate) mod rational;

pub(crate) use matrix::Matrix;
pub(crate) use rational::Rational;

use crate::{ChcExpr, ChcSort, ChcVar};

/// Result of convex closure computation
#[derive(Debug, Clone)]
pub(crate) struct ConvexClosureResult {
    /// Linear equalities discovered (e.g., x + y = 10)
    pub(crate) equalities: Vec<ChcExpr>,
    /// Bounds discovered (e.g., x >= 0, x <= 10)
    pub(crate) bounds: Vec<ChcExpr>,
    /// Divisibility/modular constraints (e.g., x mod 2 = 0)
    pub(crate) divisibility: Vec<ChcExpr>,
}

impl ConvexClosureResult {
    pub(crate) fn empty() -> Self {
        Self {
            equalities: Vec::new(),
            bounds: Vec::new(),
            divisibility: Vec::new(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.equalities.is_empty() && self.bounds.is_empty() && self.divisibility.is_empty()
    }
}

/// Convex closure computation engine
pub(crate) struct ConvexClosure {
    /// Data matrix: each row is a data point, each column is a variable + constant
    data: Matrix,
    /// Variables corresponding to columns (last column is constant 1)
    vars: Vec<ChcVar>,
}

impl ConvexClosure {
    /// Create a new convex closure engine
    pub(crate) fn new() -> Self {
        Self {
            data: Matrix::new(0),
            vars: Vec::new(),
        }
    }

    /// Reset the engine with a new set of variables
    pub(crate) fn reset(&mut self, vars: Vec<ChcVar>) {
        self.vars = vars;
        self.data.reset(self.vars.len() + 1); // +1 for constant column
    }

    /// Add a data point (values for each variable)
    pub(crate) fn add_data_point(&mut self, values: &[i64]) {
        assert_eq!(values.len(), self.vars.len());
        let mut row: Vec<Rational> = values.iter().map(|&v| Rational::from_int(v)).collect();
        row.push(Rational::one()); // constant column
        self.data.add_row(row);
    }

    /// Compute convex closure from collected data points
    pub(crate) fn compute(&mut self) -> ConvexClosureResult {
        if self.data.num_rows() < 2 {
            return ConvexClosureResult::empty();
        }

        let mut result = ConvexClosureResult::empty();

        // 1. Compute linear dependencies (kernel)
        if let Some(deps) = self.data.compute_linear_deps() {
            // Each row in deps represents an equality
            for row_idx in 0..deps.num_rows() {
                let row = deps.get_row(row_idx);
                if let Some(eq) = self.row_to_equality(row) {
                    result.equalities.push(eq);
                }
            }
        }

        // 2. Compute bounds for each variable (1D convex closure)
        for (col_idx, var) in self.vars.iter().enumerate() {
            let col_data = self.data.get_col(col_idx);

            // Get min and max values
            let min = col_data
                .iter()
                .min()
                .and_then(|r| r.to_i64())
                .unwrap_or(i64::MIN);
            let max = col_data
                .iter()
                .max()
                .and_then(|r| r.to_i64())
                .unwrap_or(i64::MAX);

            if min != i64::MIN {
                result.bounds.push(Self::lower_bound_expr(var, min));
            }
            if max != i64::MAX {
                result.bounds.push(Self::upper_bound_expr(var, max));
            }

            // 3. Check for divisibility constraints (e.g., all values mod k = r)
            if col_data.len() >= 2 {
                if let Some((divisor, remainder)) = self.infer_divisibility(&col_data) {
                    if divisor > 1 {
                        result
                            .divisibility
                            .push(Self::divisibility_expr(var, divisor, remainder));
                    }
                }
            }
        }

        result
    }

    fn lower_bound_expr(var: &ChcVar, min: i64) -> ChcExpr {
        match var.sort {
            ChcSort::Int => ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(min))),
            ChcSort::BitVec(width) => ChcExpr::bv_ule(
                ChcExpr::BitVec(bitvec_bits_from_i64(min, width), width),
                ChcExpr::var(var.clone()),
            ),
            _ => ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(min))),
        }
    }

    fn upper_bound_expr(var: &ChcVar, max: i64) -> ChcExpr {
        match var.sort {
            ChcSort::Int => ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(max))),
            ChcSort::BitVec(width) => ChcExpr::bv_ule(
                ChcExpr::var(var.clone()),
                ChcExpr::BitVec(bitvec_bits_from_i64(max, width), width),
            ),
            _ => ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(max))),
        }
    }

    fn divisibility_expr(var: &ChcVar, divisor: i64, remainder: i64) -> ChcExpr {
        match var.sort {
            ChcSort::Int => ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(divisor))),
                ChcExpr::Int(i128::from(remainder)),
            ),
            ChcSort::BitVec(width) => ChcExpr::eq(
                ChcExpr::bv_urem(
                    ChcExpr::var(var.clone()),
                    ChcExpr::BitVec(bitvec_bits_from_i64(divisor, width), width),
                ),
                ChcExpr::BitVec(bitvec_bits_from_i64(remainder, width), width),
            ),
            _ => ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(i128::from(divisor))),
                ChcExpr::Int(i128::from(remainder)),
            ),
        }
    }

    /// Convert a kernel row to an equality expression
    /// Row format: [coeff_0, coeff_1, ..., coeff_n, offset]
    /// Represents: coeff_0*var_0 + coeff_1*var_1 + ... + offset = 0
    fn row_to_equality(&self, row: &[Rational]) -> Option<ChcExpr> {
        // The current convex-closure equality pipeline is arithmetic-only.
        // Bounds/divisibility have explicit BV encodings, but affine equalities
        // still use `neg`/`mul` over terms. Emitting those rows for BitVec vars
        // produces malformed BV formulas like `(- x)` that later panic during
        // SMT conversion. Keep BV convex closure on the supported lower/upper
        // bound and divisibility lanes instead.
        if row
            .iter()
            .take(self.vars.len())
            .enumerate()
            .any(|(i, coeff)| !coeff.is_zero() && matches!(self.vars[i].sort, ChcSort::BitVec(_)))
        {
            return None;
        }

        let mut terms: Vec<ChcExpr> = Vec::new();
        let mut const_term: i64 = 0;

        for (i, &coeff) in row.iter().enumerate() {
            if coeff.is_zero() {
                continue;
            }

            let coeff_i64 = coeff.to_i64()?;

            if i < self.vars.len() {
                // Variable term
                let var_expr = ChcExpr::var(self.vars[i].clone());
                let term = if coeff_i64 == 1 {
                    var_expr
                } else if coeff_i64 == -1 {
                    ChcExpr::neg(var_expr)
                } else {
                    ChcExpr::mul(ChcExpr::Int(i128::from(coeff_i64)), var_expr)
                };
                terms.push(term);
            } else {
                // Constant term
                const_term = coeff_i64;
            }
        }

        if terms.is_empty() {
            return None;
        }

        // Build: terms = -const_term
        // i.e., coeff_0*var_0 + coeff_1*var_1 + ... = -offset
        let lhs = if terms.len() == 1 {
            terms.pop().expect("len == 1")
        } else {
            terms.into_iter().reduce(ChcExpr::add).expect("len > 1")
        };

        let rhs = ChcExpr::Int(i128::from(-const_term));
        Some(ChcExpr::eq(lhs, rhs))
    }

    /// Infer divisibility constraint: find m, d such that all values satisfy val mod m = d
    fn infer_divisibility(&self, col_data: &[Rational]) -> Option<(i64, i64)> {
        let values: Vec<i64> = col_data.iter().filter_map(|r| r.to_i64()).collect();
        if values.len() < 2 {
            return None;
        }

        // Check for even/odd first (m = 2)
        let first_mod2 = values[0].rem_euclid(2);
        if values.iter().all(|&v| v.rem_euclid(2) == first_mod2) {
            return Some((2, first_mod2));
        }

        // Try divisors up to 100
        const MAX_DIV: i64 = 100;
        let min_val = *values.iter().min().expect("len >= 2");

        let min_abs = min_val.saturating_abs();
        for m in 3..=MAX_DIV.min(min_abs.saturating_add(1)) {
            let first_mod = values[0].rem_euclid(m);
            if values.iter().all(|&v| v.rem_euclid(m) == first_mod) {
                return Some((m, first_mod));
            }
        }

        None
    }
}

impl Default for ConvexClosure {
    fn default() -> Self {
        Self::new()
    }
}

fn bitvec_bits_from_i64(value: i64, width: u32) -> u128 {
    if width >= 128 {
        (i128::from(value)) as u128
    } else {
        let modulus = 1i128 << width;
        (i128::from(value).rem_euclid(modulus)) as u128
    }
}

#[cfg(test)]
mod tests;
