// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear expression representation for LRA solver.
//!
//! Extracted from `types.rs` for code health (#5970).
//! Uses `Rational` (inline i64/i64 with BigRational fallback) instead of
//! `BigRational` to eliminate heap allocation in `compute_expr_interval`
//! hot path (#8800).

use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::rational::Rational;
use crate::types::add_sparse_term_rat;

/// Linear expression: sum(coeff * var) + constant
#[derive(Debug, Clone)]
pub struct LinearExpr {
    /// Variable coefficients
    pub coeffs: Vec<(u32, Rational)>,
    /// Constant term
    pub constant: Rational,
}

impl LinearExpr {
    /// Create an empty expression (constant 0)
    pub fn zero() -> Self {
        Self {
            coeffs: Vec::new(),
            constant: Rational::zero(),
        }
    }

    /// Create expression for a single variable with coefficient 1
    pub fn var(v: u32) -> Self {
        Self {
            coeffs: vec![(v, Rational::one())],
            constant: Rational::zero(),
        }
    }

    /// Create a constant expression from BigRational
    pub fn constant(c: BigRational) -> Self {
        Self {
            coeffs: Vec::new(),
            constant: Rational::from_big(c),
        }
    }

    /// Create a constant expression from Rational (no allocation)
    pub fn constant_rat(c: Rational) -> Self {
        Self {
            coeffs: Vec::new(),
            constant: c,
        }
    }

    /// Get constant as BigRational (for compatibility with code expecting BigRational)
    #[inline]
    pub fn constant_big(&self) -> BigRational {
        self.constant.to_big()
    }

    /// Add another expression to this one
    pub fn add(&mut self, other: &Self) {
        for &(v, ref c) in &other.coeffs {
            self.add_term_rat(v, c.clone());
        }
        self.constant = &self.constant + &other.constant;
    }

    /// Add a scaled expression to this one (BigRational scale for compatibility)
    pub fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        let scale_rat = Rational::from_big(scale.clone());
        self.add_scaled_rat(other, &scale_rat);
    }

    /// Add a scaled expression to this one (Rational scale, no allocation)
    pub fn add_scaled_rat(&mut self, other: &Self, scale: &Rational) {
        for &(v, ref c) in &other.coeffs {
            self.add_term_rat(v, c * scale);
        }
        self.constant = &self.constant + &(&other.constant * scale);
    }

    /// Add a term (variable * coefficient) from BigRational
    pub fn add_term(&mut self, var: u32, coeff: BigRational) {
        self.add_term_rat(var, Rational::from_big(coeff));
    }

    /// Add a term (variable * coefficient) with Rational (no allocation)
    pub fn add_term_rat(&mut self, var: u32, coeff: Rational) {
        add_sparse_term_rat(&mut self.coeffs, var, coeff);
    }

    /// Scale the entire expression (BigRational factor for compatibility)
    pub fn scale(&mut self, factor: &BigRational) {
        let factor_rat = Rational::from_big(factor.clone());
        self.scale_rat(&factor_rat);
    }

    /// Scale the entire expression (Rational factor, no allocation)
    pub fn scale_rat(&mut self, factor: &Rational) {
        for (_, c) in &mut self.coeffs {
            *c = &*c * factor;
        }
        self.constant = &self.constant * factor;
    }

    /// Negate the expression
    pub fn negate(&mut self) {
        for (_, c) in &mut self.coeffs {
            *c = -c.clone();
        }
        self.constant = -self.constant.clone();
    }

    /// Check if this is a constant expression (no variables)
    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Normalize the expression to canonical form:
    /// - Sort coefficients by var_id
    /// - Combine terms with same var_id (already done by add_term, but order may vary)
    /// - Remove zero-coefficient terms
    ///
    /// This enables semantic comparison: `(A+1) - (B+1)` normalizes to same form as `A - B`.
    pub fn normalize(&self) -> Self {
        use std::collections::BTreeMap;

        // Build map combining coefficients for each variable
        let mut coeff_map: BTreeMap<u32, Rational> = BTreeMap::default();
        for &(var, ref coeff) in &self.coeffs {
            let entry = coeff_map.entry(var).or_insert_with(Rational::zero);
            *entry = &*entry + coeff;
        }

        // Remove zeros and sort by var_id
        let mut coeffs: Vec<(u32, Rational)> = coeff_map
            .into_iter()
            .filter(|(_, c)| !c.is_zero())
            .collect();
        coeffs.sort_by_key(|(var, _)| *var);

        Self {
            coeffs,
            constant: self.constant.clone(),
        }
    }

    /// Check if two expressions have the same coefficients (ignoring constant term).
    /// Both expressions should be normalized first for reliable comparison.
    pub fn same_coefficients(&self, other: &Self) -> bool {
        if self.coeffs.len() != other.coeffs.len() {
            return false;
        }
        // Assumes both are normalized (sorted by var_id)
        for (a, b) in self.coeffs.iter().zip(&other.coeffs) {
            if a.0 != b.0 || a.1 != b.1 {
                return false;
            }
        }
        true
    }

    /// Check if `self`'s coefficients are a scalar multiple of `other`'s.
    /// Returns `Some(k)` where `self_coeff = k * other_coeff` for all variables,
    /// or `None` if no such constant ratio exists.
    /// Both expressions should be normalized first. `k` is guaranteed non-zero.
    pub fn proportional_coefficient_ratio(&self, other: &Self) -> Option<BigRational> {
        if self.coeffs.len() != other.coeffs.len() || self.coeffs.is_empty() {
            return None;
        }
        // Compute ratio from first pair; verify all others match.
        let mut ratio: Option<BigRational> = None;
        for (a, b) in self.coeffs.iter().zip(&other.coeffs) {
            if a.0 != b.0 {
                return None; // Different variables
            }
            let b_big = b.1.to_big();
            if b_big.is_zero() {
                return None; // Can't divide by zero
            }
            let r = a.1.to_big() / &b_big;
            if r.is_zero() {
                return None; // Zero ratio means self has a zero coefficient
            }
            match &ratio {
                None => ratio = Some(r),
                Some(prev) if prev != &r => return None,
                _ => {}
            }
        }
        ratio
    }
}
