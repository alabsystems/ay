// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The exact model of an MPS file, and the MIPLIB solution checker's test of
//! a point against it.
//!
//! [`crate::parse_mps_exact`] keeps every number of the file as the rational
//! it denotes. Every route of `ay lp solve` for MPS input takes its model from
//! that one reading: the engines get it (or, for a floating-point lane, a
//! rounded copy whose verdicts are confirmed on this model before they are
//! printed), and a point is printed only after [`ExactProblem::check_point`]
//! and [`ExactProblem::check_written`] accepted it here.
//!
//! # The referee's test
//!
//! The organizers' checker (`miplib2017-checker`, `Model::check`) reads the
//! model and the solution exactly and accepts a point when
//!
//! - every integer column holds a value within the integrality tolerance of
//!   an integer;
//! - every column bound holds within `tol * max(1, |bound|, |value|)`;
//! - every row side holds within `tol * max(1, positive activity, |side|)`;
//! - the written objective is within `tol * max(1, positive part, |written|)`
//!   of `offset + sum c_j x_j`.
//!
//! A side the file leaves open is `1e20` there (`INFBOUND`, the default upper
//! bound of a column, the upper side of a `G` row, the lower side of an `L`
//! row, what `MI`, `PL` and `FR` set). [`ExactProblem::check_point`] applies
//! the same test with the caller's tolerance: `0` demands exact feasibility;
//! [`WRITE_TOLERANCE`] (a thousandth of the competition's `1e-6`) is what a
//! written point must pass. Integer columns must always hold exact integers.

pub mod decimal;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::model::{Constraint, Problem, RowKind, Sense, VarKind, Variable};

/// The tolerance a written point must pass on [`ExactProblem::check_written`]:
/// `1e-9`, a thousandth of the `1e-6` the competitions give the checker.
#[must_use]
pub fn write_tolerance() -> BigRational {
    BigRational::new(BigInt::one(), BigInt::from(1_000_000_000u32))
}

/// The value the checker gives a side the file leaves open: `1e20`.
#[must_use]
pub fn referee_infinity() -> BigRational {
    BigRational::from_integer(BigInt::from(10u8).pow(20))
}

/// One column of an [`ExactProblem`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactColumn {
    /// The column's name in the file.
    pub name: String,
    /// The checker's type of the column (`Binary` for a marker column at its
    /// `[0, 1]` default or after `BV`).
    pub kind: VarKind,
    /// Lower bound; `None` is open (`-1e20` for the checker).
    pub lower: Option<BigRational>,
    /// Upper bound; `None` is open (`1e20` for the checker).
    pub upper: Option<BigRational>,
    /// Objective coefficient.
    pub objective: BigRational,
}

impl ExactColumn {
    /// Whether the column must hold an integer.
    #[must_use]
    pub fn is_integral(&self) -> bool {
        matches!(self.kind, VarKind::Integer | VarKind::Binary)
    }
}

/// One constraint row of an [`ExactProblem`]: `lower <= sum coeffs <= upper`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactRow {
    /// The row's name in the file.
    pub name: String,
    /// `(column index, coefficient)`, one entry per column, no zeros.
    pub coeffs: Vec<(usize, BigRational)>,
    /// Lower side; `None` is open (`-1e20` for the checker).
    pub lower: Option<BigRational>,
    /// Upper side; `None` is open (`1e20` for the checker).
    pub upper: Option<BigRational>,
}

/// A MIP read exactly: every number is the rational the file wrote.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExactProblem {
    /// The `NAME` field.
    pub name: String,
    /// Objective direction.
    pub sense: Sense,
    /// Objective constant (the negated right-hand side of the objective row).
    pub offset: BigRational,
    /// Columns in file order.
    pub columns: Vec<ExactColumn>,
    /// Constraint rows in file order (free `N` rows are not rows).
    pub rows: Vec<ExactRow>,
}

impl ExactProblem {
    /// A floating-point copy for engines that work in `f64`: each number is
    /// rounded to the nearest `f64`; a row with two sides becomes a `>=` row
    /// and a `<=` row named `<name>_rng`. A verdict about this copy is not a
    /// verdict about the file.
    #[must_use]
    pub fn to_problem(&self) -> Problem {
        let float = |v: &BigRational| num_traits::ToPrimitive::to_f64(v).unwrap_or(f64::NAN);
        let variables = self
            .columns
            .iter()
            .map(|c| Variable {
                name: c.name.clone(),
                obj_coeff: float(&c.objective),
                lower: c.lower.as_ref().map_or(f64::NEG_INFINITY, float),
                upper: c.upper.as_ref().map_or(f64::INFINITY, float),
                kind: c.kind,
            })
            .collect();
        let mut constraints = Vec::with_capacity(self.rows.len());
        let mut companions = Vec::new();
        for row in &self.rows {
            let coeffs: Vec<(usize, f64)> =
                row.coeffs.iter().map(|(j, a)| (*j, float(a))).collect();
            let row_of =
                |kind, rhs: &BigRational, name: String, coeffs: Vec<(usize, f64)>| Constraint {
                    name,
                    kind,
                    coeffs,
                    rhs: float(rhs),
                };
            match (&row.lower, &row.upper) {
                (Some(lo), Some(hi)) if lo == hi => {
                    constraints.push(row_of(RowKind::Eq, lo, row.name.clone(), coeffs));
                }
                (Some(lo), Some(hi)) => {
                    constraints.push(row_of(RowKind::Ge, lo, row.name.clone(), coeffs.clone()));
                    companions.push(row_of(RowKind::Le, hi, format!("{}_rng", row.name), coeffs));
                }
                (Some(lo), None) => {
                    constraints.push(row_of(RowKind::Ge, lo, row.name.clone(), coeffs))
                }
                (None, Some(hi)) => {
                    constraints.push(row_of(RowKind::Le, hi, row.name.clone(), coeffs))
                }
                (None, None) => {}
            }
        }
        constraints.extend(companions);
        Problem {
            name: self.name.clone(),
            sense: self.sense,
            obj_constant: float(&self.offset),
            variables,
            constraints,
        }
    }

    /// `offset + sum c_j x_j`, or `None` for a point of the wrong length.
    #[must_use]
    pub fn objective_at(&self, values: &[BigRational]) -> Option<BigRational> {
        if values.len() != self.columns.len() {
            return None;
        }
        let mut objective = self.offset.clone();
        for (column, value) in self.columns.iter().zip(values) {
            if !column.objective.is_zero() {
                objective += &column.objective * value;
            }
        }
        Some(objective)
    }

    /// Checks `values` (one per column) with the checker's test at
    /// `tolerance` (module docs) and returns its objective value.
    ///
    /// # Errors
    ///
    /// A message naming the first column or row that fails.
    pub fn check_point(
        &self,
        values: &[BigRational],
        tolerance: &BigRational,
    ) -> Result<BigRational, String> {
        if values.len() != self.columns.len() {
            return Err(format!(
                "{} values for {} columns",
                values.len(),
                self.columns.len()
            ));
        }
        let infinity = referee_infinity();
        let one = BigRational::one();
        for (column, value) in self.columns.iter().zip(values) {
            if column.is_integral() && !value.is_integer() {
                return Err(format!("integer column '{}' = {value}", column.name));
            }
            let lower = column.lower.clone().unwrap_or_else(|| -infinity.clone());
            let upper = column.upper.clone().unwrap_or_else(|| infinity.clone());
            let scale_lo = max3(&one, &lower.abs(), &value.abs());
            let scale_hi = max3(&one, &upper.abs(), &value.abs());
            if *value < lower - tolerance * scale_lo || *value > upper + tolerance * scale_hi {
                return Err(format!(
                    "column '{}' = {value} is outside [{}, {}]",
                    column.name,
                    side_text(column.lower.as_ref(), "-inf"),
                    side_text(column.upper.as_ref(), "+inf")
                ));
            }
        }
        for row in &self.rows {
            let (positive, negative) = split_activity(&row.coeffs, values)?;
            let activity = &positive + &negative;
            let lower = row.lower.clone().unwrap_or_else(|| -infinity.clone());
            let upper = row.upper.clone().unwrap_or_else(|| infinity.clone());
            let scale_lo = max3(&one, &positive, &lower.abs());
            let scale_hi = max3(&one, &positive, &upper.abs());
            if activity < lower - tolerance * scale_lo || activity > upper + tolerance * scale_hi {
                return Err(format!(
                    "row '{}' activity {activity} is outside [{}, {}]",
                    row.name,
                    side_text(row.lower.as_ref(), "-inf"),
                    side_text(row.upper.as_ref(), "+inf")
                ));
            }
        }
        self.objective_at(values)
            .ok_or_else(|| "point has the wrong length".to_string())
    }

    /// Checks a point as it is written: `objective` (the `o` line) and
    /// `values` (one text per column) are read back with
    /// [`decimal::parse_decimal`] and must pass the checker's test at
    /// [`write_tolerance`], the objective test included.
    ///
    /// # Errors
    ///
    /// A message naming what fails.
    pub fn check_written(&self, objective: &str, values: &[String]) -> Result<(), String> {
        let tolerance = write_tolerance();
        let mut point = Vec::with_capacity(values.len());
        for text in values.iter().chain(std::iter::once(&objective.to_string())) {
            if text.len() > decimal::MAX_CHECKER_NUMBER_LEN {
                return Err(format!("'{text}' is longer than the checker reads"));
            }
        }
        for (column, text) in self.columns.iter().zip(values) {
            let value = decimal::parse_decimal(text)
                .ok_or_else(|| format!("'{text}' (column '{}') is not a number", column.name))?;
            point.push(value);
        }
        let written = decimal::parse_decimal(objective)
            .ok_or_else(|| format!("objective '{objective}' is not a number"))?;
        let attained = self.check_point(&point, &tolerance)?;
        let mut positive = BigRational::zero();
        let mut negative = BigRational::zero();
        for (column, value) in self.columns.iter().zip(&point) {
            let term = &column.objective * value;
            if term.is_positive() {
                positive += term;
            } else {
                negative += term;
            }
        }
        let scale = max3(&BigRational::one(), &positive, &written.abs());
        if (attained.clone() - &written).abs() > tolerance * scale {
            return Err(format!(
                "written objective {objective} differs from the point's {attained}"
            ));
        }
        Ok(())
    }

    /// An exact reason the model has no point at all, when one is visible
    /// without search: a column whose bounds (rounded inward to integers for
    /// an integer column) are empty, or a row without coefficients whose
    /// sides exclude 0.
    #[must_use]
    pub fn empty_domain(&self) -> Option<String> {
        for column in &self.columns {
            let (lower, upper) = if column.is_integral() {
                (
                    column.lower.as_ref().map(BigRational::ceil),
                    column.upper.as_ref().map(BigRational::floor),
                )
            } else {
                (column.lower.clone(), column.upper.clone())
            };
            if let (Some(lo), Some(hi)) = (&lower, &upper) {
                if lo > hi {
                    let what = if column.is_integral() {
                        "holds no integer"
                    } else {
                        "is empty"
                    };
                    return Some(format!(
                        "column '{}' {what}: bounds [{}, {}]",
                        column.name,
                        side_text(column.lower.as_ref(), "-inf"),
                        side_text(column.upper.as_ref(), "+inf")
                    ));
                }
            }
        }
        for row in &self.rows {
            if !row.coeffs.is_empty() {
                continue;
            }
            let zero = BigRational::zero();
            if row.lower.as_ref().is_some_and(|lo| *lo > zero)
                || row.upper.as_ref().is_some_and(|hi| *hi < zero)
            {
                return Some(format!(
                    "row '{}' has no coefficients and its sides [{}, {}] exclude 0",
                    row.name,
                    side_text(row.lower.as_ref(), "-inf"),
                    side_text(row.upper.as_ref(), "+inf")
                ));
            }
        }
        None
    }
}

/// Positive and negative parts of a row's activity at `values`.
fn split_activity(
    coeffs: &[(usize, BigRational)],
    values: &[BigRational],
) -> Result<(BigRational, BigRational), String> {
    let mut positive = BigRational::zero();
    let mut negative = BigRational::zero();
    for (column, coefficient) in coeffs {
        let value = values
            .get(*column)
            .ok_or_else(|| format!("row names column {column} of {}", values.len()))?;
        let term = coefficient * value;
        if term.is_positive() {
            positive += term;
        } else {
            negative += term;
        }
    }
    Ok((positive, negative))
}

fn max3(a: &BigRational, b: &BigRational, c: &BigRational) -> BigRational {
    a.max(b).max(c).clone()
}

fn side_text(side: Option<&BigRational>, open: &str) -> String {
    side.map_or_else(|| open.to_string(), ToString::to_string)
}

#[cfg(test)]
mod tests;
