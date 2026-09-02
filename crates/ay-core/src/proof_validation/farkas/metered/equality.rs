// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, allocation-accounted equality-span elimination.

use num_rational::Rational64;
use num_traits::{One, Signed, Zero};

use super::classification::{metered_progress_row_kind, FarkasProgressRowKind};
use super::linear::{parse_linear_expr, MeteredLinearExpr};
use super::{FarkasValidationError, ProgressMeter};
use crate::{FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLit};

struct PivotBasis {
    /// Retained in conflict order, matching the legacy eliminator. Each nested
    /// coefficient vector is sorted, so searches and capacities are exact.
    rows: Vec<(TermId, MeteredLinearExpr)>,
}

impl PivotBasis {
    fn new() -> Self {
        Self { rows: Vec::new() }
    }

    /// Add one equality row. Returns `true` when the equalities alone imply an
    /// impossible constant equation.
    fn add_row(
        &mut self,
        mut row: MeteredLinearExpr,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<bool, FarkasValidationError> {
        for (variable, pivot) in &self.rows {
            meter.charge(1, 0)?;
            eliminate_variable(&mut row, *variable, pivot, meter)?;
        }
        let Some(variable) = row.leading_variable(meter)? else {
            meter.charge(1, 0)?;
            return Ok(!row.constant.is_zero());
        };
        for (_, pivot) in &mut self.rows {
            meter.charge(1, 0)?;
            eliminate_variable(pivot, variable, &row, meter)?;
        }

        meter.reserve_vec(&mut self.rows, 1)?;
        meter.charge(1, 0)?;
        self.rows.push((variable, row));
        Ok(false)
    }

    fn reduce(
        &self,
        expression: &mut MeteredLinearExpr,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<(), FarkasValidationError> {
        for (variable, pivot) in &self.rows {
            meter.charge(1, 0)?;
            eliminate_variable(expression, *variable, pivot, meter)?;
        }
        Ok(())
    }
}

fn eliminate_variable(
    target: &mut MeteredLinearExpr,
    variable: TermId,
    pivot: &MeteredLinearExpr,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    let Some(coefficient) = target.coefficient_clone(variable, meter)? else {
        return Ok(());
    };
    let denominator = pivot
        .leading_coefficient(meter)?
        .ok_or(FarkasValidationError::ResourceLimit)?;
    let negated = meter.negate(&coefficient)?;
    let factor = meter.divide(&negated, denominator)?;
    target.add_scaled(pivot, &factor, meter)?;
    meter.charge_rational_drop(&coefficient)?;
    meter.charge_rational_drop(&negated)?;
    meter.charge_rational_drop(&factor)
}

pub(super) fn verify_equality_span_farkas(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    disequality_count: usize,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    if disequality_count != 1 {
        return Err(FarkasValidationError::NonArithmeticLiteral {
            term: conflict.first().map_or(TermId(0), |literal| literal.term),
        });
    }
    let mut pivots = PivotBasis::new();
    let mut disequality_index = None;
    for (index, (literal, coefficient)) in conflict.iter().zip(&farkas.coefficients).enumerate() {
        meter.charge(1, 0)?;
        if coefficient.is_zero() {
            continue;
        }
        let kind = metered_progress_row_kind(terms, literal, meter)?
            .ok_or(FarkasValidationError::NonArithmeticLiteral { term: literal.term })?;
        match kind {
            FarkasProgressRowKind::PositiveEquality => {
                let expression = normalize_row(terms, literal, kind, meter)?;
                if pivots.add_row(expression, meter)? {
                    return Ok(());
                }
            }
            FarkasProgressRowKind::Disequality => disequality_index = Some(index),
            FarkasProgressRowKind::Inequality => {
                return Err(FarkasValidationError::NonArithmeticLiteral { term: literal.term });
            }
        }
    }
    let disequality_index =
        disequality_index.ok_or(FarkasValidationError::NonArithmeticLiteral {
            term: conflict.first().map_or(TermId(0), |literal| literal.term),
        })?;
    verify_branch(
        terms,
        conflict,
        farkas,
        disequality_index,
        &pivots,
        false,
        meter,
    )?;
    verify_branch(
        terms,
        conflict,
        farkas,
        disequality_index,
        &pivots,
        true,
        meter,
    )?;
    Ok(())
}

fn verify_branch(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    disequality_index: usize,
    pivots: &PivotBasis,
    reverse_disequality: bool,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    let Some(literal) = conflict.get(disequality_index) else {
        return Err(FarkasValidationError::NonArithmeticLiteral {
            term: conflict.first().map_or(TermId(0), |literal| literal.term),
        });
    };
    let Some(coefficient) = farkas.coefficients.get(disequality_index) else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term: literal.term });
    };
    let mut expression = normalize_row(terms, literal, FarkasProgressRowKind::Disequality, meter)?;
    if reverse_disequality {
        expression.negate(meter)?;
    }
    let mut base = MeteredLinearExpr::zero(meter)?;
    let coefficient = meter.rational_from_i64_pair(coefficient)?;
    base.add_scaled(&expression, &coefficient, meter)?;
    meter.charge_rational_drop(&coefficient)?;
    pivots.reduce(&mut base, meter)?;
    meter.charge(base.coeffs.len().max(1), 0)?;
    let contradiction = !base.constant.is_negative();
    if base.coeffs.is_empty() && contradiction {
        return Ok(());
    }
    diagnostic_error(
        recompute_diagnostic(terms, conflict, farkas, reverse_disequality, meter)?,
        meter,
    )
}

fn recompute_diagnostic(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    reverse_disequality: bool,
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    // Preserve the legacy branch order and first printed equality orientation.
    // The full validator first rewrites variable keys through its congruence
    // closure, so rejected affine certificates may name a different surviving
    // key/coefficient here. Acceptance is unchanged: the equality row span
    // already proves every affine substitution used by that closure.
    let mut diagnostic = MeteredLinearExpr::zero(meter)?;
    for (literal, coefficient) in conflict.iter().zip(&farkas.coefficients) {
        meter.charge(1, 0)?;
        if coefficient.is_zero() {
            continue;
        }
        let kind = metered_progress_row_kind(terms, literal, meter)?
            .ok_or(FarkasValidationError::NonArithmeticLiteral { term: literal.term })?;
        let mut expression = normalize_row(terms, literal, kind, meter)?;
        if kind == FarkasProgressRowKind::Disequality && reverse_disequality {
            expression.negate(meter)?;
        }
        let coefficient = meter.rational_from_i64_pair(coefficient)?;
        diagnostic.add_scaled(&expression, &coefficient, meter)?;
        meter.charge_rational_drop(&coefficient)?;
    }
    Ok(diagnostic)
}

fn normalize_row(
    terms: &TermStore,
    literal: &TheoryLit,
    kind: FarkasProgressRowKind,
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    if kind == FarkasProgressRowKind::Inequality {
        return Err(FarkasValidationError::NonArithmeticLiteral { term: literal.term });
    }
    let mut term = literal.term;
    loop {
        meter.charge(1, 0)?;
        let TermData::Not(inner) = terms.get(term) else {
            break;
        };
        term = *inner;
    }
    meter.charge(1, 0)?;
    let TermData::App(Symbol::Named(predicate), args) = terms.get(term) else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    let mut operands = args.iter();
    let (Some(&left), Some(&right), None) = (operands.next(), operands.next(), operands.next())
    else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    if !matches!(predicate.as_str(), "=" | "distinct") {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    }
    let mut expression = parse_linear_expr(terms, left, meter)?;
    let right = parse_linear_expr(terms, right, meter)?;
    let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
    expression.add_scaled(&right, &minus_one, meter)?;
    meter.charge_rational_drop(&minus_one)?;
    Ok(expression)
}

fn diagnostic_error(
    diagnostic: MeteredLinearExpr,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    meter.charge(diagnostic.coeffs.len().max(1), 0)?;
    if let Some((term, coefficient)) = diagnostic.coeffs.first() {
        return Err(FarkasValidationError::VariablesNotEliminated {
            term: *term,
            coefficient: meter.clone_rational(coefficient)?,
        });
    }
    Err(FarkasValidationError::NoContradiction {
        constant: meter.clone_rational(&diagnostic.constant)?,
        expected: ">= 0",
    })
}
