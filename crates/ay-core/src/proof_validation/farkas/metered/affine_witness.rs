// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Construct, then independently replay, an explicit equality witness.
//!
//! A row-space membership answer is never a certificate. Every echelon row
//! carries exact multipliers of source POSITIONS in the unchanged conflict.
//! Publication requires a second parse of those same borrowed owner terms and
//! the actual signed combination for every explicit branch. No search limit or
//! acceptance rule of either strict verifier is changed here.

use std::mem::size_of;

use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::linear::{parse_linear_expr, MeteredLinearExpr};
use super::{bit_limb_work, FarkasValidationError, ProgressMeter};
use crate::{FarkasAnnotation, Sort, Symbol, TermData, TermId, TermStore, TheoryLit};

#[derive(Clone, Copy, PartialEq, Eq)]
enum RowKind {
    Equality,
    Disequality,
}

struct TrackedRow {
    expression: MeteredLinearExpr,
    // expression == sum combination[i] * original_equality_row[i]. For a
    // reduced target, expression == original_target + that same sum.
    combination: Vec<BigRational>,
}

struct Pivot {
    variable: TermId,
    row: TrackedRow,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Branch {
    EqualityContradiction,
    DisequalityLess { source_position: usize },
    DisequalityGreater { source_position: usize },
}

struct ExplicitBranch {
    kind: Branch,
    coefficients: Vec<Rational64>,
}

// Not an authority token: private, immutable-owner-borrowed candidate data.
// Its annotation cannot leave this module before independent paid replay.
struct AffineWitness<'a> {
    terms: &'a TermStore,
    conflict: &'a [TheoryLit],
    annotation: FarkasAnnotation,
    branches: Vec<ExplicitBranch>,
}

/// Derive exact coefficients from the current conflict's own arithmetic
/// equalities, then independently replay the explicit signed branch identities.
/// Nonparticipating causes retain their original positions with zero weights.
/// Unsupported shape, a nonzero residual or Rational64 conversion loss returns
/// no annotation; all parsing, elimination, allocation and replay uses the SAME
/// caller callback, with no private allowance, refund, solver or span oracle.
///
/// This is a constructive producer, not a broader interpretation of an input
/// hint. In particular, no supplied all-ones vector is made authoritative.
pub fn derive_affine_equality_farkas_with_progress(
    terms: &TermStore,
    conflict: &[TheoryLit],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<FarkasAnnotation>, FarkasValidationError> {
    let mut meter = ProgressMeter::new(progress);
    meter.charge(0, 0)?;
    for literal in conflict {
        meter.charge(1, 0)?;
        if literal.term.index() >= terms.len() {
            return Err(FarkasValidationError::NonArithmeticLiteral { term: literal.term });
        }
    }
    let Some(witness) = construct(terms, conflict, &mut meter)? else {
        return Ok(None);
    };
    if !replay(&witness, &mut meter)? {
        return Ok(None);
    }
    meter.charge(0, 0)?;
    Ok(Some(witness.annotation))
}

fn row(
    terms: &TermStore,
    literal: &TheoryLit,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<(RowKind, MeteredLinearExpr)>, FarkasValidationError> {
    let mut term = literal.term;
    let mut value = literal.value;
    loop {
        meter.charge(1, 0)?;
        if term.index() >= terms.len() {
            return Err(FarkasValidationError::NonArithmeticLiteral { term });
        }
        if let TermData::Not(inner) = terms.get(term) {
            term = *inner;
            value = !value;
        } else {
            break;
        }
    }
    let TermData::App(Symbol::Named(name), arguments) = terms.get(term) else {
        return Ok(None);
    };
    if !matches!(name.as_str(), "=" | "distinct") {
        return Ok(None);
    }
    let &[left, right] = arguments.as_slice() else {
        return Ok(None);
    };
    meter.charge(2, 0)?;
    for operand in [left, right] {
        if operand.index() >= terms.len() {
            return Err(FarkasValidationError::NonArithmeticLiteral { term: operand });
        }
        if !matches!(terms.sort(operand), Sort::Int | Sort::Real) {
            return Ok(None);
        }
    }
    let kind = if (name == "=" && value) || (name == "distinct" && !value) {
        RowKind::Equality
    } else {
        RowKind::Disequality
    };
    let mut expression = parse_linear_expr(terms, left, meter)?;
    let rhs = parse_linear_expr(terms, right, meter)?;
    let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
    expression.add_scaled(&rhs, &minus_one, meter)?;
    meter.charge_rational_drop(&minus_one)?;
    Ok(Some((kind, expression)))
}

fn combination(
    width: usize,
    unit: Option<usize>,
    meter: &mut ProgressMeter<'_>,
) -> Result<Vec<BigRational>, FarkasValidationError> {
    let mut result = Vec::new();
    meter.reserve_vec(&mut result, width)?;
    for index in 0..width {
        let coefficient =
            meter.rational_from_i64_pair(&Rational64::from_integer(if unit == Some(index) {
                1
            } else {
                0
            }))?;
        meter.charge(2, 0)?;
        result.push(coefficient);
    }
    Ok(result)
}

fn combine(
    target: &mut [BigRational],
    source: &[BigRational],
    scale: &BigRational,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    meter.charge(1, 0)?;
    if target.len() != source.len() {
        return Err(FarkasValidationError::ResourceLimit);
    }
    for (old, coefficient) in target.iter_mut().zip(source) {
        let product = meter.multiply(scale, coefficient)?;
        let sum = meter.add(old, &product)?;
        meter.charge_rational_drop(old)?;
        meter.charge_rational_drop(&product)?;
        meter.charge_rational_drop(&sum)?;
        *old = sum;
    }
    Ok(())
}

fn eliminate(
    target: &mut TrackedRow,
    pivot: &Pivot,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    let Some(coefficient) = target.expression.coefficient_clone(pivot.variable, meter)? else {
        return Ok(());
    };
    let leading = pivot
        .row
        .expression
        .leading_coefficient(meter)?
        .ok_or(FarkasValidationError::ResourceLimit)?;
    meter.charge(1, 0)?;
    if leading.is_zero() {
        return Err(FarkasValidationError::ResourceLimit);
    }
    let negative = meter.negate(&coefficient)?;
    let factor = meter.divide(&negative, leading)?;
    target
        .expression
        .add_scaled(&pivot.row.expression, &factor, meter)?;
    combine(
        &mut target.combination,
        &pivot.row.combination,
        &factor,
        meter,
    )?;
    meter.charge_rational_drop(&coefficient)?;
    meter.charge_rational_drop(&negative)?;
    meter.charge_rational_drop(&factor)
}

fn construct<'a>(
    terms: &'a TermStore,
    conflict: &'a [TheoryLit],
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<AffineWitness<'a>>, FarkasValidationError> {
    meter.charge(
        1,
        size_of::<AffineWitness<'_>>() + 3 * size_of::<Vec<Pivot>>() + size_of::<TrackedRow>(),
    )?;
    let mut pivots: Vec<Pivot> = Vec::new();
    let mut targets = Vec::new();
    for (index, literal) in conflict.iter().enumerate() {
        let Some((kind, expression)) = row(terms, literal, meter)? else {
            continue;
        };
        if kind == RowKind::Disequality {
            meter.reserve_vec(&mut targets, 1)?;
            meter.charge(2, 0)?;
            targets.push((index, expression));
            continue;
        }
        let mut tracked = TrackedRow {
            expression,
            combination: combination(conflict.len(), Some(index), meter)?,
        };
        for pivot in &pivots {
            eliminate(&mut tracked, pivot, meter)?;
        }
        match tracked.expression.leading_variable(meter)? {
            Some(variable) => {
                meter.reserve_vec(&mut pivots, 1)?;
                meter.charge(2, 0)?;
                pivots.push(Pivot {
                    variable,
                    row: tracked,
                });
            }
            None if !tracked.expression.constant.is_zero() => {
                // Equality rows alone imply c=0 with c!=0. Pick the explicit
                // global sign so the published combination has positive c.
                let negate = tracked.expression.constant.is_negative();
                return package(terms, conflict, &tracked.combination, negate, None, meter);
            }
            None => {}
        }
    }
    for (index, expression) in targets {
        let mut target = TrackedRow {
            expression,
            combination: combination(conflict.len(), None, meter)?,
        };
        for pivot in &pivots {
            eliminate(&mut target, pivot, meter)?;
        }
        meter.charge(target.expression.coeffs.len().max(1), 0)?;
        if target.expression.coeffs.is_empty() && target.expression.constant.is_zero() {
            // 0 = D + sum c_i E_i, hence D = sum (-c_i) E_i.
            return package(
                terms,
                conflict,
                &target.combination,
                true,
                Some(index),
                meter,
            );
        }
    }
    Ok(None)
}

fn ratio(
    value: &BigRational,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<Rational64>, FarkasValidationError> {
    let bits = value
        .numer()
        .bits()
        .checked_add(value.denom().bits())
        .ok_or(FarkasValidationError::ResourceLimit)?;
    meter.charge(bit_limb_work(bits), 0)?;
    let (Some(numerator), Some(denominator)) = (value.numer().to_i64(), value.denom().to_i64())
    else {
        return Ok(None);
    };
    // Both explicit equality orientations must be representable. Never
    // truncate, take an unchecked absolute value, or silently rescale a row.
    if numerator.checked_neg().is_none() || denominator <= 0 {
        return Ok(None);
    }
    meter.charge(128, 4 * size_of::<Rational64>())?;
    Ok(Some(Rational64::new(numerator, denominator)))
}

fn negate_ratio(
    value: Rational64,
    meter: &mut ProgressMeter<'_>,
) -> Result<Rational64, FarkasValidationError> {
    meter.charge(128, 4 * size_of::<Rational64>())?;
    let numerator = value
        .numer()
        .checked_neg()
        .ok_or(FarkasValidationError::ResourceLimit)?;
    Ok(Rational64::new(numerator, *value.denom()))
}

fn package<'a>(
    terms: &'a TermStore,
    conflict: &'a [TheoryLit],
    combination: &[BigRational],
    negate: bool,
    disequality: Option<usize>,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<AffineWitness<'a>>, FarkasValidationError> {
    if combination.len() != conflict.len() {
        return Ok(None);
    }
    let mut coefficients = Vec::new();
    meter.reserve_vec(&mut coefficients, conflict.len())?;
    for (index, coefficient) in combination.iter().enumerate() {
        let value = if Some(index) == disequality {
            if !coefficient.is_zero() {
                return Ok(None);
            }
            Rational64::one()
        } else {
            let converted = if negate {
                let signed = meter.negate(coefficient)?;
                let converted = ratio(&signed, meter)?;
                meter.charge_rational_drop(&signed)?;
                converted
            } else {
                ratio(coefficient, meter)?
            };
            let Some(value) = converted else {
                return Ok(None);
            };
            value
        };
        meter.charge(2, 0)?;
        coefficients.push(value);
    }
    let mut branches = Vec::new();
    let count = if disequality.is_some() { 2 } else { 1 };
    meter.reserve_vec(&mut branches, count)?;
    for branch in 0..count {
        let mut explicit = Vec::new();
        meter.reserve_vec(&mut explicit, conflict.len())?;
        for (index, &coefficient) in coefficients.iter().enumerate() {
            let value = if disequality.is_some() && Some(index) != disequality && branch == 0 {
                negate_ratio(coefficient, meter)?
            } else {
                coefficient
            };
            meter.charge(2, 0)?;
            explicit.push(value);
        }
        let kind = match (disequality, branch) {
            (None, _) => Branch::EqualityContradiction,
            (Some(source_position), 0) => Branch::DisequalityLess { source_position },
            (Some(source_position), _) => Branch::DisequalityGreater { source_position },
        };
        meter.charge(2, 0)?;
        branches.push(ExplicitBranch {
            kind,
            coefficients: explicit,
        });
    }
    Ok(Some(AffineWitness {
        terms,
        conflict,
        annotation: FarkasAnnotation::new(coefficients),
        branches,
    }))
}

fn replay(
    witness: &AffineWitness<'_>,
    meter: &mut ProgressMeter<'_>,
) -> Result<bool, FarkasValidationError> {
    meter.charge(0, 0)?;
    let width = witness.conflict.len();
    if witness.annotation.coefficients.len() != width {
        return Ok(false);
    }
    let disequality = match witness.branches.as_slice() {
        [ExplicitBranch {
            kind: Branch::EqualityContradiction,
            ..
        }] => None,
        [ExplicitBranch {
            kind: Branch::DisequalityLess { source_position: a },
            ..
        }, ExplicitBranch {
            kind: Branch::DisequalityGreater { source_position: b },
            ..
        }] if a == b && *a < width => Some(*a),
        _ => return Ok(false),
    };
    if let Some(index) = disequality {
        meter.charge(1, 0)?;
        let coefficient = &witness.annotation.coefficients[index];
        if *coefficient.numer() != 1 || *coefficient.denom() != 1 {
            return Ok(false);
        }
    }
    for (branch_index, branch) in witness.branches.iter().enumerate() {
        if branch.coefficients.len() != width {
            return Ok(false);
        }
        let mut sum = MeteredLinearExpr::zero(meter)?;
        for (index, (literal, &coefficient)) in witness
            .conflict
            .iter()
            .zip(&branch.coefficients)
            .enumerate()
        {
            meter.charge(128, 0)?;
            let annotation = witness.annotation.coefficients[index];
            if *annotation.denom() <= 0 || *coefficient.denom() <= 0 {
                return Ok(false);
            }
            let expected =
                if disequality.is_some() && Some(index) != disequality && branch_index == 0 {
                    negate_ratio(annotation, meter)?
                } else {
                    annotation
                };
            if coefficient.numer() != expected.numer() || coefficient.denom() != expected.denom() {
                return Ok(false);
            }
            if coefficient.is_zero() {
                continue;
            }
            let Some((kind, expression)) = row(witness.terms, literal, meter)? else {
                return Ok(false);
            };
            let multiplier = match kind {
                RowKind::Equality if Some(index) != disequality => {
                    meter.rational_from_i64_pair(&coefficient)?
                }
                RowKind::Disequality
                    if Some(index) == disequality
                        && *coefficient.numer() == 1
                        && *coefficient.denom() == 1 =>
                {
                    meter.rational_from_i64_pair(&Rational64::from_integer(
                        if branch_index == 0 { 1 } else { -1 },
                    ))?
                }
                _ => return Ok(false),
            };
            sum.add_scaled(&expression, &multiplier, meter)?;
            meter.charge_rational_drop(&multiplier)?;
        }
        meter.charge(sum.coeffs.len().max(1), 0)?;
        if !sum.coeffs.is_empty() {
            return Ok(false);
        }
        if disequality.is_some() {
            // Explicit D + sum(-mu_i)E_i = 0 AND -D + sum(mu_i)E_i = 0.
            // Each branch contains a strict disequality side, yielding 0<0.
            if !sum.constant.is_zero() {
                return Ok(false);
            }
        } else if !sum.constant.is_positive() {
            return Ok(false);
        }
    }
    meter.charge(0, 0)?;
    Ok(true)
}

#[cfg(test)]
#[path = "affine_witness_tests.rs"]
mod tests;
