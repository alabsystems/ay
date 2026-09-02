// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-metered validation for bounded exact Farkas fragments.

use std::mem::size_of;

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, Zero};

use super::farkas::FarkasValidationError;
use crate::{FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLit};

#[path = "metered/classification.rs"]
mod classification;
#[path = "metered/equality.rs"]
mod equality;
#[cfg(test)]
#[path = "metered/equality_tests.rs"]
mod equality_tests;
#[path = "metered/linear.rs"]
mod linear;
#[cfg(test)]
#[path = "metered/tests.rs"]
mod tests;

use linear::{parse_linear_expr, MeteredLinearExpr};

pub use classification::{farkas_progress_row_kind, FarkasProgressRowKind};

const RATIONAL_SCRATCH_COPIES: usize = 32;
const RATIONAL_SCRATCH_HEADERS: usize =
    RATIONAL_SCRATCH_COPIES * (size_of::<BigInt>() + size_of::<BigRational>());
const BIGINT_PAIR_HEADERS: usize = 2 * size_of::<BigInt>();
const RATIONAL_CLONE_HEADERS: usize = BIGINT_PAIR_HEADERS + size_of::<BigRational>();
const I64_PAIR_RATIONAL_BYTES: usize = RATIONAL_CLONE_HEADERS + 2 * size_of::<u64>();

struct ProgressMeter<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl<'a> ProgressMeter<'a> {
    fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self { progress }
    }

    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), FarkasValidationError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(FarkasValidationError::ResourceLimit)
        }
    }

    fn reserve_vec<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> Result<(), FarkasValidationError> {
        let old_capacity = values.capacity();
        let required = values
            .len()
            .checked_add(additional)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        if required <= old_capacity {
            return self.charge(0, 0);
        }
        let requested_bytes = required
            .checked_mul(size_of::<T>())
            .ok_or(FarkasValidationError::ResourceLimit)?;
        // A reallocating allocator may retain the old buffer while creating
        // the new one. Prior calls already charged the old capacity, so debit
        // the complete requested target before allocation, not just growth.
        self.charge(values.len(), requested_bytes)?;
        values
            .try_reserve_exact(additional)
            .map_err(|_| FarkasValidationError::ResourceLimit)?;
        let excess_capacity = values
            .capacity()
            .checked_sub(required)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        let excess_bytes = excess_capacity
            .checked_mul(size_of::<T>())
            .ok_or(FarkasValidationError::ResourceLimit)?;
        self.charge(0, excess_bytes)
    }

    fn charge_rational_clone(&mut self, value: &BigRational) -> Result<(), FarkasValidationError> {
        let bits = rational_bits(value)?;
        let bytes = rational_payload_bytes(value)?
            .checked_add(RATIONAL_CLONE_HEADERS)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        self.charge(bit_limb_work(bits), bytes)
    }

    fn charge_rational_drop(&mut self, value: &BigRational) -> Result<(), FarkasValidationError> {
        self.charge(bit_limb_work(rational_bits(value)?), 0)
    }

    fn charge_binary_rational(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> Result<(), FarkasValidationError> {
        let bits = rational_bits(left)?
            .checked_add(rational_bits(right)?)
            .and_then(|sum| sum.checked_add(1))
            .ok_or(FarkasValidationError::ResourceLimit)?;
        let payload = rational_payload_bytes(left)?
            .checked_add(rational_payload_bytes(right)?)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        let bytes = payload
            .checked_mul(RATIONAL_SCRATCH_COPIES)
            .and_then(|scratch| scratch.checked_add(RATIONAL_SCRATCH_HEADERS))
            .ok_or(FarkasValidationError::ResourceLimit)?;
        self.charge(bit_limb_work(bits), bytes)
    }

    fn clone_rational(
        &mut self,
        value: &BigRational,
    ) -> Result<BigRational, FarkasValidationError> {
        self.charge_rational_clone(value)?;
        Ok(value.clone())
    }

    fn rational_from_bigint(
        &mut self,
        value: &BigInt,
    ) -> Result<BigRational, FarkasValidationError> {
        let bits = value.bits().max(1);
        let payload = bigint_payload_bytes(bits)?
            .checked_add(bigint_payload_bytes(1)?)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        let bytes = payload
            .checked_add(BIGINT_PAIR_HEADERS)
            .ok_or(FarkasValidationError::ResourceLimit)?;
        self.charge(bit_limb_work(bits), bytes)?;
        Ok(BigRational::from(value.clone()))
    }

    fn rational_from_i64_pair(
        &mut self,
        value: &Rational64,
    ) -> Result<BigRational, FarkasValidationError> {
        self.charge(1, I64_PAIR_RATIONAL_BYTES)?;
        Ok(BigRational::new(
            BigInt::from(*value.numer()),
            BigInt::from(*value.denom()),
        ))
    }

    fn add(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> Result<BigRational, FarkasValidationError> {
        self.charge_binary_rational(left, right)?;
        Ok(left + right)
    }

    fn multiply(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> Result<BigRational, FarkasValidationError> {
        self.charge_binary_rational(left, right)?;
        Ok(left * right)
    }

    fn divide(
        &mut self,
        left: &BigRational,
        right: &BigRational,
    ) -> Result<BigRational, FarkasValidationError> {
        self.charge_binary_rational(left, right)?;
        Ok(left / right)
    }

    fn negate(&mut self, value: &BigRational) -> Result<BigRational, FarkasValidationError> {
        self.charge_rational_clone(value)?;
        Ok(-value.clone())
    }
}

fn rational_bits(value: &BigRational) -> Result<u64, FarkasValidationError> {
    value
        .numer()
        .bits()
        .checked_add(value.denom().bits())
        .ok_or(FarkasValidationError::ResourceLimit)
}

fn rational_payload_bytes(value: &BigRational) -> Result<usize, FarkasValidationError> {
    bigint_payload_bytes(value.numer().bits())?
        .checked_add(bigint_payload_bytes(value.denom().bits())?)
        .ok_or(FarkasValidationError::ResourceLimit)
}

fn bigint_payload_bytes(bits: u64) -> Result<usize, FarkasValidationError> {
    usize::try_from(bits.max(1).div_ceil(u32::BITS as u64))
        .ok()
        .and_then(|limbs| limbs.checked_mul(size_of::<u64>()))
        .ok_or(FarkasValidationError::ResourceLimit)
}

fn bit_limb_work(bits: u64) -> usize {
    usize::try_from(bits.div_ceil(usize::BITS as u64))
        .unwrap_or(usize::MAX)
        .max(1)
}

/// Whether one Farkas row has exactly one arithmetic orientation.
#[must_use]
pub fn farkas_conflict_literal_is_single_inequality(
    terms: &TermStore,
    literal: &TheoryLit,
) -> bool {
    let mut term = literal.term;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
    }
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=")
    )
}

fn normalize_inequality(
    terms: &TermStore,
    literal: &TheoryLit,
    meter: &mut ProgressMeter<'_>,
) -> Result<(MeteredLinearExpr, bool), FarkasValidationError> {
    let mut term = literal.term;
    let mut value = literal.value;
    while let TermData::Not(inner) = terms.get(term) {
        meter.charge(1, 0)?;
        term = *inner;
        value = !value;
    }
    meter.charge(1, 0)?;
    let TermData::App(Symbol::Named(predicate), args) = terms.get(term) else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    let mut operands = args.iter();
    let (Some(&first), Some(&second), None) = (operands.next(), operands.next(), operands.next())
    else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    if !matches!(predicate.as_str(), "<" | "<=" | ">" | ">=") {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    }
    let reverse = matches!(predicate.as_str(), ">" | ">=");
    let (left, right) = if reverse {
        (second, first)
    } else {
        (first, second)
    };
    let mut expression = parse_linear_expr(terms, left, meter)?;
    let right = parse_linear_expr(terms, right, meter)?;
    let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
    expression.add_scaled(&right, &minus_one, meter)?;
    let base_strict = matches!(predicate.as_str(), "<" | ">");
    if !value {
        expression.negate(meter)?;
    }
    let mut strict = if value { base_strict } else { !base_strict };
    if strict && expression.is_integer_valued(terms, meter)? {
        let one = meter.rational_from_i64_pair(&Rational64::one())?;
        expression.constant = meter.add(&expression.constant, &one)?;
        strict = false;
    }
    Ok((expression, strict))
}

fn verify_coefficient_shape(
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    meter: &mut ProgressMeter<'_>,
) -> Result<(), FarkasValidationError> {
    if farkas.coefficients.len() != conflict.len() {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: farkas.coefficients.len(),
            literals: conflict.len(),
        });
    }
    meter.charge(farkas.coefficients.len(), 0)?;
    let negative_count = farkas
        .coefficients
        .iter()
        .filter(|value| **value < Rational64::zero())
        .count();
    if negative_count == 0 {
        return Ok(());
    }
    let mut negative = Vec::new();
    meter.reserve_vec(&mut negative, negative_count)?;
    let collection_work = farkas
        .coefficients
        .len()
        .checked_add(negative_count)
        .ok_or(FarkasValidationError::ResourceLimit)?;
    meter.charge(collection_work, 0)?;
    negative.extend(
        farkas
            .coefficients
            .iter()
            .enumerate()
            .filter(|(_, value)| **value < Rational64::zero())
            .map(|(index, value)| (index, *value)),
    );
    meter.charge(0, 0)?;
    Err(FarkasValidationError::NegativeCoefficients { negative })
}

/// Validate the pure-inequality Farkas fragment under a caller-owned envelope.
///
/// Every retained coefficient slot, exact-rational operation, and transient
/// rational scratch bound is charged before it is materialized. Nonzero rows
/// must be inequalities; zero-coefficient rows are semantically ignored.
/// Checker dispatch requires every row to be an inequality and retains the
/// general validator for other clauses.
pub fn verify_pure_inequality_farkas_with_progress(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), FarkasValidationError> {
    let mut meter = ProgressMeter::new(progress);
    meter.charge(0, 0)?;
    verify_coefficient_shape(conflict, farkas, &mut meter)?;
    let mut sum = MeteredLinearExpr::zero(&mut meter)?;
    let mut strict = false;
    for (literal, coefficient) in conflict.iter().zip(&farkas.coefficients) {
        meter.charge(1, 0)?;
        if coefficient.is_zero() {
            continue;
        }
        let coefficient = meter.rational_from_i64_pair(coefficient)?;
        let (expression, row_strict) = normalize_inequality(terms, literal, &mut meter)?;
        sum.add_scaled(&expression, &coefficient, &mut meter)?;
        strict |= row_strict;
    }
    meter.charge(sum.coeffs.len().max(1), 0)?;
    let contradiction = if strict {
        !sum.constant.is_negative()
    } else {
        sum.constant.is_positive()
    };
    if sum.coeffs.is_empty() && contradiction {
        return Ok(());
    }
    if let Some((term, coefficient)) = sum.coeffs.first() {
        return Err(FarkasValidationError::VariablesNotEliminated {
            term: *term,
            coefficient: meter.clone_rational(coefficient)?,
        });
    }
    Err(FarkasValidationError::NoContradiction {
        constant: meter.clone_rational(&sum.constant)?,
        expected: if strict { ">= 0" } else { "> 0" },
    })
}

/// Validate the explicit-affine equality-span fragment under a caller-owned
/// envelope. The selected fragment requires nonzero positive equality rows with
/// sign-free multipliers and exactly one weighted disequality, whose two strict
/// orientations must both contradict. Zero-weight rows must be inequalities.
/// Callers retain the full validator for every other shape.
pub fn verify_affine_equality_farkas_with_progress(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), FarkasValidationError> {
    let mut meter = ProgressMeter::new(progress);
    meter.charge(0, 0)?;
    let disequality_count = verify_affine_fragment_shape(terms, conflict, farkas, &mut meter)?;
    equality::verify_equality_span_farkas(terms, conflict, farkas, disequality_count, &mut meter)
}

fn verify_affine_fragment_shape(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
    meter: &mut ProgressMeter<'_>,
) -> Result<usize, FarkasValidationError> {
    if farkas.coefficients.len() != conflict.len() {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: farkas.coefficients.len(),
            literals: conflict.len(),
        });
    }
    meter.charge(farkas.coefficients.len(), 0)?;
    let mut negative = Vec::new();
    let mut first_incompatible = None;
    let mut equality_count = 0usize;
    let mut disequality_count = 0usize;
    for (index, (literal, coefficient)) in conflict.iter().zip(&farkas.coefficients).enumerate() {
        if coefficient.is_zero() {
            if !metered_literal_is_single_inequality(terms, literal, meter)?
                && first_incompatible.is_none()
            {
                first_incompatible = Some(literal.term);
            }
            continue;
        }
        let kind = classification::metered_progress_row_kind(terms, literal, meter)?;
        if *coefficient < Rational64::zero()
            && kind != Some(FarkasProgressRowKind::PositiveEquality)
        {
            meter.reserve_vec(&mut negative, 1)?;
            meter.charge(1, 0)?;
            negative.push((index, *coefficient));
        }
        let compatible = match kind {
            Some(FarkasProgressRowKind::Inequality) => false,
            Some(FarkasProgressRowKind::PositiveEquality) => {
                equality_count = equality_count
                    .checked_add(1)
                    .ok_or(FarkasValidationError::ResourceLimit)?;
                true
            }
            Some(FarkasProgressRowKind::Disequality) => {
                disequality_count = disequality_count
                    .checked_add(1)
                    .ok_or(FarkasValidationError::ResourceLimit)?;
                disequality_count <= 1
            }
            _ => false,
        };
        if !compatible && first_incompatible.is_none() {
            first_incompatible = Some(literal.term);
        }
    }
    if !negative.is_empty() {
        return Err(FarkasValidationError::NegativeCoefficients { negative });
    }
    if let Some(term) = first_incompatible {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    }
    if equality_count == 0 || disequality_count != 1 {
        return Err(FarkasValidationError::NonArithmeticLiteral {
            term: conflict.first().map_or(TermId(0), |literal| literal.term),
        });
    }
    Ok(disequality_count)
}

fn metered_literal_is_single_inequality(
    terms: &TermStore,
    literal: &TheoryLit,
    meter: &mut ProgressMeter<'_>,
) -> Result<bool, FarkasValidationError> {
    let mut term = literal.term;
    loop {
        meter.charge(1, 0)?;
        let TermData::Not(inner) = terms.get(term) else {
            break;
        };
        term = *inner;
    }
    meter.charge(1, 0)?;
    Ok(matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=")
    ))
}
