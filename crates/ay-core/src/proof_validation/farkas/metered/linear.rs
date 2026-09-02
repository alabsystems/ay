// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact linear-expression operations used by the progress-metered Farkas path.

use num_rational::{BigRational, Rational64};
use num_traits::{One, Zero};

use super::{FarkasValidationError, ProgressMeter};
use crate::{Constant, Sort, Symbol, TermData, TermId, TermStore};

pub(super) struct MeteredLinearExpr {
    pub(super) coeffs: Vec<(TermId, BigRational)>,
    pub(super) constant: BigRational,
}

impl MeteredLinearExpr {
    pub(super) fn zero(meter: &mut ProgressMeter<'_>) -> Result<Self, FarkasValidationError> {
        Ok(Self {
            coeffs: Vec::new(),
            constant: meter.rational_from_i64_pair(&Rational64::zero())?,
        })
    }

    fn constant(value: BigRational) -> Self {
        Self {
            coeffs: Vec::new(),
            constant: value,
        }
    }

    fn variable(
        term: TermId,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Self, FarkasValidationError> {
        let coefficient = meter.rational_from_i64_pair(&Rational64::one())?;
        let constant = meter.rational_from_i64_pair(&Rational64::zero())?;
        let mut coeffs = Vec::new();
        meter.reserve_vec(&mut coeffs, 1)?;
        meter.charge(1, 0)?;
        coeffs.push((term, coefficient));
        Ok(Self { coeffs, constant })
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub(super) fn negate(
        &mut self,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<(), FarkasValidationError> {
        let constant = meter.negate(&self.constant)?;
        meter.charge_rational_drop(&self.constant)?;
        self.constant = constant;
        for (_, coefficient) in &mut self.coeffs {
            let negated = meter.negate(coefficient)?;
            meter.charge_rational_drop(coefficient)?;
            *coefficient = negated;
        }
        Ok(())
    }

    fn scale(
        &mut self,
        scale: &BigRational,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<(), FarkasValidationError> {
        if scale.is_zero() {
            meter.charge(self.coeffs.len(), 0)?;
            for (_, coefficient) in &self.coeffs {
                meter.charge_rational_drop(coefficient)?;
            }
            meter.charge_rational_drop(&self.constant)?;
            let zero = meter.rational_from_i64_pair(&Rational64::zero())?;
            self.coeffs.clear();
            self.constant = zero;
            return Ok(());
        }
        if scale.is_one() {
            return Ok(());
        }
        let constant = meter.multiply(&self.constant, scale)?;
        meter.charge_rational_drop(&self.constant)?;
        self.constant = constant;
        for (_, coefficient) in &mut self.coeffs {
            let scaled = meter.multiply(coefficient, scale)?;
            meter.charge_rational_drop(coefficient)?;
            *coefficient = scaled;
        }
        Ok(())
    }

    pub(super) fn add_scaled(
        &mut self,
        other: &Self,
        scale: &BigRational,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<(), FarkasValidationError> {
        if scale.is_zero() {
            return Ok(());
        }
        let scaled_constant = meter.multiply(scale, &other.constant)?;
        let constant = meter.add(&self.constant, &scaled_constant)?;
        meter.charge_rational_drop(&self.constant)?;
        meter.charge_rational_drop(&scaled_constant)?;
        self.constant = constant;
        for (variable, coefficient) in &other.coeffs {
            let scaled = meter.multiply(scale, coefficient)?;
            let entries = self.coeffs.len();
            meter.charge(sorted_search_work(entries), 0)?;
            match self
                .coeffs
                .binary_search_by_key(variable, |(term, _)| *term)
            {
                Ok(index) => {
                    let Some(entry) = self.coeffs.get(index) else {
                        return Err(FarkasValidationError::ResourceLimit);
                    };
                    let updated = meter.add(&entry.1, &scaled)?;
                    meter.charge_rational_drop(&entry.1)?;
                    meter.charge_rational_drop(&scaled)?;
                    if updated.is_zero() {
                        let after = index
                            .checked_add(1)
                            .ok_or(FarkasValidationError::ResourceLimit)?;
                        let moves = entries
                            .checked_sub(after)
                            .and_then(|moves| moves.checked_add(1))
                            .ok_or(FarkasValidationError::ResourceLimit)?;
                        meter.charge(moves, 0)?;
                        meter.charge_rational_drop(&updated)?;
                        if index >= self.coeffs.len() {
                            return Err(FarkasValidationError::ResourceLimit);
                        }
                        drop(self.coeffs.remove(index));
                    } else {
                        meter.charge(1, 0)?;
                        let Some(entry) = self.coeffs.get_mut(index) else {
                            return Err(FarkasValidationError::ResourceLimit);
                        };
                        entry.1 = updated;
                    }
                }
                Err(index) => {
                    meter.reserve_vec(&mut self.coeffs, 1)?;
                    let moves = entries
                        .checked_sub(index)
                        .and_then(|moves| moves.checked_add(1))
                        .ok_or(FarkasValidationError::ResourceLimit)?;
                    meter.charge(moves, 0)?;
                    if index > self.coeffs.len() {
                        return Err(FarkasValidationError::ResourceLimit);
                    }
                    self.coeffs.insert(index, (*variable, scaled));
                }
            }
        }
        Ok(())
    }

    pub(super) fn is_integer_valued(
        &self,
        terms: &TermStore,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<bool, FarkasValidationError> {
        meter.charge(1, 0)?;
        if !self.constant.is_integer() {
            return Ok(false);
        }
        for (term, coefficient) in &self.coeffs {
            meter.charge(1, 0)?;
            if !coefficient.is_integer() || !matches!(terms.sort(*term), Sort::Int) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn leading_variable(
        &self,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Option<TermId>, FarkasValidationError> {
        meter.charge(1, 0)?;
        Ok(self.coeffs.first().map(|(term, _)| *term))
    }

    pub(super) fn coefficient_clone(
        &self,
        variable: TermId,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Option<BigRational>, FarkasValidationError> {
        meter.charge(sorted_search_work(self.coeffs.len()), 0)?;
        let Ok(index) = self
            .coeffs
            .binary_search_by_key(&variable, |(term, _)| *term)
        else {
            return Ok(None);
        };
        let Some(entry) = self.coeffs.get(index) else {
            return Ok(None);
        };
        Ok(Some(meter.clone_rational(&entry.1)?))
    }

    pub(super) fn leading_coefficient<'a>(
        &'a self,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Option<&'a BigRational>, FarkasValidationError> {
        meter.charge(1, 0)?;
        Ok(self.coeffs.first().map(|(_, coefficient)| coefficient))
    }
}

fn sorted_search_work(entries: usize) -> usize {
    if entries == 0 {
        0
    } else {
        usize::BITS as usize - entries.leading_zeros() as usize
    }
}

pub(super) fn parse_linear_expr(
    terms: &TermStore,
    term: TermId,
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    meter.charge(1, 0)?;
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Ok(MeteredLinearExpr::constant(
            meter.rational_from_bigint(value)?,
        )),
        TermData::Const(Constant::Rational(value)) => {
            Ok(MeteredLinearExpr::constant(meter.clone_rational(&value.0)?))
        }
        TermData::Var(_, _) => MeteredLinearExpr::variable(term, meter),
        TermData::App(Symbol::Named(name), args) => parse_named_app(terms, term, name, args, meter),
        _ => MeteredLinearExpr::variable(term, meter),
    }
}

fn parse_named_app(
    terms: &TermStore,
    term: TermId,
    name: &str,
    args: &[TermId],
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    match name {
        "+" => parse_sum(terms, args, meter),
        "-" if args.len() == 1 => {
            let mut result = parse_linear_expr(terms, args[0], meter)?;
            result.negate(meter)?;
            Ok(result)
        }
        "-" if args.len() >= 2 => {
            let mut result = parse_linear_expr(terms, args[0], meter)?;
            let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
            for &arg in &args[1..] {
                let sub = parse_linear_expr(terms, arg, meter)?;
                result.add_scaled(&sub, &minus_one, meter)?;
            }
            Ok(result)
        }
        "*" => parse_product(terms, term, args, meter),
        "/" if args.len() == 2 => parse_quotient(terms, term, args, meter),
        _ => MeteredLinearExpr::variable(term, meter),
    }
}

fn parse_sum(
    terms: &TermStore,
    args: &[TermId],
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    let mut result = MeteredLinearExpr::zero(meter)?;
    let one = meter.rational_from_i64_pair(&Rational64::one())?;
    for &arg in args {
        let sub = parse_linear_expr(terms, arg, meter)?;
        result.add_scaled(&sub, &one, meter)?;
    }
    Ok(result)
}

fn parse_product(
    terms: &TermStore,
    term: TermId,
    args: &[TermId],
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    let mut constant = meter.rational_from_i64_pair(&Rational64::one())?;
    let mut non_constant = None;
    for &arg in args {
        let sub = parse_linear_expr(terms, arg, meter)?;
        if sub.is_constant() {
            constant = meter.multiply(&constant, &sub.constant)?;
        } else if non_constant.is_none() {
            non_constant = Some(sub);
        } else {
            return MeteredLinearExpr::variable(term, meter);
        }
    }
    match non_constant {
        Some(mut expression) => {
            expression.scale(&constant, meter)?;
            Ok(expression)
        }
        None => Ok(MeteredLinearExpr::constant(constant)),
    }
}

fn parse_quotient(
    terms: &TermStore,
    term: TermId,
    args: &[TermId],
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    let &[numerator, denominator] = args else {
        return MeteredLinearExpr::variable(term, meter);
    };
    let mut numerator = parse_linear_expr(terms, numerator, meter)?;
    let denominator = parse_linear_expr(terms, denominator, meter)?;
    if denominator.is_constant() && !denominator.constant.is_zero() {
        let one = meter.rational_from_i64_pair(&Rational64::one())?;
        let inverse = meter.divide(&one, &denominator.constant)?;
        numerator.scale(&inverse, meter)?;
        Ok(numerator)
    } else {
        MeteredLinearExpr::variable(term, meter)
    }
}
