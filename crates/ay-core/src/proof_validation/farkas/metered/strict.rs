// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict positional coefficients, with every parse and arithmetic visit metered.
//! Unlike the affine-span fragment this retains the supplied magnitudes and the
//! legacy 1024-orientation / all-first-plus-one-flip decision boundary.

use num_rational::Rational64;
use num_traits::{One, Signed, Zero};

use super::{
    congruence::Congruence, linear::parse_linear_expr, FarkasValidationError, MeteredLinearExpr,
    ProgressMeter,
};
use crate::{FarkasAnnotation, Symbol, TermData, TermStore, TheoryLit};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Inequality,
    Equality,
    Disequality,
}

struct Plan {
    base: MeteredLinearExpr,
    strict: bool,
    equalities: Vec<MeteredLinearExpr>,
    disequality: Option<MeteredLinearExpr>,
}

/// Strict linear Farkas decision under the caller's work, space and stop
/// callback. `Ok(false)` is rejection; exhaustion is `ResourceLimit`. No grant
/// or span-based completeness fallback is created by this API.
pub fn farkas_conflict_lits_linear_holds_with_progress(
    terms: &TermStore,
    conflict: &[TheoryLit],
    annotation: &FarkasAnnotation,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<bool, FarkasValidationError> {
    let mut meter = ProgressMeter::new(progress);
    meter.charge(0, 0)?;
    let Some(plan) = prepare_plan(terms, conflict, annotation, &mut meter)? else {
        return Ok(false);
    };
    plan_holds(&plan, &mut meter)
}

/// Exact positional coefficients with congruence derived ONLY from the whole
/// conflict's positive equalities. Every closure, parse, arithmetic and scratch
/// operation shares the caller's meter. This is native witness metadata, not
/// permission to print `la_generic`: the LINEAR export contract stays separate.
///
/// As in the strict LINEAR path, equality orientations retain their supplied
/// magnitudes and the 1024 / all-first-plus-single-flip boundary. No affine-span
/// completion, private grant, or unmetered FULL fallback is used.
pub fn farkas_conflict_lits_full_holds_with_progress(
    terms: &TermStore,
    conflict: &[TheoryLit],
    annotation: &FarkasAnnotation,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<bool, FarkasValidationError> {
    let mut meter = ProgressMeter::new(progress);
    meter.charge(0, 0)?;
    if annotation.coefficients.len() != conflict.len() {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: annotation.coefficients.len(),
            literals: conflict.len(),
        });
    }
    let congruence = Congruence::build(terms, conflict, &mut meter)?;
    let substitution = if congruence.is_empty() {
        None
    } else {
        Some(&congruence)
    };
    let Some(plan) =
        prepare_plan_with_congruence(terms, conflict, annotation, substitution, &mut meter)?
    else {
        return Ok(false);
    };
    plan_holds(&plan, &mut meter)
}

fn plan_holds(plan: &Plan, meter: &mut ProgressMeter<'_>) -> Result<bool, FarkasValidationError> {
    let branches = if plan.disequality.is_some() { 2 } else { 1 };
    for branch in 0..branches {
        let base = branch_base(plan, branch, meter)?;
        if !orientations_hold(
            &base,
            plan.strict || plan.disequality.is_some(),
            &plan.equalities,
            meter,
        )? {
            return Ok(false);
        }
    }
    meter.charge(0, 0)?;
    Ok(true)
}

fn prepare_plan(
    terms: &TermStore,
    conflict: &[TheoryLit],
    annotation: &FarkasAnnotation,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<Plan>, FarkasValidationError> {
    prepare_plan_with_congruence(terms, conflict, annotation, None, meter)
}

fn prepare_plan_with_congruence(
    terms: &TermStore,
    conflict: &[TheoryLit],
    annotation: &FarkasAnnotation,
    congruence: Option<&Congruence>,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<Plan>, FarkasValidationError> {
    if annotation.coefficients.len() != conflict.len() {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: annotation.coefficients.len(),
            literals: conflict.len(),
        });
    }
    let mut plan = Plan {
        base: MeteredLinearExpr::zero(meter)?,
        strict: false,
        equalities: Vec::new(),
        disequality: None,
    };
    for (literal, coefficient) in conflict.iter().zip(&annotation.coefficients) {
        meter.charge(1, 0)?;
        if *coefficient.denom() <= 0 {
            return Ok(None);
        }
        if coefficient.is_zero() {
            continue;
        }
        let Some((mut expression, mode, strict)) = normalize(terms, literal, coefficient, meter)?
        else {
            return Ok(None);
        };
        if let Some(congruence) = congruence {
            expression.canonicalize_variables(congruence, meter)?;
        }
        let lambda = meter.rational_from_i64_pair(coefficient)?;
        let mut scaled = MeteredLinearExpr::zero(meter)?;
        scaled.add_scaled(&expression, &lambda, meter)?;
        match mode {
            Mode::Inequality => {
                let one = meter.rational_from_i64_pair(&Rational64::one())?;
                plan.base.add_scaled(&scaled, &one, meter)?;
                plan.strict |= strict;
            }
            Mode::Equality => {
                meter.reserve_vec(&mut plan.equalities, 1)?;
                meter.charge(1, 0)?;
                plan.equalities.push(scaled);
            }
            Mode::Disequality if plan.disequality.is_none() => plan.disequality = Some(scaled),
            Mode::Disequality => return Ok(None),
        }
    }
    Ok(Some(plan))
}

fn branch_base(
    plan: &Plan,
    branch: usize,
    meter: &mut ProgressMeter<'_>,
) -> Result<MeteredLinearExpr, FarkasValidationError> {
    meter.charge(1, 0)?;
    let mut base = plan.base.clone_metered(meter)?;
    if let Some(row) = &plan.disequality {
        let sign = meter.rational_from_i64_pair(&Rational64::from_integer(if branch == 0 {
            1
        } else {
            -1
        }))?;
        base.add_scaled(row, &sign, meter)?;
    }
    Ok(base)
}

fn normalize(
    terms: &TermStore,
    literal: &TheoryLit,
    coefficient: &Rational64,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<(MeteredLinearExpr, Mode, bool)>, FarkasValidationError> {
    let mut term = literal.term;
    let mut value = literal.value;
    loop {
        meter.charge(1, 0)?;
        if term.index() >= terms.len() {
            return Err(FarkasValidationError::NonArithmeticLiteral { term });
        }
        let TermData::Not(inner) = terms.get(term) else {
            break;
        };
        term = *inner;
        value = !value;
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    let &[lhs, rhs] = args.as_slice() else {
        return Err(FarkasValidationError::NonArithmeticLiteral { term });
    };
    let mode = match name.as_str() {
        "<" | "<=" | ">" | ">=" => Mode::Inequality,
        "=" if value => Mode::Equality,
        "distinct" if !value => Mode::Equality,
        "=" | "distinct" => Mode::Disequality,
        _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
    };
    if coefficient.is_negative() && mode != Mode::Equality {
        return Ok(None);
    }
    if mode == Mode::Inequality {
        let (expression, strict) = super::normalize_inequality(terms, literal, meter)?;
        return Ok(Some((expression, mode, strict)));
    }
    let mut expression = parse_linear_expr(terms, lhs, meter)?;
    let right = parse_linear_expr(terms, rhs, meter)?;
    let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
    expression.add_scaled(&right, &minus_one, meter)?;
    Ok(Some((expression, mode, false)))
}

fn contradicts(
    expression: &MeteredLinearExpr,
    strict: bool,
    meter: &mut ProgressMeter<'_>,
) -> Result<bool, FarkasValidationError> {
    meter.charge(1, 0)?;
    Ok(expression.coeffs.is_empty()
        && if strict {
            !expression.constant.is_negative()
        } else {
            expression.constant.is_positive()
        })
}

fn orientations_hold(
    base: &MeteredLinearExpr,
    strict: bool,
    equalities: &[MeteredLinearExpr],
    meter: &mut ProgressMeter<'_>,
) -> Result<bool, FarkasValidationError> {
    let one = meter.rational_from_i64_pair(&Rational64::one())?;
    let minus_one = meter.rational_from_i64_pair(&-Rational64::one())?;
    if equalities.len() <= 10 {
        // Same lexicographic alternatives as the legacy exhaustive search.
        for choices in 0..(1usize << equalities.len()) {
            meter.charge(1, 0)?;
            let mut sum = base.clone_metered(meter)?;
            for (index, row) in equalities.iter().enumerate() {
                meter.charge(1, 0)?;
                let reverse = choices & (1usize << (equalities.len() - index - 1)) != 0;
                sum.add_scaled(row, if reverse { &minus_one } else { &one }, meter)?;
            }
            if contradicts(&sum, strict, meter)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    // Above 1024 orientations, retain exactly all-first and each SINGLE flip.
    let mut sum = base.clone_metered(meter)?;
    for row in equalities {
        meter.charge(1, 0)?;
        sum.add_scaled(row, &one, meter)?;
    }
    if contradicts(&sum, strict, meter)? {
        return Ok(true);
    }
    let two = meter.rational_from_i64_pair(&Rational64::from_integer(2))?;
    let minus_two = meter.rational_from_i64_pair(&Rational64::from_integer(-2))?;
    for row in equalities {
        meter.charge(1, 0)?;
        sum.add_scaled(row, &minus_two, meter)?;
        let hit = contradicts(&sum, strict, meter)?;
        sum.add_scaled(row, &two, meter)?;
        if hit {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(test)]
#[path = "strict_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "full_tests.rs"]
mod full_tests;
