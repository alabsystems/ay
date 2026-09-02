// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed syntax classification for progress-metered Farkas rows.

use num_traits::Zero;

use crate::{Constant, Sort, Symbol, TermData, TermId, TermStore, TheoryLit};

const MAX_CLASSIFIER_VISITS: usize = 4096;

/// Arithmetic row kinds whose exact linear semantics the progress path covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FarkasProgressRowKind {
    /// A single oriented `<`, `<=`, `>`, or `>=` constraint.
    Inequality,
    /// An asserted binary equality, whose multiplier is sign-free.
    PositiveEquality,
    /// An asserted binary disequality, discharged by two strict branches.
    Disequality,
}

#[derive(Clone, Copy)]
enum AffineShape {
    Constant,
    Linear,
}

/// Classify one row only when both operands use the explicit affine parser
/// surface. Unknown applications are deliberately rejected rather than treated
/// as opaque variables: the full validator may need congruence closure for them.
#[must_use]
pub fn farkas_progress_row_kind(
    terms: &TermStore,
    literal: &TheoryLit,
) -> Option<FarkasProgressRowKind> {
    let mut visits = MAX_CLASSIFIER_VISITS;
    classify_row(terms, literal, &mut || {
        let Some(next) = visits.checked_sub(1) else {
            return false;
        };
        visits = next;
        true
    })
    .ok()
    .flatten()
}

pub(super) fn metered_progress_row_kind(
    terms: &TermStore,
    literal: &TheoryLit,
    meter: &mut super::ProgressMeter<'_>,
) -> Result<Option<FarkasProgressRowKind>, super::FarkasValidationError> {
    let mut visits = MAX_CLASSIFIER_VISITS;
    classify_row(terms, literal, &mut || {
        let Some(next) = visits.checked_sub(1) else {
            return false;
        };
        visits = next;
        meter.charge(1, 0).is_ok()
    })
    .map_err(|()| super::FarkasValidationError::ResourceLimit)
}

fn classify_row(
    terms: &TermStore,
    literal: &TheoryLit,
    visit: &mut dyn FnMut() -> bool,
) -> Result<Option<FarkasProgressRowKind>, ()> {
    let mut term = literal.term;
    let mut value = literal.value;
    loop {
        if !visit() {
            return Err(());
        }
        let TermData::Not(inner) = terms.get(term) else {
            break;
        };
        term = *inner;
        value = !value;
    }
    if !visit() {
        return Err(());
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return Ok(None);
    };
    let mut operands = args.iter();
    let (Some(&lhs), Some(&rhs), None) = (operands.next(), operands.next(), operands.next()) else {
        return Ok(None);
    };
    if affine_shape(terms, lhs, visit)?.is_none() || affine_shape(terms, rhs, visit)?.is_none() {
        return Ok(None);
    }
    let kind = match name.as_str() {
        "<" | "<=" | ">" | ">=" => FarkasProgressRowKind::Inequality,
        "=" if value => FarkasProgressRowKind::PositiveEquality,
        "distinct" if !value => FarkasProgressRowKind::PositiveEquality,
        "=" | "distinct" => FarkasProgressRowKind::Disequality,
        _ => return Ok(None),
    };
    Ok(Some(kind))
}

fn affine_shape(
    terms: &TermStore,
    term: TermId,
    visit: &mut dyn FnMut() -> bool,
) -> Result<Option<AffineShape>, ()> {
    if !visit() {
        return Err(());
    }
    if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
        return Ok(None);
    }
    let shape = match terms.get(term) {
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => Some(AffineShape::Constant),
        TermData::Var(_, _) => Some(AffineShape::Linear),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => aggregate_affine(terms, args, visit)?,
            "-" if args.len() == 1 || args.len() >= 2 => aggregate_affine(terms, args, visit)?,
            "*" => product_shape(terms, args, visit)?,
            "/" => match args.as_slice() {
                &[dividend, divisor] if literal_nonzero_number(terms, divisor, visit)? => {
                    affine_shape(terms, dividend, visit)?
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    };
    Ok(shape)
}

fn aggregate_affine(
    terms: &TermStore,
    args: &[TermId],
    visit: &mut dyn FnMut() -> bool,
) -> Result<Option<AffineShape>, ()> {
    let mut linear = false;
    for &arg in args {
        match affine_shape(terms, arg, visit)? {
            Some(AffineShape::Constant) => {}
            Some(AffineShape::Linear) => linear = true,
            None => return Ok(None),
        }
    }
    Ok(Some(if linear {
        AffineShape::Linear
    } else {
        AffineShape::Constant
    }))
}

fn product_shape(
    terms: &TermStore,
    args: &[TermId],
    visit: &mut dyn FnMut() -> bool,
) -> Result<Option<AffineShape>, ()> {
    let mut linear = false;
    for &arg in args {
        match affine_shape(terms, arg, visit)? {
            Some(AffineShape::Constant) => {}
            Some(AffineShape::Linear) => {
                if linear {
                    return Ok(None);
                }
                linear = true;
            }
            None => return Ok(None),
        }
    }
    Ok(Some(if linear {
        AffineShape::Linear
    } else {
        AffineShape::Constant
    }))
}

fn literal_nonzero_number(
    terms: &TermStore,
    term: TermId,
    visit: &mut dyn FnMut() -> bool,
) -> Result<bool, ()> {
    if !visit() {
        return Err(());
    }
    Ok(match terms.get(term) {
        TermData::Const(Constant::Int(value)) => !value.is_zero(),
        TermData::Const(Constant::Rational(value)) => !value.0.is_zero(),
        _ => false,
    })
}
