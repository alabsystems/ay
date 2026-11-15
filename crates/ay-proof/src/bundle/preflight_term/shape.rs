// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve the existing raw term shape and prior-child invariants.

use super::*;

pub(super) fn validate(
    entries: &[(TermData, Sort)],
    index: usize,
    data: &TermData,
    result: &Sort,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    match data {
        TermData::Const(value) => constant(value, result, index, progress),
        TermData::Var(..) => Ok(()),
        TermData::App(symbol, args) => {
            for &arg in args {
                prior_sort(entries, index, arg, progress)?;
            }
            super::super::preflight_app::validate_app_signature_with_progress(
                entries, index, symbol, args, result, progress,
            )
        }
        TermData::Let(bindings, body) => {
            let mut names = BTreeSet::new();
            for (name, value) in bindings {
                unique_name(&mut names, name, index, progress)?;
                prior_sort(entries, index, *value, progress)?;
            }
            let actual = prior_sort(entries, index, *body, progress)?;
            if !equal_sorts(actual, result, index, progress)? {
                return invalid(index, "let body and recorded sort disagree", progress);
            }
            Ok(())
        }
        TermData::Not(inner) => {
            let inner_sort = prior_sort(entries, index, *inner, progress)?;
            if !matches!(result, Sort::Bool) || !matches!(inner_sort, Sort::Bool) {
                return invalid(
                    index,
                    "not term and its child must both have sort Bool",
                    progress,
                );
            }
            Ok(())
        }
        TermData::Ite(condition, then_branch, else_branch) => conditional(
            entries,
            index,
            [*condition, *then_branch, *else_branch],
            result,
            progress,
        ),
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            if !matches!(result, Sort::Bool) {
                return invalid(index, "quantifier must have sort Bool", progress);
            }
            quantified(entries, index, vars, *body, triggers, progress)
        }
        _ => invalid(index, "uses an unsupported term-data variant", progress),
    }
}

fn constant(
    value: &Constant,
    sort: &Sort,
    index: usize,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge(progress, 3, 0)?;
    let valid = match value {
        Constant::Bool(_) => matches!(sort, Sort::Bool),
        Constant::Int(_) => matches!(sort, Sort::Int),
        Constant::Rational(value) => {
            matches!(sort, Sort::Real) && value.0.denom().sign() != Sign::NoSign
        }
        Constant::FiniteField { value, field } => {
            sort == &Sort::FiniteField(*field) && *value < field.modulus()
        }
        Constant::String(_) => matches!(sort, Sort::String),
        Constant::BitVec { value, width } => {
            matches!(sort, Sort::BitVec(bitvec) if bitvec.width == *width)
                && value.sign() != Sign::Minus
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        invalid(
            index,
            "constant has incompatible recorded sort or non-canonical value",
            progress,
        )
    }
}

fn conditional(
    entries: &[(TermData, Sort)],
    index: usize,
    children: [TermId; 3],
    result: &Sort,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    let condition = prior_sort(entries, index, children[0], progress)?;
    let left = prior_sort(entries, index, children[1], progress)?;
    let right = prior_sort(entries, index, children[2], progress)?;
    if !matches!(condition, Sort::Bool)
        || !equal_sorts(left, right, index, progress)?
        || !equal_sorts(left, result, index, progress)?
    {
        return invalid(
            index,
            "ite has inconsistent condition, branch, or result sorts",
            progress,
        );
    }
    Ok(())
}

fn quantified(
    entries: &[(TermData, Sort)],
    index: usize,
    variables: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    if !matches!(prior_sort(entries, index, body, progress)?, Sort::Bool) {
        return invalid(index, "quantifier has non-Boolean body sort", progress);
    }
    let mut names = BTreeSet::new();
    for (name, sort) in variables {
        unique_name(&mut names, name, index, progress)?;
        validate_sort_with_progress(sort, index, "quantifier binding sort", 0, progress)?;
    }
    for group in triggers {
        charge(progress, 1, 0)?;
        for &trigger in group {
            prior_sort(entries, index, trigger, progress)?;
        }
    }
    Ok(())
}
