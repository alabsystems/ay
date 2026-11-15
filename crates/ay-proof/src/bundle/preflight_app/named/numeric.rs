// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn bitvector(app: &mut App<'_, '_>, rule: Rule) -> Result<(), ProofCheckError> {
    app.arity(if matches!(rule, Rule::BvUnary) { 1 } else { 2 })?;
    let first = app.arg(0)?;
    let valid = match rule {
        Rule::BvUnary => matches!(first, Sort::BitVec(_)) && app.equal_sorts(app.result, first)?,
        Rule::BvBinary | Rule::BvCompare => {
            let second = app.arg(1)?;
            matches!(first, Sort::BitVec(_))
                && app.equal_sorts(first, second)?
                && if matches!(rule, Rule::BvCompare) {
                    matches!(app.result, Sort::Bool)
                } else {
                    app.equal_sorts(app.result, first)?
                }
        }
        Rule::Concat => {
            let second = app.arg(1)?;
            let (Sort::BitVec(left), Sort::BitVec(right), Sort::BitVec(result)) =
                (first, second, app.result)
            else {
                return app.invalid("operands and result must be bit-vectors");
            };
            if left.width.checked_add(right.width) != Some(result.width) {
                return app.invalid("result width must equal the sum of operand widths");
            }
            true
        }
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    if !valid {
        return app.invalid("must consume and return consistent bit-vector sorts");
    }
    Ok(())
}

pub(super) fn floating_point(app: &mut App<'_, '_>, rule: Rule) -> Result<(), ProofCheckError> {
    if matches!(rule, Rule::FpCompose) {
        return compose(app);
    }
    app.arity(if matches!(rule, Rule::FpCompare) {
        2
    } else {
        1
    })?;
    let first = app.arg(0)?;
    if !matches!(first, Sort::FloatingPoint(..)) {
        return app.invalid("must consume a floating-point operand");
    }
    let valid = match rule {
        Rule::FpUnary => app.equal_sorts(app.result, first)?,
        Rule::FpClassify => matches!(app.result, Sort::Bool),
        Rule::FpCompare => {
            let second = app.arg(1)?;
            app.equal_sorts(first, second)? && matches!(app.result, Sort::Bool)
        }
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    if !valid {
        return app.invalid("has inconsistent floating-point operand or result sorts");
    }
    Ok(())
}

fn compose(app: &mut App<'_, '_>) -> Result<(), ProofCheckError> {
    app.arity(3)?;
    let (Sort::BitVec(sign), Sort::BitVec(exponent), Sort::BitVec(significand)) =
        (app.arg(0)?, app.arg(1)?, app.arg(2)?)
    else {
        return app.invalid("operands must be bit-vectors");
    };
    let Sort::FloatingPoint(result_exponent, result_significand) = app.result else {
        return app.invalid("result must be floating-point sorted");
    };
    if sign.width != 1
        || exponent.width != *result_exponent
        || significand.width.checked_add(1) != Some(*result_significand)
    {
        return app.invalid("component widths do not match its result format");
    }
    Ok(())
}
