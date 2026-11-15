// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete native FP arithmetic/conversion signatures, not source authority.
//!
//! SMT-LIB FloatingPoint 2.7: https://smt-lib.org/theories-FloatingPoint.shtml.
//! `fp.to_ieee_bv` and rounded Int conversion are existing AY extensions.
//! These checks authenticate only builtin *shape*. They do not authenticate a
//! declaration environment, Rust target/occurrence, or an FP/CNF proof bridge.

use super::*;

#[derive(Clone, Copy)]
enum Rule {
    RoundingLiteral,
    RoundedUnary,
    RoundedBinary,
    RoundedTernary,
    Binary,
    ToReal,
    ToIeee,
}

#[derive(Clone, Copy)]
enum FpConversion {
    SignedOrInterchange,
    Unsigned,
}

const NAMED: &[(Rule, &[&str])] = &[
    (
        Rule::RoundingLiteral,
        &[
            "RNE",
            "RNA",
            "RTP",
            "RTN",
            "RTZ",
            "roundNearestTiesToEven",
            "roundNearestTiesToAway",
            "roundTowardPositive",
            "roundTowardNegative",
            "roundTowardZero",
        ],
    ),
    (Rule::RoundedUnary, &["fp.sqrt", "fp.roundToIntegral"]),
    (
        Rule::RoundedBinary,
        &["fp.add", "fp.sub", "fp.mul", "fp.div"],
    ),
    (Rule::RoundedTernary, &["fp.fma"]),
    (Rule::Binary, &["fp.rem", "fp.min", "fp.max"]),
    (Rule::ToReal, &["fp.to_real"]),
    (Rule::ToIeee, &["fp.to_ieee_bv"]),
];

const INDEXED: &[&str] = &["to_fp", "to_fp_unsigned", "fp.to_ubv", "fp.to_sbv"];

pub(super) fn named(app: &mut App<'_, '_>) -> Result<bool, ProofCheckError> {
    for &(rule, names) in NAMED {
        app.charge(1, 0)?;
        for &name in names {
            if app.named(name)? {
                validate_named(app, rule)?;
                return Ok(true);
            }
        }
    }
    for &name in INDEXED {
        if app.named(name)? {
            return app.invalid("floating-point conversion must be an indexed symbol");
        }
    }
    Ok(false)
}

fn rounding_mode(app: &mut App<'_, '_>, sort: &Sort) -> Result<(), ProofCheckError> {
    app.charge(1, 0)?;
    if let Sort::Uninterpreted(name) = sort {
        // Borrowed name comparison, with no speculative owned sort/String.
        app.charge(name.len().min("RoundingMode".len()) + 1, 0)?;
        if name == "RoundingMode" {
            return Ok(());
        }
    }
    app.invalid("rounding operand or literal must have the native RoundingMode sort")
}

fn fp_operand<'a>(app: &mut App<'a, '_>, index: usize) -> Result<&'a Sort, ProofCheckError> {
    let sort = app.arg(index)?;
    if !matches!(sort, Sort::FloatingPoint(exponent, significand) if *exponent > 1 && *significand > 1)
    {
        return app.invalid("operand must have a valid floating-point format");
    }
    Ok(sort)
}

fn validate_named(app: &mut App<'_, '_>, rule: Rule) -> Result<(), ProofCheckError> {
    let (arity, first_fp) = match rule {
        Rule::RoundingLiteral => {
            app.arity(0)?;
            let result = app.result;
            return rounding_mode(app, result);
        }
        Rule::RoundedUnary => (2, 1),
        Rule::RoundedBinary => (3, 1),
        Rule::RoundedTernary => (4, 1),
        Rule::Binary => (2, 0),
        Rule::ToReal | Rule::ToIeee => (1, 0),
    };
    app.arity(arity)?;
    if first_fp == 1 {
        let rounding = app.arg(0)?;
        rounding_mode(app, rounding)?;
    }
    let first = fp_operand(app, first_fp)?;
    for index in first_fp + 1..arity {
        let next = fp_operand(app, index)?;
        if !app.equal_sorts(first, next)? {
            return app.invalid("floating-point operands must have one identical format");
        }
    }
    let valid_result = match rule {
        Rule::ToReal => matches!(app.result, Sort::Real),
        Rule::ToIeee => {
            let (Sort::FloatingPoint(exponent, significand), Sort::BitVec(result)) =
                (first, app.result)
            else {
                return app.invalid("IEEE interchange result must be a bit-vector");
            };
            exponent.checked_add(*significand) == Some(result.width)
        }
        _ => app.equal_sorts(first, app.result)?,
    };
    if !valid_result {
        return app.invalid("floating-point operation has an inconsistent result sort");
    }
    Ok(())
}

pub(super) fn indexed(app: &mut App<'_, '_>, indices: &[u32]) -> Result<bool, ProofCheckError> {
    for &name in INDEXED {
        if app.named(name)? {
            match name {
                "to_fp" => to_fp(app, indices, FpConversion::SignedOrInterchange)?,
                "to_fp_unsigned" => to_fp(app, indices, FpConversion::Unsigned)?,
                _ => to_bv(app, indices)?,
            }
            return Ok(true);
        }
    }
    for &(_, names) in NAMED {
        app.charge(1, 0)?;
        for &name in names {
            if app.named(name)? {
                return app.invalid("must be a named symbol without indices");
            }
        }
    }
    Ok(false)
}

fn to_fp(
    app: &mut App<'_, '_>,
    indices: &[u32],
    conversion: FpConversion,
) -> Result<(), ProofCheckError> {
    app.charge(3, 0)?;
    let Sort::FloatingPoint(exponent, significand) = app.result else {
        return app.invalid("conversion result must be floating-point sorted");
    };
    if *exponent <= 1 || *significand <= 1 || indices != [*exponent, *significand] {
        return app.invalid("floating-point conversion indices must match its valid result format");
    }
    if matches!(conversion, FpConversion::SignedOrInterchange) && app.args.len() == 1 {
        let Sort::BitVec(source) = app.arg(0)? else {
            return app.invalid("unrounded interchange conversion requires a bit-vector");
        };
        if exponent.checked_add(*significand) != Some(source.width) {
            return app.invalid("interchange source width must equal exponent plus significand");
        }
        return Ok(());
    }
    app.arity(2)?;
    let rounding = app.arg(0)?;
    rounding_mode(app, rounding)?;
    let source = app.arg(1)?;
    let valid_source = if matches!(conversion, FpConversion::Unsigned) {
        matches!(source, Sort::BitVec(width) if width.width > 0)
    } else {
        matches!(source, Sort::Real | Sort::Int)
            || matches!(source, Sort::BitVec(width) if width.width > 0)
            || matches!(source, Sort::FloatingPoint(e, s) if *e > 1 && *s > 1)
    };
    if !valid_source {
        return app.invalid("rounded conversion consumes an inconsistent source sort");
    }
    Ok(())
}

fn to_bv(app: &mut App<'_, '_>, indices: &[u32]) -> Result<(), ProofCheckError> {
    app.charge(2, 0)?;
    let Sort::BitVec(result) = app.result else {
        return app.invalid("integer conversion result must be bit-vector sorted");
    };
    if result.width == 0 || indices != [result.width] {
        return app.invalid("integer conversion width index must match its nonzero result width");
    }
    app.arity(2)?;
    let rounding = app.arg(0)?;
    rounding_mode(app, rounding)?;
    fp_operand(app, 1)?;
    Ok(())
}
