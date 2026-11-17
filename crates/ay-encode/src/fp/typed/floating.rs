// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed literal-RM FP forms; numeric casts admit only bounded literal RNE.

use ay_bindings::{Expr, ExprValue, RoundingMode};

use super::{both, fixed, scalar, Operator, Scalar, Shape};
use crate::fp::FpAdapterError;

pub(super) fn describe(expr: &Expr, result: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    use ExprValue::{
        BvToFp, BvToFpUnsigned, FpAbs, FpAdd, FpDiv, FpFma, FpFromBvs, FpMinusInfinity,
        FpMinusZero, FpMul, FpNaN, FpNeg, FpPlusInfinity, FpPlusZero, FpRem, FpSqrt, FpSub,
        FpTruncatingRem,
    };
    match expr.value() {
        FpPlusZero { eb, sb }
        | FpMinusZero { eb, sb }
        | FpPlusInfinity { eb, sb }
        | FpMinusInfinity { eb, sb }
        | FpNaN { eb, sb } => {
            if result != Scalar::Fp(*eb, *sb) {
                return Err(FpAdapterError::Invalid("typed FP literal"));
            }
            let name = match expr.value() {
                FpPlusZero { .. } => "+zero",
                FpMinusZero { .. } => "-zero",
                FpPlusInfinity { .. } => "+oo",
                FpMinusInfinity { .. } => "-oo",
                _ => "NaN",
            };
            Ok(Shape {
                op: Operator::Special(name, *eb, *sb),
                children: fixed(None, None, None),
            })
        }
        FpAbs(a) | FpNeg(a) => {
            if !matches!(result, Scalar::Fp(_, _)) || scalar(a)? != result {
                return Err(FpAdapterError::Invalid("typed unary FP"));
            }
            let name = if matches!(expr.value(), FpAbs(_)) {
                "fp.abs"
            } else {
                "fp.neg"
            };
            Ok(Shape {
                op: Operator::Apply(name, None),
                children: fixed(Some(a), None, None),
            })
        }
        FpAdd(..) | FpSub(..) | FpMul(..) | FpDiv(..) => arithmetic(expr, result),
        FpSqrt(..) | FpFma(..) => rounded(expr, result),
        BvToFp(..) | BvToFpUnsigned(..) => numeric(expr, result),
        FpRem(a, b) | FpTruncatingRem(a, b) => {
            if !matches!(result, Scalar::Fp(_, _)) {
                return Err(FpAdapterError::Invalid("typed remainder result"));
            }
            both(a, b, result)?;
            Ok(Shape {
                op: Operator::Apply(
                    if matches!(expr.value(), FpRem(..)) {
                        "fp.rem"
                    } else {
                        "__ay_fp_truncating_rem"
                    },
                    None,
                ),
                children: fixed(Some(a), Some(b), None),
            })
        }
        FpFromBvs(a, b, c) => fields(result, a, b, c),
        _ => predicate(expr, result),
    }
}

fn numeric(expr: &Expr, result: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    let (name, rm, word, e, s) = match expr.value() {
        ExprValue::BvToFp(rm, word, e, s) => ("to_fp", rm, word, e, s),
        ExprValue::BvToFpUnsigned(rm, word, e, s) => ("to_fp_unsigned", rm, word, e, s),
        _ => return Err(FpAdapterError::Invalid("typed numeric source")),
    };
    if result != Scalar::Fp(*e, *s) || !matches!(result, Scalar::Fp(8, 24) | Scalar::Fp(11, 53)) {
        return Err(FpAdapterError::Invalid("typed numeric result"));
    }
    if *rm != RoundingMode::RNE {
        return Err(FpAdapterError::Unsupported(
            "numeric conversion requires literal RNE",
        ));
    }
    if !matches!(scalar(word)?, Scalar::Bv(8..=64))
        || !matches!(
            word.value(),
            ExprValue::Var { .. } | ExprValue::BitVecConst { .. } | ExprValue::BvExtract { .. }
        )
    {
        return Err(FpAdapterError::Unsupported("typed numeric word"));
    }
    Ok(Shape {
        op: Operator::Numeric(name, *e, *s),
        children: fixed(Some(word), None, None),
    })
}

fn mode(rm: RoundingMode) -> Result<usize, FpAdapterError> {
    match rm {
        RoundingMode::RNE => Ok(0),
        RoundingMode::RNA => Ok(1),
        RoundingMode::RTP => Ok(2),
        RoundingMode::RTN => Ok(3),
        RoundingMode::RTZ => Ok(4),
        _ => Err(FpAdapterError::Unsupported("literal rounding mode")),
    }
}

fn arithmetic(expr: &Expr, result: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    use ExprValue::{FpAdd, FpDiv, FpMul, FpSub};
    let (name, r, a, b) = match expr.value() {
        FpAdd(r, a, b) => ("fp.add", r, a, b),
        FpSub(r, a, b) => ("fp.sub", r, a, b),
        FpMul(r, a, b) => ("fp.mul", r, a, b),
        FpDiv(r, a, b) => ("fp.div", r, a, b),
        _ => return Err(FpAdapterError::Invalid("typed arithmetic source")),
    };
    if !matches!(result, Scalar::Fp(_, _)) {
        return Err(FpAdapterError::Invalid("typed arithmetic result"));
    }
    both(a, b, result)?;
    Ok(Shape {
        op: Operator::Apply(name, Some(mode(*r)?)),
        children: fixed(Some(a), Some(b), None),
    })
}

// The literal RM is inserted by the positional builder, not a new source input.
// All original operands stay visited, including a zero FMA factor.
fn rounded(expr: &Expr, result: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    use ExprValue::{FpFma, FpSqrt};
    let (name, rm, children) = match expr.value() {
        FpSqrt(rm, a) => ("fp.sqrt", rm, fixed(Some(a), None, None)),
        FpFma(rm, a, b, c) => ("fp.fma", rm, fixed(Some(a), Some(b), Some(c))),
        _ => return Err(FpAdapterError::Invalid("typed rounded source")),
    };
    if !matches!(result, Scalar::Fp(_, _)) {
        return Err(FpAdapterError::Invalid("typed rounded result"));
    }
    for child in children.clone() {
        if scalar(child)? != result {
            return Err(FpAdapterError::Invalid("typed rounded operand sorts"));
        }
    }
    Ok(Shape {
        op: Operator::Apply(name, Some(mode(*rm)?)),
        children,
    })
}

fn fields<'a>(
    result: Scalar,
    a: &'a Expr,
    b: &'a Expr,
    c: &'a Expr,
) -> Result<Shape<'a>, FpAdapterError> {
    let Scalar::Fp(e, s) = result else {
        return Err(FpAdapterError::Invalid("typed field result"));
    };
    if scalar(a)? != Scalar::Bv(1) || scalar(b)? != Scalar::Bv(e) || scalar(c)? != Scalar::Bv(s - 1)
    {
        return Err(FpAdapterError::Invalid("typed raw fields"));
    }
    Ok(Shape {
        op: Operator::Apply("fp", None),
        children: fixed(Some(a), Some(b), Some(c)),
    })
}

fn predicate(expr: &Expr, result: Scalar) -> Result<Shape<'_>, FpAdapterError> {
    use ExprValue::{FpEq, FpGe, FpGt, FpLe, FpLt};
    if result != Scalar::Bool {
        return Err(FpAdapterError::Unsupported("typed FP source operation"));
    }
    match expr.value() {
        FpEq(a, b) | FpLt(a, b) | FpLe(a, b) | FpGt(a, b) | FpGe(a, b) => {
            let kind = scalar(a)?;
            if !matches!(kind, Scalar::Fp(_, _)) {
                return Err(FpAdapterError::Invalid("typed FP comparison"));
            }
            both(a, b, kind)?;
            let name = match expr.value() {
                FpEq(..) => "fp.eq",
                FpLt(..) => "fp.lt",
                FpLe(..) => "fp.leq",
                FpGt(..) => "fp.gt",
                _ => "fp.geq",
            };
            Ok(Shape {
                op: Operator::Apply(name, None),
                children: fixed(Some(a), Some(b), None),
            })
        }
        _ => classification(expr),
    }
}

fn classification(expr: &Expr) -> Result<Shape<'_>, FpAdapterError> {
    use ExprValue::{
        FpIsInfinite, FpIsNaN, FpIsNegative, FpIsNormal, FpIsPositive, FpIsSubnormal, FpIsZero,
    };
    let (name, a) = match expr.value() {
        FpIsNaN(a) => ("fp.isNaN", a),
        FpIsInfinite(a) => ("fp.isInfinite", a),
        FpIsZero(a) => ("fp.isZero", a),
        FpIsNormal(a) => ("fp.isNormal", a),
        FpIsSubnormal(a) => ("fp.isSubnormal", a),
        FpIsPositive(a) => ("fp.isPositive", a),
        FpIsNegative(a) => ("fp.isNegative", a),
        _ => return Err(FpAdapterError::Unsupported("typed source operation")),
    };
    if !matches!(scalar(a)?, Scalar::Fp(_, _)) {
        return Err(FpAdapterError::Invalid("typed classify"));
    }
    Ok(Shape {
        op: Operator::Apply(name, None),
        children: fixed(Some(a), None, None),
    })
}
