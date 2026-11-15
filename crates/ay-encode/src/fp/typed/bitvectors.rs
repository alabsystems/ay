// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact <=64-bit comparisons; no arithmetic or conversion alias admission.

use ay_bindings::{Expr, ExprValue};

use super::{fixed, scalar, Operator, Scalar, Shape};
use crate::fp::FpAdapterError;

pub(super) fn describe(expr: &Expr) -> Result<Shape<'_>, FpAdapterError> {
    let (name, left, right) = match expr.value() {
        ExprValue::BvULt(a, b) => ("bvult", a, b),
        ExprValue::BvULe(a, b) => ("bvule", a, b),
        ExprValue::BvUGt(a, b) => ("bvugt", a, b),
        ExprValue::BvUGe(a, b) => ("bvuge", a, b),
        ExprValue::BvSLt(a, b) => ("bvslt", a, b),
        ExprValue::BvSLe(a, b) => ("bvsle", a, b),
        ExprValue::BvSGt(a, b) => ("bvsgt", a, b),
        ExprValue::BvSGe(a, b) => ("bvsge", a, b),
        _ => return Err(FpAdapterError::Unsupported("typed BV predicate kind")),
    };
    if scalar(expr)? != Scalar::Bool
        || !matches!(scalar(left)?, Scalar::Bv(_))
        || scalar(left)? != scalar(right)?
    {
        return Err(FpAdapterError::Invalid("typed BV predicate sorts"));
    }
    // Plan retains BOTH complete operands. A later raw/unchosen descendant
    // cannot turn an unsupported arithmetic expression into a free input.
    Ok(Shape {
        op: Operator::Apply(name, None),
        children: fixed(Some(left), Some(right), None),
    })
}
