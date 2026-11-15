// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Build exact payload bytes from already completed child occurrences.

use super::super::{bytes::Bytes, input::Labels, operators, order, spelling, Control, QueryError};
use crate::{ChcExpr, ChcSort};

enum ChildOrder {
    Original,
    Canonical,
}

pub(super) fn sort<C: Control>(
    sort: &ChcSort,
    values: &[Bytes],
    control: &mut C,
) -> Result<Bytes, QueryError> {
    let mut out = Bytes::new(control)?;
    match sort {
        ChcSort::Bool => out.text("Bool", control)?,
        ChcSort::Int => out.text("Int", control)?,
        ChcSort::Real => out.text("Real", control)?,
        ChcSort::BitVec(width) => {
            out.text("BitVec(", control)?;
            spelling::unsigned(&mut out, u128::from(*width), control)?;
            out.text(")", control)?;
        }
        ChcSort::Array(_, _) => {
            out.text("Array(", control)?;
            out.append(&values[0].0, control)?;
            out.text(",", control)?;
            out.append(&values[1].0, control)?;
            out.text(")", control)?;
        }
        ChcSort::Uninterpreted(name) => {
            out.text("Uninterpreted(", control)?;
            spelling::quoted(&mut out, name, control)?;
            out.text(")", control)?;
        }
        ChcSort::Datatype { .. } => {
            return Err(QueryError::Invalid(
                "datatype-bearing normalized input is unsupported",
            ))
        }
    }
    Ok(out)
}

pub(super) fn expression<C: Control>(
    expr: &ChcExpr,
    values: &[Bytes],
    labels: &Labels,
    control: &mut C,
) -> Result<Bytes, QueryError> {
    control.offer(1, 0)?;
    if matches!(
        expr,
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _)
    ) {
        return scalar(expr, control);
    }
    let mut out = Bytes::new(control)?;
    match expr {
        ChcExpr::ArrayLambda(lambda) => {
            out.text("array-lambda(", control)?;
            spelling::quoted(&mut out, &lambda.binder().name, control)?;
            out.text(":", control)?;
            out.append(&values[0].0, control)?;
            out.text(";[", control)?;
            for (index, formal) in lambda.formals().iter().enumerate() {
                if index != 0 {
                    out.text(",", control)?;
                }
                spelling::quoted(&mut out, &formal.name, control)?;
                out.text(":", control)?;
                out.append(&values[index + 1].0, control)?;
            }
            let body = lambda.formals().len() + 1;
            out.text("];", control)?;
            out.append(&values[body].0, control)?;
            out.text(";[", control)?;
            for (index, capture) in values[body + 1..].iter().enumerate() {
                if index != 0 {
                    out.text(",", control)?;
                }
                out.append(&capture.0, control)?;
            }
            out.text("])", control)?;
        }
        ChcExpr::Var(var) => {
            out.text("var:", control)?;
            spelling::quoted(&mut out, &var.name, control)?;
            out.text(":", control)?;
            out.append(&values[0].0, control)?;
        }
        ChcExpr::Op(op, _) => {
            out.text("op:", control)?;
            operators::write(&mut out, *op, control)?;
            let order = if super::super::super::payload::is_commutative_op(*op) {
                ChildOrder::Canonical
            } else {
                ChildOrder::Original
            };
            arguments(&mut out, values, order, control)?;
        }
        ChcExpr::PredicateApp(name, pred, _) => {
            out.text("pred-expr:", control)?;
            labels.write(&mut out, *pred, control)?;
            out.text(":", control)?;
            spelling::quoted(&mut out, name, control)?;
            arguments(&mut out, values, ChildOrder::Original, control)?;
        }
        ChcExpr::FuncApp(name, _, _) => {
            out.text("func:", control)?;
            spelling::quoted(&mut out, name, control)?;
            out.text(":", control)?;
            out.append(&values[0].0, control)?;
            arguments(&mut out, &values[1..], ChildOrder::Original, control)?;
        }
        ChcExpr::ConstArrayMarker(_) => {
            out.text("const-array-marker:", control)?;
            out.append(&values[0].0, control)?;
        }
        ChcExpr::IsTesterMarker(name) => {
            out.text("is-tester:", control)?;
            spelling::quoted(&mut out, name, control)?;
        }
        ChcExpr::ConstArray(_, _) => {
            out.text("const-array:", control)?;
            out.append(&values[0].0, control)?;
            out.text(":", control)?;
            out.append(&values[1].0, control)?;
        }
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            return Err(QueryError::Invalid("scalar canonical dispatch mismatch"));
        }
    }
    Ok(out)
}

fn scalar<C: Control>(expr: &ChcExpr, control: &mut C) -> Result<Bytes, QueryError> {
    let mut out = Bytes::new(control)?;
    match expr {
        ChcExpr::Bool(value) => {
            out.text(if *value { "bool:true" } else { "bool:false" }, control)?
        }
        ChcExpr::Int(value) => {
            out.text("int:", control)?;
            spelling::signed(&mut out, *value, control)?;
        }
        ChcExpr::Real(n, d) => {
            out.text("real:", control)?;
            spelling::signed(&mut out, i128::from(*n), control)?;
            out.text("/", control)?;
            spelling::signed(&mut out, i128::from(*d), control)?;
        }
        ChcExpr::BitVec(value, width) => {
            out.text("bv", control)?;
            spelling::unsigned(&mut out, u128::from(*width), control)?;
            out.text(":", control)?;
            spelling::unsigned(&mut out, *value, control)?;
        }
        _ => return Err(QueryError::Invalid("nonscalar canonical dispatch mismatch")),
    }
    Ok(out)
}

fn arguments<C: Control>(
    out: &mut Bytes,
    values: &[Bytes],
    ordering: ChildOrder,
    control: &mut C,
) -> Result<(), QueryError> {
    out.text("(", control)?;
    if matches!(ordering, ChildOrder::Canonical) {
        let indices = order::indices(values.len(), control, |a, b, control| {
            order::compare(&values[a].0, &values[b].0, control)
        })?;
        for (position, index) in indices.into_iter().enumerate() {
            control.offer(2, 0)?;
            if position != 0 {
                out.text(",", control)?;
            }
            out.append(&values[index].0, control)?;
        }
    } else {
        for index in 0..values.len() {
            control.offer(2, 0)?;
            if index != 0 {
                out.text(",", control)?;
            }
            out.append(&values[index].0, control)?;
        }
    }
    out.text(")", control)
}
