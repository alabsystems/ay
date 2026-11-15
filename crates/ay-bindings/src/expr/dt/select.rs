// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Checked struct projection. Enum selectors retain their partial semantics.

use std::collections::HashMap;
use std::sync::Arc;

use crate::{Sort, SortError};

use super::check::Check;
use super::{Expr, ExprValue};

type Key = (*const ExprValue, *const crate::sort::SortInner);

fn key(expr: &Expr) -> Key {
    (Arc::as_ptr(&expr.value), expr.sort.inner())
}

enum Frame<'a> {
    Visit(&'a Expr),
    Finish(&'a Expr, &'a Expr, &'a Expr, &'a Expr),
}

pub(super) fn select(
    source: Expr,
    datatype_name: String,
    selector_name: String,
    result_sort: Sort,
    check: &mut Check,
) -> Result<Expr, SortError> {
    let index = check.selector(&source.sort, &datatype_name, &selector_name, &result_sort)?;
    let mut pending = vec![Frame::Visit(&source)];
    let mut results = HashMap::new();
    while let Some(frame) = pending.pop() {
        check.charge(1)?;
        match frame {
            Frame::Visit(expr) => {
                if results.contains_key(&key(expr)) {
                    continue;
                }
                authenticate_source(expr, check)?;
                match (index, expr.value()) {
                    (Some(index), ExprValue::DatatypeConstructor { args, .. }) => {
                        let field = args
                            .get(index)
                            .ok_or_else(|| check.error("validated constructor field is missing"))?;
                        results.insert(key(expr), field.clone());
                    }
                    (
                        Some(_),
                        ExprValue::Ite {
                            cond,
                            then_expr,
                            else_expr,
                        },
                    ) => {
                        check.charge(3)?;
                        pending.push(Frame::Finish(expr, cond, then_expr, else_expr));
                        pending.push(Frame::Visit(else_expr));
                        pending.push(Frame::Visit(then_expr));
                    }
                    _ => {
                        check.charge(datatype_name.len())?;
                        check.charge(selector_name.len())?;
                        results.insert(
                            key(expr),
                            Expr {
                                sort: result_sort.clone(),
                                value: Arc::new(ExprValue::DatatypeSelector {
                                    datatype_name: datatype_name.clone(),
                                    selector_name: selector_name.clone(),
                                    expr: expr.clone(),
                                }),
                            },
                        );
                    }
                }
            }
            Frame::Finish(expr, cond, then_expr, else_expr) => {
                let then_value = results
                    .get(&key(then_expr))
                    .ok_or_else(|| check.error("missing checked then projection"))?
                    .clone();
                let else_value = results
                    .get(&key(else_expr))
                    .ok_or_else(|| check.error("missing checked else projection"))?
                    .clone();
                let value = if same_leaf(&then_value, &else_value, check)? {
                    then_value
                } else {
                    // Branch sorts and the condition were checked before descent.
                    Expr {
                        sort: result_sort.clone(),
                        value: Arc::new(ExprValue::Ite {
                            cond: cond.clone(),
                            then_expr: then_value,
                            else_expr: else_value,
                        }),
                    }
                };
                results.insert(key(expr), value);
            }
        }
    }
    results
        .remove(&key(&source))
        .ok_or_else(|| check.error("missing checked datatype projection"))
}

/// Check immediate source-node signatures before either folding or retaining it.
/// This intentionally does not claim validation of arbitrary scalar AST bodies.
pub(super) fn authenticate_source(expr: &Expr, check: &mut Check) -> Result<(), SortError> {
    match expr.value() {
        ExprValue::DatatypeConstructor {
            datatype_name,
            constructor_name,
            args,
        } => {
            check.constructor(&expr.sort, datatype_name, constructor_name, args)?;
        }
        ExprValue::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            if !cond.sort.is_bool() {
                return Err(check.error("datatype ITE condition is not Boolean"));
            }
            check.require_same_sort(&then_expr.sort, &expr.sort)?;
            check.require_same_sort(&else_expr.sort, &expr.sort)?;
        }
        _ => {}
    }
    Ok(())
}

/// Retain cheap exact collapses without recursively comparing arbitrary bodies.
/// Separate but equal compound terms may remain an equivalent ITE.
fn same_leaf(a: &Expr, b: &Expr, check: &mut Check) -> Result<bool, SortError> {
    check.charge(1)?;
    if Arc::ptr_eq(&a.value, &b.value) {
        return Ok(true);
    }
    match (a.value(), b.value()) {
        (ExprValue::BoolConst(a), ExprValue::BoolConst(b)) => Ok(a == b),
        (ExprValue::Var { name: a }, ExprValue::Var { name: b }) => check.names_equal(a, b),
        (
            ExprValue::BitVecConst {
                value: a,
                width: aw,
            },
            ExprValue::BitVecConst {
                value: b,
                width: bw,
            },
        ) if aw == bw => same_integer(a, b, check),
        (ExprValue::IntConst(a), ExprValue::IntConst(b))
        | (ExprValue::RealConst(a), ExprValue::RealConst(b)) => same_integer(a, b, check),
        _ => Ok(false),
    }
}

fn same_integer(
    a: &num_bigint::BigInt,
    b: &num_bigint::BigInt,
    check: &mut Check,
) -> Result<bool, SortError> {
    if a.bits() != b.bits() || a.sign() != b.sign() {
        return Ok(false);
    }
    let bytes = usize::try_from(a.bits().div_ceil(8))
        .map_err(|_| check.error("integer comparison exceeds signature check budget"))?;
    check.charge(bytes)?;
    Ok(a == b)
}
