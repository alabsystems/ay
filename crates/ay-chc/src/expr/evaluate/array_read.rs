// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact element reads without materializing a functional array value.

use super::{eval_array_select, evaluate_expr, smt_values_equal, value_matches_sort};
use crate::expr::{maybe_grow_expr_stack, ExprDepthGuard};
use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap;

struct Read<'a> {
    index: &'a ChcExpr,
    index_value: SmtValue,
    key: ChcSort,
    element: ChcSort,
    model: &'a DetHashMap<String, SmtValue>,
}

pub(super) fn select(
    array: &ChcExpr,
    index: &ChcExpr,
    model: &DetHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    let ChcSort::Array(key, element) = array.sort() else {
        return None;
    };
    if index.sort() != *key {
        return None;
    }
    let index_value = evaluate_expr(index, model)?;
    if !admit_value(&index_value, &key) {
        return None;
    }
    Read {
        index,
        index_value,
        key: *key,
        element: *element,
        model,
    }
    .array(array)
}

// The general model predicate is deliberately partial for composite values.
// Scalar lambda indices/results require a positive match; an opaque model
// value does not become an integer or Boolean merely because it is unknown.
fn admit_value(value: &SmtValue, sort: &ChcSort) -> bool {
    let matches = value_matches_sort(value, sort);
    match sort {
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => matches == Some(true),
        _ => matches != Some(false),
    }
}

impl Read<'_> {
    fn matching_array(&self, expression: &ChcExpr) -> bool {
        matches!(expression.sort(), ChcSort::Array(key, element)
            if *key == self.key && *element == self.element)
    }

    fn result(&self, value: SmtValue) -> Option<SmtValue> {
        admit_value(&value, &self.element).then_some(value)
    }

    fn array(&self, expression: &ChcExpr) -> Option<SmtValue> {
        maybe_grow_expr_stack(|| {
            // Stay in the outer evaluator's model/memo scope and depth budget.
            // The growable-stack frame retains depth through recursive steps.
            ExprDepthGuard::check()?;
            if !self.matching_array(expression) {
                return None;
            }
            match expression {
                ChcExpr::ArrayLambda(lambda) => {
                    let value = lambda.instantiate((*self.index).clone())?;
                    self.result(evaluate_expr(&value, self.model)?)
                }
                ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                    if args[1].sort() != self.key || args[2].sort() != self.element {
                        return None;
                    }
                    let stored_index = evaluate_expr(&args[1], self.model)?;
                    if !admit_value(&stored_index, &self.key) {
                        return None;
                    }
                    if smt_values_equal(&stored_index, &self.index_value)? {
                        self.result(evaluate_expr(&args[2], self.model)?)
                    } else {
                        self.array(&args[0])
                    }
                }
                ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    if args[0].sort() != ChcSort::Bool
                        || !self.matching_array(&args[1])
                        || !self.matching_array(&args[2])
                    {
                        return None;
                    }
                    let SmtValue::Bool(condition) = evaluate_expr(&args[0], self.model)? else {
                        return None;
                    };
                    self.array(&args[if condition { 1 } else { 2 }])
                }
                _ => {
                    let array = evaluate_expr(expression, self.model)?;
                    self.result(eval_array_select(&array, &self.index_value)?)
                }
            }
        })
    }
}
