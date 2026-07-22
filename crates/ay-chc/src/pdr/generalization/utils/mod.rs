// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure utility functions for generalization.
//!
//! These functions don't depend on PdrSolver state and can be used
//! by any code that needs to manipulate formula conjuncts.

use crate::{ChcExpr, ChcOp};
use std::sync::Arc;

/// Build a conjunction from a list of formulas.
///
/// - Empty list returns `true`
/// - Single element returns that element
/// - Multiple elements returns nested AND
pub(in crate::pdr) fn build_conjunction(conjuncts: &[ChcExpr]) -> ChcExpr {
    if conjuncts.is_empty() {
        ChcExpr::Bool(true)
    } else if conjuncts.len() == 1 {
        conjuncts[0].clone()
    } else {
        let mut result = conjuncts[0].clone();
        for conjunct in conjuncts.iter().skip(1) {
            result = ChcExpr::Op(
                ChcOp::And,
                vec![Arc::new(result), Arc::new(conjunct.clone())],
            );
        }
        result
    }
}

/// Collect all branches from an OR expression (handles nested ORs).
pub(in crate::pdr) fn collect_or_branches(args: &[Arc<ChcExpr>], result: &mut Vec<ChcExpr>) {
    crate::expr::maybe_grow_expr_stack(|| {
        for arg in args {
            match arg.as_ref() {
                ChcExpr::Op(ChcOp::Or, nested_args) => {
                    collect_or_branches(nested_args, result);
                }
                _ => {
                    result.push(arg.as_ref().clone());
                }
            }
        }
    });
}

/// Extract all disequalities `(not (= a b))` from an expression.
///
/// Returns Vec<(lhs, rhs)> for each disequality found.
pub(in crate::pdr) fn extract_disequalities(expr: &ChcExpr) -> Vec<(ChcExpr, ChcExpr)> {
    let mut diseqs = Vec::new();
    extract_disequalities_rec(expr, &mut diseqs);
    diseqs
}

/// Recursively extract disequalities from an expression.
pub(in crate::pdr) fn extract_disequalities_rec(
    expr: &ChcExpr,
    result: &mut Vec<(ChcExpr, ChcExpr)>,
) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                if eq_args.len() == 2 {
                    result.push(((*eq_args[0]).clone(), (*eq_args[1]).clone()));
                }
            }
        }
        ChcExpr::Op(ChcOp::And | ChcOp::Or, args) => {
            for arg in args {
                extract_disequalities_rec(arg, result);
            }
        }
        _ => {}
    });
}

use crate::ChcVar;

/// Extract a variable and constant from an equality conjunct (v = c).
///
/// Handles:
/// - `(= var const)` → Some((var, const))
/// - `(= const var)` → Some((var, const))
/// - other expressions → None
pub(in crate::pdr) fn extract_equality(expr: &ChcExpr) -> Option<(ChcVar, i128)> {
    expr.extract_var_int_equality()
}

/// Extract a variable and constant from an equality or negated distinct.
///
/// This is useful when interpolation produces `(distinct var k)` and we need
/// `NOT(distinct var k)` which is semantically equivalent to `(= var k)`.
///
/// Handles:
/// - `(= var const)` → Some((var, const))
/// - `(not (distinct var const))` → Some((var, const))
/// - other expressions → None
pub(in crate::pdr) fn extract_equality_or_not_distinct(expr: &ChcExpr) -> Option<(ChcVar, i128)> {
    // Try direct equality first: (= var const)
    if let Some(eq) = extract_equality(expr) {
        return Some(eq);
    }

    // Try (not (ne var const)) = (= var const)
    // Note: "distinct" in SMT-LIB is represented as ChcOp::Ne internally
    if let ChcExpr::Op(ChcOp::Not, args) = expr {
        if args.len() == 1 {
            if let ChcExpr::Op(ChcOp::Ne, distinct_args) = args[0].as_ref() {
                if distinct_args.len() == 2 {
                    match (distinct_args[0].as_ref(), distinct_args[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) => return Some((v.clone(), *n)),
                        (ChcExpr::Int(n), ChcExpr::Var(v)) => return Some((v.clone(), *n)),
                        _ => {}
                    }
                }
            }
        }
    }

    None
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
