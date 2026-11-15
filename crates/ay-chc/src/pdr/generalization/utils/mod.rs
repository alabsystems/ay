// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure utility functions for generalization.
//!
//! These functions don't depend on PdrSolver state and can be used
//! by any code that needs to manipulate formula conjuncts.

use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashSet as FxHashSet;
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

/// Extract the disequalities `(not (= a b))` under the `and`/`or` spine of
/// an expression, in tree (depth-first) order and with tree multiplicity,
/// stopping once `cap` are collected.
///
/// Returns Vec<(lhs, rhs)> for each disequality found (at most `cap`).
///
/// The cap and the memo of diseq-free subtrees bound the walk on DAGs: the
/// expression is a DAG (substituted frames and `let`-expanded transitions
/// share subterms), and the uncapped tree walk expanded a shared `and`/`or`
/// spine into one pushed pair per tree occurrence — measured on toy-bug-1
/// (LRA-Lin) as two PDR lanes growing a `Vec` past 4 GiB each. Callers only
/// look at the first few pairs or refuse beyond a count, so up to `cap` the
/// result is exactly the tree walk's.
pub(in crate::pdr) fn extract_disequalities(expr: &ChcExpr, cap: usize) -> Vec<(ChcExpr, ChcExpr)> {
    let mut diseqs = Vec::new();
    let mut barren: FxHashSet<*const ChcExpr> = FxHashSet::default();
    extract_disequalities_rec(expr, cap, &mut diseqs, &mut barren);
    diseqs
}

/// Recursive step of [`extract_disequalities`]. `barren` holds the spine
/// nodes (by address; the root is borrowed for the whole walk) already known
/// to contain no disequality, so a shared subtree without one is walked once.
fn extract_disequalities_rec(
    expr: &ChcExpr,
    cap: usize,
    result: &mut Vec<(ChcExpr, ChcExpr)>,
    barren: &mut FxHashSet<*const ChcExpr>,
) {
    if result.len() >= cap {
        return;
    }
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                if eq_args.len() == 2 {
                    result.push(((*eq_args[0]).clone(), (*eq_args[1]).clone()));
                }
            }
        }
        ChcExpr::Op(ChcOp::And | ChcOp::Or, args) => {
            let key: *const ChcExpr = expr;
            if barren.contains(&key) {
                return;
            }
            let before = result.len();
            for arg in args {
                if result.len() >= cap {
                    return;
                }
                extract_disequalities_rec(arg, cap, result, barren);
            }
            if result.len() == before {
                barren.insert(key);
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
