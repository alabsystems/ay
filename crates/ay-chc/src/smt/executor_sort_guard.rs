// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort preflight for CHC expressions serialized to SMT-LIB executor paths.

use crate::{ChcExpr, ChcOp, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

fn is_numeric_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Int | ChcSort::Real)
}

fn all_same_sort(args: &[Arc<ChcExpr>]) -> bool {
    let Some(first) = args.first().map(|arg| arg.sort()) else {
        return false;
    };
    args.iter().skip(1).all(|arg| arg.sort() == first)
}

fn all_bool_args(args: &[Arc<ChcExpr>]) -> bool {
    args.iter().all(|arg| matches!(arg.sort(), ChcSort::Bool))
}

fn all_same_numeric_sort(args: &[Arc<ChcExpr>]) -> bool {
    let Some(first) = args.first().map(|arg| arg.sort()) else {
        return false;
    };
    is_numeric_sort(&first) && args.iter().skip(1).all(|arg| arg.sort() == first)
}

fn all_bv_args(args: &[Arc<ChcExpr>]) -> bool {
    args.iter()
        .all(|arg| matches!(arg.sort(), ChcSort::BitVec(_)))
}

fn same_width_bv_binary_args(args: &[Arc<ChcExpr>]) -> bool {
    if args.len() != 2 {
        return false;
    }
    matches!(
        (args[0].sort(), args[1].sort()),
        (ChcSort::BitVec(a), ChcSort::BitVec(b)) if a == b
    )
}

/// Return a reason when serializing `expr` would feed an ill-sorted SMT-LIB
/// term to the executor frontend.
///
/// The frontend elaborator calls typed ay-core builders while parsing the
/// generated SMT-LIB. CHC transforms can create expressions that are valid as
/// conservative internal abstractions but unsupported by that serialization
/// boundary, e.g. arithmetic `<` over BV terms or same-BV-op operands with
/// different widths. Those cases should become `Unknown`, not a frontend panic.
///
/// The answer is the first failing node in post-order — a function of each
/// subtree — so on large inputs it is memoised per distinct node (WP-F F0b).
pub(crate) fn unsupported_executor_expr_reason(expr: &ChcExpr) -> Option<&'static str> {
    if semantic_tree_size_at_least(expr, crate::expr::dag::DAG_WALK_MIN_TREE) {
        let mut memo = FxHashMap::default();
        return reason_memo(expr, &mut memo);
    }
    reason_plain(expr)
}

/// Include closed lambda code in the plain-walk/memo threshold. A small
/// capture environment must not hide an exponentially shared body from it.
fn semantic_tree_size_at_least(root: &ChcExpr, limit: usize) -> bool {
    let mut stack = vec![root];
    let mut visited = 0usize;
    while let Some(expr) = stack.pop() {
        visited = visited.saturating_add(1);
        let children = crate::expr::dag::children(expr);
        let body = match expr {
            ChcExpr::ArrayLambda(lambda) => Some(lambda.body().as_ref()),
            _ => None,
        };
        // Each queued child costs at least one visit. Stop before allocating
        // a pending stack wider than the threshold.
        if visited
            .saturating_add(stack.len())
            .saturating_add(children.len())
            .saturating_add(usize::from(body.is_some()))
            >= limit
        {
            return true;
        }
        stack.extend(children.iter().map(AsRef::as_ref));
        stack.extend(body);
    }
    false
}

type ReasonMemo = FxHashMap<*const ChcExpr, Option<&'static str>>;

fn reason_plain(expr: &ChcExpr) -> Option<&'static str> {
    crate::expr::maybe_grow_expr_stack(|| reason_node(expr, &mut |child| reason_plain(child)))
}

fn reason_memo(expr: &ChcExpr, memo: &mut ReasonMemo) -> Option<&'static str> {
    if crate::expr::dag::children(expr).is_empty() && !matches!(expr, ChcExpr::ArrayLambda(_)) {
        return reason_node(expr, &mut |_| None);
    }
    let key = std::ptr::from_ref::<ChcExpr>(expr);
    if let Some(known) = memo.get(&key) {
        return *known;
    }
    let reason = crate::expr::maybe_grow_expr_stack(|| {
        reason_node(expr, &mut |child| reason_memo(child, memo))
    });
    memo.insert(key, reason);
    reason
}

/// One node's verdict given how to judge its children (`recurse`): the first
/// failing child's reason, else this node's own sort check.
fn reason_node(
    expr: &ChcExpr,
    recurse: &mut dyn FnMut(&ChcExpr) -> Option<&'static str>,
) -> Option<&'static str> {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => None,
        ChcExpr::Var(_) => None,
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().find_map(|arg| recurse(arg))
        }
        ChcExpr::ConstArray(_, value) => recurse(value),
        ChcExpr::ArrayLambda(lambda) => {
            if !lambda.captures_are_well_typed() {
                return Some("array lambda has mismatched capture sorts");
            }
            recurse(lambda.body())
                .or_else(|| lambda.captures().iter().find_map(|value| recurse(value)))
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => {
            Some("internal marker expression is not a standalone SMT-LIB term")
        }
        ChcExpr::Op(op, args) => {
            if let Some(reason) = args.iter().find_map(|arg| recurse(arg)) {
                return Some(reason);
            }

            match op {
                ChcOp::Not => (args.len() == 1 && all_bool_args(args))
                    .then_some(())
                    .map_or(Some("Boolean negation has a non-Bool operand"), |()| None),
                ChcOp::And | ChcOp::Or => all_bool_args(args)
                    .then_some(())
                    .map_or(Some("Boolean connective has a non-Bool operand"), |()| None),
                ChcOp::Implies | ChcOp::Iff => (args.len() == 2 && all_bool_args(args))
                    .then_some(())
                    .map_or(
                        Some("Boolean binary connective has non-Bool operands"),
                        |()| None,
                    ),
                ChcOp::Add | ChcOp::Mul => (args.len() >= 2 && all_same_numeric_sort(args))
                    .then_some(())
                    .map_or(
                        Some("arithmetic operation has non-numeric operands"),
                        |()| None,
                    ),
                ChcOp::Sub => (!args.is_empty() && all_same_numeric_sort(args))
                    .then_some(())
                    .map_or(Some("subtraction has non-numeric operands"), |()| None),
                ChcOp::Div | ChcOp::Mod => {
                    if args.len() == 2 && args.iter().all(|arg| matches!(arg.sort(), ChcSort::Int))
                    {
                        None
                    } else {
                        Some("integer division/modulo has non-Int operands")
                    }
                }
                ChcOp::Neg => (args.len() == 1 && all_same_numeric_sort(args))
                    .then_some(())
                    .map_or(
                        Some("arithmetic negation has a non-numeric operand"),
                        |()| None,
                    ),
                ChcOp::Eq | ChcOp::Ne => (args.len() >= 2 && all_same_sort(args))
                    .then_some(())
                    .map_or(Some("equality has mismatched operand sorts"), |()| None),
                ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => (args.len() == 2
                    && all_same_numeric_sort(args))
                .then_some(())
                .map_or(
                    Some("arithmetic comparison has non-numeric operands"),
                    |()| None,
                ),
                ChcOp::Ite => {
                    if args.len() == 3
                        && matches!(args[0].sort(), ChcSort::Bool)
                        && args[1].sort() == args[2].sort()
                    {
                        None
                    } else {
                        Some("ite has non-Bool condition or mismatched branch sorts")
                    }
                }
                ChcOp::Select => {
                    if args.len() != 2 {
                        return Some("select has invalid arity");
                    }
                    match args[0].sort() {
                        ChcSort::Array(key_sort, _) if *key_sort == args[1].sort() => None,
                        ChcSort::Array(_, _) => Some("select index sort does not match array"),
                        _ => Some("select target is not an array"),
                    }
                }
                ChcOp::Store => {
                    if args.len() != 3 {
                        return Some("store has invalid arity");
                    }
                    match args[0].sort() {
                        ChcSort::Array(key_sort, value_sort)
                            if *key_sort == args[1].sort() && *value_sort == args[2].sort() =>
                        {
                            None
                        }
                        ChcSort::Array(_, _) => Some("store index/value sort does not match array"),
                        _ => Some("store target is not an array"),
                    }
                }
                ChcOp::BvAdd
                | ChcOp::BvSub
                | ChcOp::BvMul
                | ChcOp::BvUDiv
                | ChcOp::BvURem
                | ChcOp::BvSDiv
                | ChcOp::BvSRem
                | ChcOp::BvSMod
                | ChcOp::BvAnd
                | ChcOp::BvOr
                | ChcOp::BvXor
                | ChcOp::BvNand
                | ChcOp::BvNor
                | ChcOp::BvXnor
                | ChcOp::BvShl
                | ChcOp::BvLShr
                | ChcOp::BvAShr
                | ChcOp::BvULt
                | ChcOp::BvULe
                | ChcOp::BvUGt
                | ChcOp::BvUGe
                | ChcOp::BvSLt
                | ChcOp::BvSLe
                | ChcOp::BvSGt
                | ChcOp::BvSGe
                | ChcOp::BvComp => same_width_bv_binary_args(args).then_some(()).map_or(
                    Some("BV binary operation has mismatched operand widths"),
                    |()| None,
                ),
                ChcOp::BvConcat => (args.len() == 2 && all_bv_args(args))
                    .then_some(())
                    .map_or(Some("concat has non-BV operands"), |()| None),
                ChcOp::BvNot | ChcOp::BvNeg | ChcOp::Bv2Nat => (args.len() == 1
                    && all_bv_args(args))
                .then_some(())
                .map_or(Some("unary BV operation has a non-BV operand"), |()| None),
                ChcOp::BvExtract(hi, lo) => (args.len() == 1 && hi >= lo && all_bv_args(args))
                    .then_some(())
                    .map_or(Some("extract has malformed BV operands"), |()| None),
                ChcOp::BvZeroExtend(_)
                | ChcOp::BvSignExtend(_)
                | ChcOp::BvRotateLeft(_)
                | ChcOp::BvRotateRight(_)
                | ChcOp::BvRepeat(_) => (args.len() == 1 && all_bv_args(args))
                    .then_some(())
                    .map_or(Some("indexed BV operation has a non-BV operand"), |()| None),
                ChcOp::Int2Bv(_) => (args.len() == 1 && matches!(args[0].sort(), ChcSort::Int))
                    .then_some(())
                    .map_or(Some("int2bv has a non-Int operand"), |()| None),
            }
        }
    }
}
