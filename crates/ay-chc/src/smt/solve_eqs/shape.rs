// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape tests of [`super::solve_eqs`]: which right-hand sides may replace a
//! variable, and the rejoining of equalities that callers split in two.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::MAX_DEF_RHS_NODES;
use crate::{ChcExpr, ChcOp, ChcSort};

/// Rejoin conjunct pairs `a <= b`, `b <= a` into `a = b` when one side is a
/// variable and both are small scalar terms. Interpolation callers split every
/// top-level equality into two inequalities before handing constraints over
/// (`collect_conjuncts_for_interpolation`), which would hide the definitions
/// from this pass. Returns the number of pairs rejoined.
pub(super) fn rejoin_equality_pairs(conjuncts: &mut Vec<Arc<ChcExpr>>) -> usize {
    let mut open: FxHashMap<(ChcExpr, ChcExpr), usize> = FxHashMap::default();
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for (i, c) in conjuncts.iter().enumerate() {
        let ChcExpr::Op(ChcOp::Le, args) = c.as_ref() else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (l, r) = (args[0].as_ref(), args[1].as_ref());
        if !matches!(l, ChcExpr::Var(_)) && !matches!(r, ChcExpr::Var(_)) {
            continue;
        }
        if !small_scalar_term(l, MAX_DEF_RHS_NODES) || !small_scalar_term(r, MAX_DEF_RHS_NODES) {
            continue;
        }
        match open.remove(&(r.clone(), l.clone())) {
            Some(j) => pairs.push((j, i)),
            None => {
                open.entry((l.clone(), r.clone())).or_insert(i);
            }
        }
    }
    let mut dropped: FxHashSet<usize> = FxHashSet::default();
    for &(j, i) in &pairs {
        let joined = match conjuncts[j].as_ref() {
            ChcExpr::Op(_, args) => Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::clone(&args[0]), Arc::clone(&args[1])],
            )),
            _ => continue,
        };
        conjuncts[j] = joined;
        dropped.insert(i);
    }
    let mut index = 0usize;
    conjuncts.retain(|_| {
        let keep = !dropped.contains(&index);
        index += 1;
        keep
    });
    pairs.len()
}

/// A right-hand side that may replace a variable of `sort`: a constant or a
/// variable of that sort, or a compound term of that sort with at most
/// [`MAX_DEF_RHS_NODES`] distinct nodes.
pub(super) fn is_substitutable(t: &ChcExpr, sort: &ChcSort) -> bool {
    match t {
        ChcExpr::Bool(_) => *sort == ChcSort::Bool,
        ChcExpr::Int(_) => *sort == ChcSort::Int,
        ChcExpr::Real(_, d) => *sort == ChcSort::Real && *d != 0,
        ChcExpr::Var(v) => v.sort == *sort,
        ChcExpr::Op(..) => small_scalar_term(t, MAX_DEF_RHS_NODES) && t.sort() == *sort,
        _ => false,
    }
}

/// A right-hand side of any size for a variable of `sort`: built only from
/// Bool/Int/Real constants and variables and the linear/Boolean operators.
pub(super) fn is_scalar_term(t: &ChcExpr, sort: &ChcSort) -> bool {
    small_scalar_term(t, usize::MAX) && t.sort() == *sort
}

/// `true` when `t` has at most `limit` distinct nodes and consists only of
/// Bool/Int/Real constants, variables of those sorts and linear-arithmetic /
/// Boolean operators.
fn small_scalar_term(t: &ChcExpr, limit: usize) -> bool {
    let mut seen: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![t];
    let mut count = 0usize;
    while let Some(e) = stack.pop() {
        count += 1;
        if count > limit {
            return false;
        }
        match e {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(..) => {}
            ChcExpr::Var(v) => {
                if !matches!(v.sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real) {
                    return false;
                }
            }
            ChcExpr::Op(op, args) => {
                if !is_scalar_op(*op) {
                    return false;
                }
                for a in args {
                    if seen.insert(Arc::as_ptr(a)) {
                        stack.push(a.as_ref());
                    }
                }
            }
            _ => return false,
        }
    }
    true
}

fn is_scalar_op(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Sub
            | ChcOp::Mul
            | ChcOp::Neg
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::Ite
    )
}
