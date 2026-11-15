// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact case split of locals an unsigned literal bound confines to a few
//! values, for the array-free formula `read_only_arrays` produces.
//!
//! When a conjunct of a disjunct is `x <u K` (or `x <=u K - 1`) over a local
//! `x` and a literal `K` of at most [`MAX_VALUES`], then
//!
//! ```text
//! ∃x. (x <u K) ∧ φ(x)  ≡  φ(0) ∨ φ(1) ∨ … ∨ φ(K - 1)
//! ```
//!
//! because the bound admits exactly those values. A read through a pointer
//! offset `i < 2` scaled into an address (`concat(hi, lo + extract(i * 4))`)
//! leaves, after Ackermann's reduction, a local the exact projection has no
//! inverse for; each case makes the index a literal it can decide (model-checker-consumer
//! `safe_symbolic_from_elem`). The split is all-or-nothing: past
//! [`MAX_DISJUNCTS`] the formula is left as it was.

use super::{ChcExpr, ChcOp, ChcVar, FxHashSet};

/// Values one bound may enumerate.
const MAX_VALUES: u128 = 8;
/// Disjuncts the whole split may produce (the exact projection's own branch
/// budget).
const MAX_DISJUNCTS: usize = 64;

/// The formula with every bounded local of every disjunct split into its
/// cases; `None` when there is none or the split would pass the budget.
pub(super) fn split(formula: &ChcExpr, keep: &[ChcVar]) -> Option<ChcExpr> {
    let keep: FxHashSet<&str> = keep.iter().map(|var| var.name.as_str()).collect();
    let mut done: Vec<ChcExpr> = Vec::new();
    let mut pending: Vec<ChcExpr> = disjuncts(formula);
    let mut split_any = false;
    while let Some(disjunct) = pending.pop() {
        if done.len() + pending.len() >= MAX_DISJUNCTS {
            return None;
        }
        let Some((local, width, count)) = bounded_local(&disjunct, &keep) else {
            done.push(disjunct);
            continue;
        };
        split_any = true;
        for value in 0..count {
            let case = disjunct
                .substitute(&[(local.clone(), ChcExpr::BitVec(value, width))])
                .simplify_constants();
            if !matches!(case, ChcExpr::Bool(false)) {
                pending.extend(disjuncts(&case));
            }
        }
    }
    split_any.then(|| ChcExpr::or_all(done))
}

fn disjuncts(formula: &ChcExpr) -> Vec<ChcExpr> {
    match formula {
        ChcExpr::Op(ChcOp::Or, args) => args.iter().map(|arg| arg.as_ref().clone()).collect(),
        other => vec![other.clone()],
    }
}

/// The first conjunct `x <u K` / `x <=u K` over a local `x` with at most
/// [`MAX_VALUES`] values: `(x, width, value count)`.
fn bounded_local(disjunct: &ChcExpr, keep: &FxHashSet<&str>) -> Option<(ChcVar, u32, u128)> {
    disjunct
        .collect_conjuncts()
        .into_iter()
        .find_map(|conjunct| {
            let ChcExpr::Op(operation @ (ChcOp::BvULt | ChcOp::BvULe), args) = &conjunct else {
                return None;
            };
            let [lhs, rhs] = args.as_slice() else {
                return None;
            };
            let (ChcExpr::Var(local), ChcExpr::BitVec(bound, width)) = (lhs.as_ref(), rhs.as_ref())
            else {
                return None;
            };
            if keep.contains(local.name.as_str()) {
                return None;
            }
            let count = match operation {
                ChcOp::BvULt => Some(*bound),
                _ => bound.checked_add(1),
            }?;
            (count <= MAX_VALUES).then(|| (local.clone(), *width, count))
        })
}

#[cfg(test)]
mod tests;
