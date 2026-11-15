// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! First-ITE search for the ITE-before-query case split.

use super::super::super::PdrSolver;
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

/// `(cond, then_case, else_case)` of a split.
type IteSplit = (ChcExpr, ChcExpr, ChcExpr);

impl PdrSolver {
    /// Split on the first ITE occurrence anywhere in a boolean formula.
    ///
    /// Returns `(cond, then_case, else_case)` where:
    /// - `then_case` is `expr` with the first `ite(cond, t, e)` replaced by `t`
    /// - `else_case` is `expr` with the first `ite(cond, t, e)` replaced by `e`
    ///
    /// "First" is preorder over `Op` arguments. A shared sub-term is searched
    /// once: its first occurrence explores its whole subtree, so when that
    /// finds no ITE no later occurrence can hold the first one. The answer is
    /// the tree search's, in time linear in the distinct nodes; the tree
    /// search was exponential in the nesting of shared sub-terms (seconds per
    /// call on the ITE-free bist_cell transition, past the solve deadline).
    pub(in crate::pdr::solver) fn split_first_ite_anywhere(expr: &ChcExpr) -> Option<IteSplit> {
        first_ite(expr, &mut FxHashSet::default())
    }
}

/// `ite_free` holds the addresses of sub-terms already searched without an
/// ITE; they stay valid because the root is borrowed for the whole search.
fn first_ite(expr: &ChcExpr, ite_free: &mut FxHashSet<*const ChcExpr>) -> Option<IteSplit> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => Some((
            args[0].as_ref().clone(),
            args[1].as_ref().clone(),
            args[2].as_ref().clone(),
        )),
        ChcExpr::Op(op, args) => {
            for (i, arg) in args.iter().enumerate() {
                if ite_free.contains(&Arc::as_ptr(arg)) {
                    continue;
                }
                if let Some((cond, then_sub, else_sub)) = first_ite(arg, ite_free) {
                    let mut then_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                    let mut else_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                    for (j, a) in args.iter().enumerate() {
                        if i == j {
                            then_args.push(Arc::new(then_sub.clone()));
                            else_args.push(Arc::new(else_sub.clone()));
                        } else {
                            then_args.push(a.clone());
                            else_args.push(a.clone());
                        }
                    }
                    return Some((
                        cond,
                        ChcExpr::Op(*op, then_args),
                        ChcExpr::Op(*op, else_args),
                    ));
                }
                ite_free.insert(Arc::as_ptr(arg));
            }
            None
        }
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `c(0) = (x = 0)`, `c(i+1) = c(i) and (c(i) or p(i))`: one shared node
    /// per level, `2^depth` leaf occurrences in the tree.
    fn shared_boolean_chain(depth: usize, last: ChcExpr) -> ChcExpr {
        let x = ChcExpr::var(crate::ChcVar::new("x", crate::ChcSort::Int));
        let mut c = Arc::new(ChcExpr::eq(x.clone(), ChcExpr::int(0)));
        for i in 0..depth {
            let p = if i + 1 == depth {
                last.clone()
            } else {
                ChcExpr::le(x.clone(), ChcExpr::int(i as i64))
            };
            let or = Arc::new(ChcExpr::Op(ChcOp::Or, vec![Arc::clone(&c), Arc::new(p)]));
            c = Arc::new(ChcExpr::Op(ChcOp::And, vec![Arc::clone(&c), or]));
        }
        Arc::unwrap_or_clone(c)
    }

    #[test]
    #[ntest::timeout(60_000)]
    fn an_ite_free_shared_dag_is_searched_once_per_node() {
        let y = ChcExpr::var(crate::ChcVar::new("y", crate::ChcSort::Int));
        let expr = shared_boolean_chain(80, ChcExpr::ge(y, ChcExpr::int(3)));
        assert!(PdrSolver::split_first_ite_anywhere(&expr).is_none());
    }

    /// The ITE sits in the last level only, behind 2^60 tree occurrences of
    /// ITE-free sub-terms; the split replaces exactly that occurrence.
    #[test]
    #[ntest::timeout(60_000)]
    fn the_first_ite_behind_a_shared_dag_is_split_in_place() {
        let y = ChcExpr::var(crate::ChcVar::new("y", crate::ChcSort::Int));
        let cond = ChcExpr::ge(y.clone(), ChcExpr::int(3));
        let ite = ChcExpr::ite(cond.clone(), ChcExpr::int(1), ChcExpr::int(2));
        let expr = shared_boolean_chain(60, ChcExpr::eq(y.clone(), ite));

        let (found, then_case, else_case) =
            PdrSolver::split_first_ite_anywhere(&expr).expect("an ITE is present");

        assert_eq!(found, cond);
        // `==` is DAG-linear; a failing `assert_eq!` would print 2^60 nodes.
        let then_expected = shared_boolean_chain(60, ChcExpr::eq(y.clone(), ChcExpr::int(1)));
        let else_expected = shared_boolean_chain(60, ChcExpr::eq(y, ChcExpr::int(2)));
        assert!(
            then_case == then_expected,
            "then case must replace only the ITE"
        );
        assert!(
            else_case == else_expected,
            "else case must replace only the ITE"
        );
    }
}
