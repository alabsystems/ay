// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality collection for model augmentation during cube extraction.

use crate::{ChcExpr, ChcOp};
use std::sync::Arc;

/// Collect equalities from an expression into a list of (lhs, rhs) pairs.
///
/// A large tree (a shared DAG: the tree walk below is exponential in the
/// nesting of shared sub-terms, past the solve deadline inside cube
/// extraction) is walked once per distinct sub-term instead, in the same
/// preorder: only repeated pairs from repeated sub-terms are left out.
pub(super) fn collect_equalities(expr: &ChcExpr, out: &mut Vec<(Arc<ChcExpr>, Arc<ChcExpr>)>) {
    if crate::expr::dag::tree_size_at_least(expr, crate::expr::dag::DAG_WALK_MIN_TREE) {
        collect_distinct_equalities(expr, out);
        return;
    }
    collect_equalities_tree(expr, out);
}

/// [`collect_equalities`] over the distinct sub-terms of `expr`, descending
/// exactly where the tree walk does.
fn collect_distinct_equalities(expr: &ChcExpr, out: &mut Vec<(Arc<ChcExpr>, Arc<ChcExpr>)>) {
    let mut walked: ay_core::kani_compat::DetHashSet<*const ChcExpr> = Default::default();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !walked.insert(std::ptr::from_ref(node)) {
            continue;
        }
        let children: &[Arc<ChcExpr>] = match node {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                out.push((args[0].clone(), args[1].clone()));
                &[]
            }
            ChcExpr::Op(ChcOp::Not, args) => &args[..args.len().min(1)],
            ChcExpr::Op(ChcOp::Implies | ChcOp::Iff, args) => &args[..args.len().min(2)],
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args,
            _ => &[],
        };
        stack.extend(children.iter().rev().map(AsRef::as_ref));
    }
}

fn collect_equalities_tree(expr: &ChcExpr, out: &mut Vec<(Arc<ChcExpr>, Arc<ChcExpr>)>) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::ArrayLambda(_) => {}
        ChcExpr::Op(ChcOp::And | ChcOp::Or, args) => {
            for a in args {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Not, args) => {
            if let Some(a) = args.first() {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Implies | ChcOp::Iff, args) => {
            if let Some(a) = args.first() {
                collect_equalities_tree(a, out);
            }
            if let Some(b) = args.get(1) {
                collect_equalities_tree(b, out);
            }
        }
        ChcExpr::Op(ChcOp::Ite, args) => {
            for a in args {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            out.push((args[0].clone(), args[1].clone()));
        }
        ChcExpr::Op(_, args) => {
            for a in args {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::PredicateApp(_, _, args) => {
            for a in args {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::FuncApp(_, _, args) => {
            for a in args {
                collect_equalities_tree(a, out);
            }
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => {}
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcSort, ChcVar};

    fn x() -> ChcExpr {
        ChcExpr::var(ChcVar::new("x", ChcSort::Int))
    }

    /// `c(0) = (x = 1)`, `c(i+1) = (c(i) and x <= i) or (c(i) and x >= -i)`.
    fn shared_chain(depth: i64) -> ChcExpr {
        let mut c = Arc::new(ChcExpr::eq(x(), ChcExpr::int(1)));
        for i in 0..depth {
            let left = ChcExpr::Op(
                ChcOp::And,
                vec![Arc::clone(&c), Arc::new(ChcExpr::le(x(), ChcExpr::int(i)))],
            );
            let right = ChcExpr::Op(
                ChcOp::And,
                vec![Arc::clone(&c), Arc::new(ChcExpr::ge(x(), ChcExpr::int(-i)))],
            );
            c = Arc::new(ChcExpr::Op(
                ChcOp::Or,
                vec![Arc::new(left), Arc::new(right)],
            ));
        }
        Arc::unwrap_or_clone(c)
    }

    /// A `2^60`-copy DAG: the one `(= x 1)` node is collected once.
    #[test]
    #[ntest::timeout(60_000)]
    fn a_large_shared_dag_yields_each_equality_node_once() {
        let mut out = Vec::new();
        collect_equalities(&shared_chain(60), &mut out);
        assert_eq!(out.len(), 1);
        assert_eq!(*out[0].0, x());
        assert_eq!(*out[0].1, ChcExpr::int(1));
    }

    /// Negative twin: below the DAG threshold the tree walk still runs, so a
    /// small expression keeps its repeated pairs exactly as before.
    #[test]
    fn a_small_expression_keeps_the_tree_walks_repeats() {
        let mut out = Vec::new();
        collect_equalities(&shared_chain(3), &mut out);
        assert_eq!(out.len(), 8, "2^3 tree copies of `(= x 1)`");
    }
}
