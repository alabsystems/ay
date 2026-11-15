// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `eliminate_ite` on shared DAGs (WP-F F0c).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::eliminate::EliminationState;
use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, MAX_EXPR_RECURSION_DEPTH};

/// Tree size from which [`ChcExpr::eliminate_ite`] rewrites the shared DAG
/// instead of the tree. Below it the historical per-path rewrite runs unchanged.
const ITE_DAG_REWRITE_MIN_TREE: usize = 65_536;

impl ChcExpr {
    /// Eliminate arithmetic ite expressions by introducing auxiliary variables and constraints.
    ///
    /// The CHC SMT backend ultimately relies on the LIA solver, which only supports linear
    /// integer/real arithmetic terms. Arithmetic-valued ite terms (e.g. `(ite c 1 0)`) create
    /// non-linear theory atoms like `(= x (ite ...))`, which can force the backend to return
    /// `unknown`. This pass rewrites arithmetic ite expressions into a fresh variable `v` with:
    /// - (=> c (= v t))
    /// - (=> (not c) (= v e))
    ///
    /// Boolean-valued ite expressions are left intact.
    /// If the expression exceeds 1M nodes, returns `self` unchanged (#2774).
    ///
    /// Shared DAGs: when the tree expansion has at least
    /// [`ITE_DAG_REWRITE_MIN_TREE`] nodes the rewrite runs once per DISTINCT
    /// node ([`Self::eliminate_ite_dag`]), and the 1M-node budget then bounds
    /// distinct nodes. A shared arithmetic `ite` reached along several paths
    /// gets ONE fresh variable instead of one per path; each fresh variable is
    /// defined by the same `cond → v = then`, `¬cond → v = else` pair, so the
    /// result is equisatisfiable with, and has the same models over the
    /// original variables as, the per-path rewrite.
    pub(crate) fn eliminate_ite(&self) -> Self {
        if self.node_count(ITE_DAG_REWRITE_MIN_TREE) >= ITE_DAG_REWRITE_MIN_TREE
            && !super::dag::longest_path_at_least(
                self,
                MAX_EXPR_RECURSION_DEPTH.saturating_sub(super::current_expr_depth() + 2),
            )
        {
            return self.eliminate_ite_dag();
        }
        self.eliminate_ite_tree()
    }

    /// [`Self::eliminate_ite`] over distinct nodes (WP-F F0c): each shared
    /// `Arc` is rewritten once and its result reused; an unchanged subtree is
    /// returned as the SAME `Arc`, so the output keeps the input's sharing.
    /// Callers guarantee no path is deep enough for `ExprDepthGuard` to trip,
    /// so the result is the per-path rewrite modulo fresh-variable sharing.
    pub(super) fn eliminate_ite_dag(&self) -> Self {
        let mut state = EliminationState::new();
        let mut memo: FxHashMap<*const ChcExpr, Arc<ChcExpr>> = FxHashMap::default();
        let root = Arc::new(self.clone());
        let Some(transformed) = Self::eliminate_ite_dag_node(&root, &mut state, &mut memo) else {
            return self.clone();
        };
        let transformed = Arc::unwrap_or_clone(transformed);
        if state.constraints.is_empty() {
            transformed
        } else {
            let mut all_conjuncts = state.constraints;
            all_conjuncts.push(transformed);
            Self::and_vec(all_conjuncts)
        }
    }

    fn eliminate_ite_dag_node(
        node: &Arc<ChcExpr>,
        state: &mut EliminationState,
        memo: &mut FxHashMap<*const ChcExpr, Arc<ChcExpr>>,
    ) -> Option<Arc<ChcExpr>> {
        let children = super::dag::children(node);
        if children.is_empty() {
            return Some(Arc::clone(node));
        }
        let key = Arc::as_ptr(node);
        if let Some(done) = memo.get(&key) {
            return Some(Arc::clone(done));
        }
        if !state.tick() {
            return None;
        }
        let result = maybe_grow_expr_stack(|| {
            let mut rewrite = |child: &Arc<ChcExpr>| {
                Self::eliminate_ite_dag_node(child, state, memo)
                    .unwrap_or_else(|| Arc::clone(child))
            };
            match node.as_ref() {
                Self::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    let cond = rewrite(&args[0]);
                    let then_ = rewrite(&args[1]);
                    let else_ = rewrite(&args[2]);
                    let then_sort = then_.sort();
                    let else_sort = else_.sort();
                    if then_sort == else_sort && matches!(then_sort, ChcSort::Int | ChcSort::Real) {
                        let v = state.fresh_var("_ite", then_sort);
                        let v_expr = Self::Var(v);
                        let cond = Arc::unwrap_or_clone(cond);
                        let eq_then = Self::eq(v_expr.clone(), Arc::unwrap_or_clone(then_));
                        let eq_else = Self::eq(v_expr.clone(), Arc::unwrap_or_clone(else_));
                        state.constraints.push(Self::implies(cond.clone(), eq_then));
                        state
                            .constraints
                            .push(Self::implies(Self::not(cond), eq_else));
                        return Arc::new(v_expr);
                    }
                    if Arc::ptr_eq(&cond, &args[0])
                        && Arc::ptr_eq(&then_, &args[1])
                        && Arc::ptr_eq(&else_, &args[2])
                    {
                        Arc::clone(node)
                    } else {
                        Arc::new(Self::Op(ChcOp::Ite, vec![cond, then_, else_]))
                    }
                }
                other => {
                    let old = super::dag::children(other);
                    let new: Vec<Arc<ChcExpr>> = old.iter().map(&mut rewrite).collect();
                    if old.iter().zip(&new).all(|(a, b)| Arc::ptr_eq(a, b)) {
                        return Arc::clone(node);
                    }
                    match (other, new.as_slice()) {
                        (Self::Op(op, _), _) => Arc::new(Self::Op(*op, new)),
                        (Self::PredicateApp(name, id, _), _) => {
                            Arc::new(Self::PredicateApp(name.clone(), *id, new))
                        }
                        (Self::FuncApp(name, sort, _), _) => {
                            Arc::new(Self::FuncApp(name.clone(), sort.clone(), new))
                        }
                        (Self::ConstArray(sort, _), [value]) => {
                            Arc::new(Self::ConstArray(sort.clone(), Arc::clone(value)))
                        }
                        (Self::ArrayLambda(lambda), _) => {
                            Arc::new(Self::ArrayLambda(lambda.with_captures(new)))
                        }
                        // Leaves never reach here (no children to rebuild).
                        _ => Arc::clone(node),
                    }
                }
            }
        });
        memo.insert(key, Arc::clone(&result));
        Some(result)
    }
}
