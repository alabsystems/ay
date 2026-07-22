// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression normalization passes (negation rewriting, strict comparison elimination).

use std::sync::Arc;

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, MAX_EXPR_RECURSION_DEPTH,
    MAX_PREPROCESSING_NODES,
};

impl ChcExpr {
    /// Normalize negations by rewriting `not` applied to comparisons into equivalent operators.
    ///
    /// This keeps formulas in a form that the CHC SMT backend can treat as theory atoms, avoiding
    /// expensive DPLL(T) splitting on Boolean structure like `(not (<= ...))`.
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2771).
    /// Unnormalized negations are still semantically correct, just less efficient.
    pub(crate) fn normalize_negations(&self) -> Self {
        use std::cell::Cell;

        /// Budget for normalize_negations traversal (#2771).
        const MAX_NORMALIZE_NODES: usize = 1_000_000;

        let budget = Cell::new(MAX_NORMALIZE_NODES);

        fn normalize_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                        let inner = normalize_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        match inner {
                            ChcExpr::Bool(b) => ChcExpr::Bool(!b),
                            ChcExpr::Op(ChcOp::Not, ref inner_args) if inner_args.len() == 1 => {
                                normalize_inner(&inner_args[0], budget, depth + 1)
                                    .unwrap_or_else(|| inner_args[0].as_ref().clone())
                            }
                            ChcExpr::Op(ChcOp::And, ref inner_args) => {
                                // De Morgan: NOT(AND(a,b,...)) → OR(NOT(a), NOT(b), ...)
                                // Distributing NOT here avoids mk_not's De Morgan in the
                                // TermStore, which creates complex boolean structure that
                                // triggers incorrect UNSAT in the SAT solver (#5376).
                                let children: Vec<ChcExpr> = inner_args
                                    .iter()
                                    .map(|child| {
                                        let not_child = ChcExpr::not(child.as_ref().clone());
                                        normalize_inner(&not_child, budget, depth + 1)
                                            .unwrap_or(not_child)
                                    })
                                    .collect();
                                ChcExpr::or_vec(children)
                            }
                            ChcExpr::Op(ChcOp::Or, ref inner_args) => {
                                // De Morgan: NOT(OR(a,b,...)) → AND(NOT(a), NOT(b), ...)
                                let children: Vec<ChcExpr> = inner_args
                                    .iter()
                                    .map(|child| {
                                        let not_child = ChcExpr::not(child.as_ref().clone());
                                        normalize_inner(&not_child, budget, depth + 1)
                                            .unwrap_or(not_child)
                                    })
                                    .collect();
                                ChcExpr::and_vec(children)
                            }
                            ChcExpr::Op(op, ref inner_args) if inner_args.len() == 2 => {
                                let a = inner_args[0].as_ref().clone();
                                let b = inner_args[1].as_ref().clone();
                                match op {
                                    ChcOp::Eq | ChcOp::Iff => ChcExpr::ne(a, b),
                                    ChcOp::Ne => ChcExpr::eq(a, b),
                                    ChcOp::Lt => ChcExpr::ge(a, b),
                                    ChcOp::Le => ChcExpr::gt(a, b),
                                    ChcOp::Gt => ChcExpr::le(a, b),
                                    ChcOp::Ge => ChcExpr::lt(a, b),
                                    _ => {
                                        // Skip rebuild when inner is unchanged (#3665)
                                        if args[0].as_ref() == &ChcExpr::Op(op, inner_args.clone())
                                        {
                                            expr.clone()
                                        } else {
                                            ChcExpr::not(ChcExpr::Op(op, inner_args.clone()))
                                        }
                                    }
                                }
                            }
                            ref other if args[0].as_ref() == other => {
                                // Inner unchanged, skip rebuild (#3665)
                                expr.clone()
                            }
                            other => ChcExpr::not(other),
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        normalize_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        normalize_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }

    /// Rewrite strict integer comparisons with constant bounds into equivalent non-strict forms.
    ///
    /// For Ints:
    /// - `x < c`  <=>  `x <= c-1`
    /// - `x > c`  <=>  `x >= c+1`
    /// - `c < x`  <=>  `x >= c+1`
    /// - `c > x`  <=>  `x <= c-1`
    pub(crate) fn normalize_strict_int_comparisons(&self) -> Self {
        use std::cell::Cell;

        let budget = Cell::new(MAX_PREPROCESSING_NODES);

        fn normalize_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Op(op, args) if args.len() == 2 => {
                        let a = normalize_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let b = normalize_inner(&args[1], budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());

                        let is_int = |e: &ChcExpr| matches!(e.sort(), ChcSort::Int);

                        match op {
                            ChcOp::Lt if is_int(&a) && is_int(&b) => match (&a, &b) {
                                (_, ChcExpr::Int(c)) => {
                                    if let Some(c1) = c.checked_sub(1) {
                                        ChcExpr::le(a.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::lt(a.clone(), b.clone())
                                    }
                                }
                                (ChcExpr::Int(c), _) => {
                                    if let Some(c1) = c.checked_add(1) {
                                        ChcExpr::ge(b.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::lt(a.clone(), b.clone())
                                    }
                                }
                                _ => ChcExpr::le(ChcExpr::add(a, ChcExpr::Int(1)), b),
                            },
                            ChcOp::Gt if is_int(&a) && is_int(&b) => match (&a, &b) {
                                (_, ChcExpr::Int(c)) => {
                                    if let Some(c1) = c.checked_add(1) {
                                        ChcExpr::ge(a.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::gt(a.clone(), b.clone())
                                    }
                                }
                                (ChcExpr::Int(c), _) => {
                                    if let Some(c1) = c.checked_sub(1) {
                                        ChcExpr::le(b.clone(), ChcExpr::Int(c1))
                                    } else {
                                        ChcExpr::gt(a.clone(), b.clone())
                                    }
                                }
                                _ => ChcExpr::ge(a, ChcExpr::add(b, ChcExpr::Int(1))),
                            },
                            _ => {
                                // Skip rebuild when children are unchanged (#3665)
                                if args[0].as_ref() == &a && args[1].as_ref() == &b {
                                    expr.clone()
                                } else {
                                    ChcExpr::Op(*op, vec![Arc::new(a), Arc::new(b)])
                                }
                            }
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        normalize_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        normalize_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }
}
