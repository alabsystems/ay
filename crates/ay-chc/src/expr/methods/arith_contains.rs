// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic-shape checks routing `check_sat` (wide constant moduli,
//! nonlinear products), with DAG forms for shared expressions (WP-F F0b).

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, MAX_EXPR_RECURSION_DEPTH};

impl ChcExpr {
    /// Whether the expression contains a `Mod`/`Div` whose divisor is a *wide*
    /// positive constant — value > `i64::MAX`, i.e. a `2^w` product tree for
    /// w>=63, the shape a preserved BV64 modulus (W1-1B) takes after
    /// `eliminate_mod_recursive` leaves it intact.
    ///
    /// Such a modulus is left for the BigInt executor to fold (`2^32 * 2^32 ->
    /// 2^64`) and decide exactly. The native DPLL(T) LIA loop instead treats the
    /// surviving `(mod x 2^64)` as an opaque factor (freeing `x` from its
    /// residue), which can produce a spurious Sat. `check_sat` uses this to route
    /// the query to the exact executor first, and to cap the native attempt, so
    /// the executor — not the incomplete native loop — is the one that decides it.
    pub(crate) fn contains_wide_const_mod_div(&self) -> bool {
        fn is_wide(expr: &ChcExpr) -> bool {
            matches!(expr, ChcExpr::Op(ChcOp::Mod | ChcOp::Div, args)
                if args.len() == 2
                    && ChcExpr::positive_int_constant_expr_value(args[1].as_ref())
                        .is_some_and(|v| v > i64::MAX as u128))
        }
        // DAG form (WP-F F0b): exact when no path reaches the depth cut-off.
        if super::super::dag::prefer_dag_walk(self, MAX_EXPR_RECURSION_DEPTH) {
            let mut found = false;
            super::super::dag::walk_distinct_preorder(self, |e| {
                if is_wide(e)
                    || matches!(e, ChcExpr::ArrayLambda(lambda) if lambda.body().contains_wide_const_mod_div())
                {
                    found = true;
                    return super::super::dag::Step::Stop;
                }
                if matches!(e, ChcExpr::Op(..) | ChcExpr::ArrayLambda(_)) {
                    super::super::dag::Step::Descend
                } else {
                    super::super::dag::Step::Skip
                }
            });
            return found;
        }
        fn check(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return false; // Conservative: assume none if too deep
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Mod | ChcOp::Div, args)
                    if args.len() == 2
                        && ChcExpr::positive_int_constant_expr_value(args[1].as_ref())
                            .is_some_and(|v| v > i64::MAX as u128) =>
                {
                    true
                }
                ChcExpr::Op(_, args) => args.iter().any(|a| check(a.as_ref(), depth + 1)),
                ChcExpr::ArrayLambda(lambda) => {
                    check(lambda.body(), depth + 1)
                        || lambda
                            .captures()
                            .iter()
                            .any(|value| check(value, depth + 1))
                }
                _ => false,
            })
        }
        check(self, 0)
    }

    /// Check if expression contains nonlinear integer multiplication (Mul of two
    /// non-constant sub-expressions). These produce Unknown from the LIA solver.
    pub(crate) fn contains_nonlinear_mul(&self) -> bool {
        // A product is nonlinear only when at least two of its factors each
        // contain a free variable. A factor with no free variables is a
        // constant regardless of its syntactic shape — e.g. `(- 1.0)`
        // (`Op(Neg,[Real])`), `(* 2.0 3.0)`, or `(to_real 5)`. The previous
        // implementation counted any arg that was not a *literal* `Int`/`Real`
        // node as non-constant, so `(* (- 1.0) x)` was misclassified as
        // nonlinear. That wrongly suppressed the executor fallback in
        // `check_sat` (gated on `!contains_nonlinear_mul`) on otherwise-linear
        // LRA queries (cav12/array_max etc.: every product is `(* (- 1.0) v)`),
        // forcing a fast Unknown. Counting variable-bearing factors keeps
        // genuine nonlinear products (`(* x y)`) classified as nonlinear.
        fn factor_has_var(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true; // Conservative: assume a variable is present.
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Var(_) => true,
                ChcExpr::Op(_, args) => args.iter().any(|a| factor_has_var(a, depth + 1)),
                ChcExpr::ConstArray(_ks, val) => factor_has_var(val, depth + 1),
                ChcExpr::PredicateApp(_, _, args) => {
                    args.iter().any(|a| factor_has_var(a, depth + 1))
                }
                ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| factor_has_var(a, depth + 1)),
                _ => false,
            })
        }
        // DAG form (WP-F F0b). The tree walk answers `true` as soon as it
        // reaches the depth cut-off, and otherwise asks, for every node, whether
        // it is a product with at least two variable-bearing factors — a
        // question about distinct nodes only.
        if super::super::dag::tree_size_at_least(self, super::super::dag::DAG_WALK_MIN_TREE) {
            if super::super::dag::longest_path_at_least(self, MAX_EXPR_RECURSION_DEPTH) {
                return true;
            }
            let mut has_var = super::super::dag::SubtreeAny::new(|e| matches!(e, ChcExpr::Var(_)));
            let mut found = false;
            super::super::dag::walk_distinct_preorder(self, |e| {
                if matches!(e, ChcExpr::ArrayLambda(lambda) if lambda.body().contains_nonlinear_mul())
                {
                    found = true;
                    return super::super::dag::Step::Stop;
                }
                if let ChcExpr::Op(ChcOp::Mul, args) = e {
                    if args.iter().filter(|a| has_var.holds(a)).count() >= 2 {
                        found = true;
                        return super::super::dag::Step::Stop;
                    }
                }
                super::super::dag::Step::Descend
            });
            return found;
        }
        fn inner(expr: &ChcExpr, depth: usize) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return true; // Conservative: assume nonlinear if too deep
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Op(ChcOp::Mul, args) => {
                    let var_factor_count =
                        args.iter().filter(|a| factor_has_var(a, depth + 1)).count();
                    if var_factor_count >= 2 {
                        return true;
                    }
                    args.iter().any(|a| inner(a, depth + 1))
                }
                ChcExpr::Op(_, args) => args.iter().any(|a| inner(a, depth + 1)),
                ChcExpr::ConstArray(_ks, val) => inner(val, depth + 1),
                ChcExpr::ArrayLambda(lambda) => {
                    inner(lambda.body(), depth + 1)
                        || lambda
                            .captures()
                            .iter()
                            .any(|value| inner(value, depth + 1))
                }
                ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| inner(a, depth + 1)),
                ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| inner(a, depth + 1)),
                _ => false,
            })
        }
        inner(self, 0)
    }
}
