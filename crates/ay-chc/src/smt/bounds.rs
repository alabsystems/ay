// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound and equality analysis for integer variables (expression level).
//!
//! Companion: `bounds_inference.rs` has model-based inference methods
//! (term_const_i128_if_int, infer_int_bounds_from_sat_model, etc.).

use super::context::SmtContext;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl SmtContext {
    pub(super) fn flatten_top_level_and(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
        expr.collect_conjuncts_into(out);
    }

    pub(super) fn collect_int_var_const_equalities(
        expr: &ChcExpr,
        out: &mut FxHashMap<String, i128>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for a in args {
                    Self::collect_int_var_const_equalities(a, out);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if matches!(v.sort, ChcSort::Int) => {
                        out.insert(v.name.clone(), *n);
                    }
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                        out.insert(v.name.clone(), *n);
                    }
                    _ => {
                        if let Some((v, val)) =
                            Self::extract_linear_int_equality(args[0].as_ref(), args[1].as_ref())
                                .or_else(|| {
                                    Self::extract_linear_int_equality(
                                        args[1].as_ref(),
                                        args[0].as_ref(),
                                    )
                                })
                        {
                            out.insert(v.name, val);
                        }
                    }
                }
            }
            _ => {}
        })
    }

    /// Collect BV var=const equalities from the top-level conjunction.
    ///
    /// Matches patterns like `(= bv_var #xABCD)` where `bv_var` has `ChcSort::BitVec(w)`.
    /// Returns `(value, width)` pairs for canonical `SmtValue` construction.
    pub(super) fn collect_bv_var_const_equalities(
        expr: &ChcExpr,
        out: &mut FxHashMap<String, (u128, u32)>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for a in args {
                    Self::collect_bv_var_const_equalities(a, out);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::BitVec(val, width))
                        if matches!(v.sort, ChcSort::BitVec(_)) =>
                    {
                        out.insert(v.name.clone(), (*val, *width));
                    }
                    (ChcExpr::BitVec(val, width), ChcExpr::Var(v))
                        if matches!(v.sort, ChcSort::BitVec(_)) =>
                    {
                        out.insert(v.name.clone(), (*val, *width));
                    }
                    _ => {}
                }
            }
            _ => {}
        })
    }

    pub(super) fn extract_linear_int_equality(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
    ) -> Option<(ChcVar, i128)> {
        let c = match rhs {
            ChcExpr::Int(n) => *n,
            _ => return None,
        };

        // Decompose lhs into sum of (coeff * var) + constant using walk_linear_expr.
        // Solves: coeff * var + const_offset = c => var = (c - const_offset) / coeff
        let mut var_found: Option<(ChcVar, i128)> = None;
        let mut const_offset: i128 = 0;
        crate::expr::walk_linear_expr(
            lhs,
            1i128,
            &mut |mult, n| {
                const_offset = const_offset.checked_add(mult.checked_mul(n)?)?;
                Some(())
            },
            &mut |mult, v| {
                if !matches!(v.sort, ChcSort::Int) || var_found.is_some() {
                    return None; // Only handle single Int variable
                }
                var_found = Some((v.clone(), mult));
                Some(())
            },
        )?;

        let (var, coeff) = var_found?;
        // coeff * var = c - const_offset; require exact integer division.
        // Use checked_rem/checked_div to avoid panic on i128::MIN / -1 overflow.
        let rhs_val = c.checked_sub(const_offset)?;
        if coeff == 0 || rhs_val.checked_rem(coeff)? != 0 {
            return None;
        }
        Some((var, rhs_val.checked_div(coeff)?))
    }

    /// Collect integer var=const equalities with transitive closure over var=var chains.
    ///
    /// Unlike `collect_int_var_const_equalities` which only finds direct `var = const` pairs,
    /// this function also collects `var = var` equalities and uses a union-find to resolve
    /// transitive chains. For example, given `A = B, B = C, C = 5`, this resolves
    /// `{A: 5, B: 5, C: 5}`.
    ///
    /// Returns `true` if a contradiction was detected (same equivalence class, two different
    /// constants), `false` otherwise.
    ///
    /// Fix for #2445: chained var-var equalities caused false-Sat in assumption mode.
    pub(super) fn collect_int_equalities_with_closure(
        exprs: &[&ChcExpr],
        out: &mut FxHashMap<String, i128>,
    ) -> bool {
        // Inline union-find for var=var chains.
        // The parent map and find/union functions are kept simple — no constant
        // tracking in union, which avoids the silent-drop bug where `or_insert`
        // discards a conflicting constant.
        let mut parent: FxHashMap<String, String> = FxHashMap::default();
        let mut var_const: FxHashMap<String, i128> = FxHashMap::default();
        let mut var_var_pairs: Vec<(String, String)> = Vec::new();

        fn find(parent: &mut FxHashMap<String, String>, var: &str) -> String {
            if !parent.contains_key(var) {
                let owned = var.to_string();
                parent.insert(owned.clone(), owned.clone());
                return owned;
            }
            let is_root = parent.get(var).is_some_and(|p| p.as_str() == var);
            if is_root {
                return parent
                    .get_key_value(var)
                    .map_or_else(|| var.to_string(), |(k, _)| k.clone());
            }
            let p = parent
                .get(var)
                .cloned()
                .expect("invariant: var in parent map");
            let root = find(parent, &p);
            parent.insert(var.to_string(), root.clone());
            root
        }

        // Phase 1: Walk all expressions, collecting var=var and var=const pairs.
        // Direct contradictions (same variable, different constants) are detected
        // here and short-circuit to `true` immediately.
        for expr in exprs {
            if Self::collect_equality_pairs(expr, &mut var_var_pairs, &mut var_const) {
                return true;
            }
        }

        // Phase 2: Build union-find from var=var pairs (no constant tracking here)
        for (a, b) in &var_var_pairs {
            let ra = find(&mut parent, a);
            let rb = find(&mut parent, b);
            if ra != rb {
                parent.insert(rb, ra);
            }
        }

        // Phase 3: Map each var=const binding to its root representative.
        // Detect contradictions: same equivalence class with different constants.
        let mut root_constants: FxHashMap<String, i128> = FxHashMap::default();
        for (var, val) in &var_const {
            let root = find(&mut parent, var);
            if let Some(&existing) = root_constants.get(&root) {
                if existing != *val {
                    return true; // Contradiction: e.g., A=B, A=5, B=10
                }
            } else {
                root_constants.insert(root, *val);
            }
        }

        // Phase 4: Propagate constants to ALL variables in each equivalence class
        let all_vars: Vec<String> = parent.keys().cloned().collect();
        for var in all_vars {
            let root = find(&mut parent, &var);
            if let Some(&val) = root_constants.get(&root) {
                out.insert(var, val);
            }
        }

        false
    }

    /// Helper: extract var=var and var=const equality pairs from an expression.
    /// Returns `true` if a direct contradiction was detected (same variable
    /// bound to two different constants).
    fn collect_equality_pairs(
        expr: &ChcExpr,
        var_var: &mut Vec<(String, String)>,
        var_const: &mut FxHashMap<String, i128>,
    ) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for a in args {
                    if Self::collect_equality_pairs(a, var_var, var_const) {
                        return true;
                    }
                }
                false
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let mut try_insert = |name: String, val: i128| -> bool {
                    if let Some(&existing) = var_const.get(&name) {
                        if existing != val {
                            return true; // contradiction
                        }
                    }
                    var_const.insert(name, val);
                    false
                };
                match (args[0].as_ref(), args[1].as_ref()) {
                    // var = const
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if matches!(v.sort, ChcSort::Int) => {
                        try_insert(v.name.clone(), *n)
                    }
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                        try_insert(v.name.clone(), *n)
                    }
                    // var = var
                    (ChcExpr::Var(a), ChcExpr::Var(b))
                        if matches!(a.sort, ChcSort::Int) && matches!(b.sort, ChcSort::Int) =>
                    {
                        var_var.push((a.name.clone(), b.name.clone()));
                        false
                    }
                    _ => {
                        // Linear patterns like (+ k var) = c
                        if let Some((v, val)) =
                            Self::extract_linear_int_equality(args[0].as_ref(), args[1].as_ref())
                                .or_else(|| {
                                    Self::extract_linear_int_equality(
                                        args[1].as_ref(),
                                        args[0].as_ref(),
                                    )
                                })
                        {
                            try_insert(v.name, val)
                        } else {
                            false
                        }
                    }
                }
            }
            _ => false,
        })
    }

    pub(super) fn collect_int_var_bounds(
        expr: &ChcExpr,
        lower: &mut FxHashMap<String, i128>,
        upper: &mut FxHashMap<String, i128>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for a in args {
                    Self::collect_int_var_bounds(a, lower, upper);
                }
            }
            ChcExpr::Op(ChcOp::Le | ChcOp::Ge, args) if args.len() == 2 => {
                let op = match expr {
                    ChcExpr::Op(op, _) => op,
                    _ => return, // #6091: defensive
                };

                let (a, b) = (args[0].as_ref(), args[1].as_ref());

                let update_lower = |name: &str, v: i128, lower: &mut FxHashMap<String, i128>| {
                    lower
                        .entry(name.to_string())
                        .and_modify(|cur| *cur = (*cur).max(v))
                        .or_insert(v);
                };
                let update_upper = |name: &str, v: i128, upper: &mut FxHashMap<String, i128>| {
                    upper
                        .entry(name.to_string())
                        .and_modify(|cur| *cur = (*cur).min(v))
                        .or_insert(v);
                };

                match (op, a, b) {
                    // var <= c
                    (ChcOp::Le, ChcExpr::Var(v), ChcExpr::Int(c))
                        if matches!(v.sort, ChcSort::Int) =>
                    {
                        update_upper(&v.name, *c, upper);
                    }
                    // var >= c
                    (ChcOp::Ge, ChcExpr::Var(v), ChcExpr::Int(c))
                        if matches!(v.sort, ChcSort::Int) =>
                    {
                        update_lower(&v.name, *c, lower);
                    }
                    // c <= var  => var >= c
                    (ChcOp::Le, ChcExpr::Int(c), ChcExpr::Var(v))
                        if matches!(v.sort, ChcSort::Int) =>
                    {
                        update_lower(&v.name, *c, lower);
                    }
                    // c >= var  => var <= c
                    (ChcOp::Ge, ChcExpr::Int(c), ChcExpr::Var(v))
                        if matches!(v.sort, ChcSort::Int) =>
                    {
                        update_upper(&v.name, *c, upper);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

// Model-based inference methods are in bounds_inference.rs
