// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Arc, ChcExpr, ChcOp, ChcVar, PdrSolver};

impl PdrSolver {
    /// Extract lower bound for a canonical variable from a formula.
    ///
    /// Searches the formula for constraints like:
    /// - `(>= var N)` → returns `Some(N)`
    /// - `(> var N)` → returns `Some(N+1)`
    /// - `(not (<= var N))` equivalent to `(> var N)` → returns `Some(N+1)`
    ///
    /// Part of #1613: Helper for self-loop closure enrichment.
    pub(in crate::pdr::solver) fn extract_lower_bound_for_var(
        formula: &ChcExpr,
        var_idx: usize,
        canonical_vars: &[ChcVar],
    ) -> Option<i128> {
        if var_idx >= canonical_vars.len() {
            return None;
        }
        let var_name = &canonical_vars[var_idx].name;
        Self::extract_lower_bound_recursive(formula, var_name)
    }

    /// Recursive helper to extract lower bound on a variable from a formula.
    pub(in crate::pdr::solver) fn extract_lower_bound_recursive(
        formula: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| {
            match formula {
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(*n);
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(n.saturating_add(1));
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Le, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(n.saturating_add(1));
                                }
                            }
                        }
                    }
                    if let ChcExpr::Op(ChcOp::Lt, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(*n);
                                }
                            }
                        }
                    }
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        if let Some(lb) = Self::extract_lower_bound_recursive(arg, var_name) {
                            return Some(lb);
                        }
                    }
                }
                _ => {}
            }
            None
        })
    }

    /// Extract an upper bound on a canonical variable from a formula if one exists.
    pub(in crate::pdr::solver) fn extract_upper_bound_for_canonical_var(
        formula: &ChcExpr,
        var_idx: usize,
        canonical_vars: &[ChcVar],
    ) -> Option<i128> {
        if var_idx >= canonical_vars.len() {
            return None;
        }
        let var_name = &canonical_vars[var_idx].name;
        Self::extract_upper_bound_recursive_impl(formula, var_name)
    }

    /// Recursive helper to extract upper bound on a variable from a formula.
    pub(in crate::pdr::solver) fn extract_upper_bound_recursive_impl(
        formula: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| {
            match formula {
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(*n);
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(n.saturating_sub(1));
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Op(ChcOp::Ge, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(n.saturating_sub(1));
                                }
                            }
                        }
                    }
                    if let ChcExpr::Op(ChcOp::Gt, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(*n);
                                }
                            }
                        }
                    }
                    if let ChcExpr::Op(ChcOp::Le, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Int(k), ChcExpr::Var(v)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(k.saturating_sub(1));
                                }
                            }
                        }
                    }
                    if let ChcExpr::Op(ChcOp::Lt, inner_args) = args[0].as_ref() {
                        if inner_args.len() == 2 {
                            if let (ChcExpr::Int(k), ChcExpr::Var(v)) =
                                (inner_args[0].as_ref(), inner_args[1].as_ref())
                            {
                                if v.name == var_name {
                                    return Some(*k);
                                }
                            }
                        }
                    }
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        if let Some(ub) = Self::extract_upper_bound_recursive_impl(arg, var_name) {
                            return Some(ub);
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) if !args.is_empty() => {
                    let bounds: Vec<_> = args
                        .iter()
                        .filter_map(|arg| Self::extract_upper_bound_recursive_impl(arg, var_name))
                        .collect();
                    if bounds.len() == args.len() {
                        return bounds.into_iter().min();
                    }
                }
                _ => {}
            }
            None
        })
    }

    /// Check if the formula contains an equality constraint between two canonical variables.
    pub(in crate::pdr::solver) fn has_equality_in_formula(
        formula: &ChcExpr,
        idx_i: usize,
        idx_j: usize,
        canonical_vars: &[ChcVar],
    ) -> bool {
        if idx_i >= canonical_vars.len() || idx_j >= canonical_vars.len() {
            return false;
        }
        let var_name_i = &canonical_vars[idx_i].name;
        let var_name_j = &canonical_vars[idx_j].name;
        Self::has_equality_recursive(formula, var_name_i, var_name_j)
    }

    /// Recursive helper to check if formula contains equality between two variables.
    pub(in crate::pdr::solver) fn has_equality_recursive(
        formula: &ChcExpr,
        var_name_i: &str,
        var_name_j: &str,
    ) -> bool {
        crate::expr::maybe_grow_expr_stack(|| {
            match formula {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(vi), ChcExpr::Var(vj)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if (vi.name == var_name_i && vj.name == var_name_j)
                            || (vi.name == var_name_j && vj.name == var_name_i)
                        {
                            return true;
                        }
                    }
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        if Self::has_equality_recursive(arg, var_name_i, var_name_j) {
                            return true;
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) if !args.is_empty() => {
                    return args
                        .iter()
                        .all(|arg| Self::has_equality_recursive(arg, var_name_i, var_name_j));
                }
                _ => {}
            }
            false
        })
    }

    /// Extract constant equality for a variable (e.g., `var = 5`) from formula.
    pub(in crate::pdr::solver) fn extract_constant_equality_for_var(
        formula: &ChcExpr,
        var_idx: usize,
        canonical_vars: &[ChcVar],
    ) -> Option<i128> {
        if var_idx >= canonical_vars.len() {
            return None;
        }
        let var_name = &canonical_vars[var_idx].name;
        Self::extract_constant_equality_recursive(formula, var_name)
    }

    /// Extract all var=constant equalities from a formula.
    pub(in crate::pdr::solver) fn extract_var_const_equalities(
        formula: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> Vec<(usize, i128)> {
        let mut result = Vec::new();
        for (idx, _var) in canonical_vars.iter().enumerate() {
            if let Some(c) = Self::extract_constant_equality_for_var(formula, idx, canonical_vars) {
                result.push((idx, c));
            }
        }
        result
    }

    /// Recursive helper to extract constant equality (var = N) from formula.
    pub(in crate::pdr::solver) fn extract_constant_equality_recursive(
        formula: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| {
            match formula {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(*n);
                        }
                    }
                    if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if v.name == var_name {
                            return Some(*n);
                        }
                    }
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for arg in args {
                        if let Some(c) = Self::extract_constant_equality_recursive(arg, var_name) {
                            return Some(c);
                        }
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) if !args.is_empty() => {
                    let constants: Vec<_> = args
                        .iter()
                        .filter_map(|arg| Self::extract_constant_equality_recursive(arg, var_name))
                        .collect();
                    if constants.len() == args.len() {
                        let first = constants[0];
                        if constants.iter().all(|&c| c == first) {
                            return Some(first);
                        }
                    }
                }
                _ => {}
            }
            None
        })
    }

    /// Filter out blocking lemmas from a formula.
    pub(in crate::pdr) fn filter_blocking_lemmas(formula: &ChcExpr) -> ChcExpr {
        Self::filter_blocking_lemmas_impl(formula, false)
    }

    /// More aggressive filtering for incoming transitions.
    pub(in crate::pdr) fn filter_blocking_lemmas_aggressive(formula: &ChcExpr) -> ChcExpr {
        Self::filter_blocking_lemmas_impl(formula, true)
    }

    /// Check if a formula is an error-implied invariant.
    pub(in crate::pdr) fn is_error_implied_invariant(formula: &ChcExpr) -> bool {
        if let ChcExpr::Op(ChcOp::Or, args) = formula {
            if args.len() == 2 {
                let (maybe_not_guard, maybe_conclusion) =
                    if matches!(&*args[0], ChcExpr::Op(ChcOp::Not, _)) {
                        (&*args[0], &*args[1])
                    } else if matches!(&*args[1], ChcExpr::Op(ChcOp::Not, _)) {
                        (&*args[1], &*args[0])
                    } else {
                        return false;
                    };

                if let ChcExpr::Op(ChcOp::Not, not_args) = maybe_not_guard {
                    if not_args.len() == 1 {
                        let guard = &*not_args[0];
                        let is_guard_comparison = matches!(
                            guard,
                            ChcExpr::Op(ChcOp::Ge | ChcOp::Le | ChcOp::Gt | ChcOp::Lt, _)
                        );
                        let is_conclusion_equality =
                            matches!(maybe_conclusion, ChcExpr::Op(ChcOp::Eq, _));

                        return is_guard_comparison && is_conclusion_equality;
                    }
                }
            }
        }
        false
    }

    pub(in crate::pdr::solver) fn filter_blocking_lemmas_impl(
        formula: &ChcExpr,
        aggressive: bool,
    ) -> ChcExpr {
        match formula {
            ChcExpr::Op(ChcOp::And, args) => {
                let filtered: Vec<ChcExpr> = args
                    .iter()
                    .map(|a| Self::filter_blocking_lemmas_impl(a, aggressive))
                    .filter(|e| *e != ChcExpr::Bool(true))
                    .collect();
                ChcExpr::and_all(filtered)
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Op(ChcOp::And, inner_args) => {
                    if Self::is_point_blocking_lemma(inner_args) {
                        ChcExpr::Bool(true)
                    } else {
                        formula.clone()
                    }
                }
                ChcExpr::Op(ChcOp::Eq, _) if Self::is_var_const_equality(args[0].as_ref()) => {
                    ChcExpr::Bool(true)
                }
                ChcExpr::Op(ChcOp::Le | ChcOp::Ge | ChcOp::Lt | ChcOp::Gt, _) => {
                    if aggressive {
                        ChcExpr::Bool(true)
                    } else {
                        formula.clone()
                    }
                }
                _ => formula.clone(),
            },
            _ => formula.clone(),
        }
    }

    /// Check if inner_args represents a point-blocking conjunction.
    pub(in crate::pdr::solver) fn is_point_blocking_lemma(inner_args: &[Arc<ChcExpr>]) -> bool {
        inner_args
            .iter()
            .all(|arg| Self::is_var_const_equality(arg.as_ref()))
    }

    /// Check if expr is an equality between a variable and a constant.
    pub(in crate::pdr::solver) fn is_var_const_equality(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| {
            if let ChcExpr::Op(ChcOp::And, args) = expr {
                return args.iter().all(|a| Self::is_var_const_equality(a.as_ref()));
            }

            let ChcExpr::Op(ChcOp::Eq, args) = expr else {
                return false;
            };
            if args.len() != 2 {
                return false;
            }
            let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());

            matches!(
                (lhs, rhs),
                (ChcExpr::Var(_), ChcExpr::Int(_)) | (ChcExpr::Int(_), ChcExpr::Var(_))
            )
        })
    }
}
