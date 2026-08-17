// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression traversal and numeric-offset helpers for algebraic parity checks.

use super::super::super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort};

impl PdrSolver {
    /// Find the definition of a variable in a constraint (var = expr).
    /// Chases through single-variable intermediate definitions:
    /// e.g., if constraint has `A = arg0` and `arg0 = X + Y`, returns `X + Y` for `A`.
    pub(in crate::pdr::solver) fn find_var_definition(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<ChcExpr> {
        // Collect all definitions (may have multiple: A = arg0, A = 3*q + r)
        let mut defs = Vec::new();
        Self::collect_var_definitions(constraint, var_name, &mut defs);
        if defs.is_empty() {
            return None;
        }
        // Prefer non-variable definition (the actual expression)
        if let Some(pos) = defs.iter().position(|d| !matches!(d, ChcExpr::Var(_))) {
            return Some(defs.swap_remove(pos));
        }
        // All definitions are variables — chase through them
        let mut visited = ay_core::kani_compat::DetHashSet::default();
        visited.insert(var_name.to_string());
        for def in &defs {
            if let ChcExpr::Var(v) = def {
                if visited.contains(&v.name) {
                    continue;
                }
                visited.insert(v.name.clone());
                let mut intermediates = Vec::new();
                Self::collect_var_definitions(constraint, &v.name, &mut intermediates);
                for idef in &intermediates {
                    if !matches!(idef, ChcExpr::Var(_)) {
                        return Some(idef.clone());
                    }
                }
            }
        }
        Some(defs.swap_remove(0))
    }

    /// Collect all definitions of var_name from equality conjuncts.
    fn collect_var_definitions(constraint: &ChcExpr, var_name: &str, out: &mut Vec<ChcExpr>) {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::collect_var_definitions(arg, var_name, out);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                if Self::is_var_expr(&args[0], var_name) {
                    out.push((*args[1]).clone());
                } else if Self::is_var_expr(&args[1], var_name) {
                    out.push((*args[0]).clone());
                }
            }
            _ => {}
        }
    }

    /// Extract all terms from a sum expression (flatten nested additions).
    /// No stack guard needed: Add nodes are flattened, recursion depth <= 2.
    pub(in crate::pdr::solver) fn extract_sum_terms(expr: &ChcExpr) -> Vec<ChcExpr> {
        match expr {
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut terms = Vec::new();
                for arg in args {
                    terms.extend(Self::extract_sum_terms(arg));
                }
                terms
            }
            _ => vec![expr.clone()],
        }
    }

    /// Find the top-level OR constraint in an expression.
    /// No stack guard needed: only recurses through And/Or (flattened, depth <= 3).
    pub(in crate::pdr::solver) fn find_or_constraint(constraint: &ChcExpr) -> Option<ChcExpr> {
        match constraint {
            ChcExpr::Op(ChcOp::Or, _) => Some(constraint.clone()),
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(or_expr) = Self::find_or_constraint(arg) {
                        return Some(or_expr);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Find offset of var from any source in a conjunction: var = source + offset.
    /// No stack guard needed: only recurses through And (flattened, depth <= 3).
    pub(in crate::pdr::solver) fn find_var_offset_in_conjuncts(
        expr: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(offset) = Self::find_var_offset_in_conjuncts(arg, var_name) {
                        return Some(offset);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check var = source + offset
                if Self::is_var_expr(&args[0], var_name) {
                    return Self::extract_any_offset(&args[1]);
                }
                if Self::is_var_expr(&args[1], var_name) {
                    return Self::extract_any_offset(&args[0]);
                }
                None
            }
            _ => None,
        }
    }

    /// Extract offset from expr = source + offset (where source is any variable)
    pub(in crate::pdr::solver) fn extract_any_offset(expr: &ChcExpr) -> Option<i128> {
        match expr {
            ChcExpr::Var(_) => Some(0), // Identity
            ChcExpr::Int(c) => Some(*c),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                if let ChcExpr::Int(c) = args[0].as_ref() {
                    Some(-c)
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Try to extract constant from either side
                if let Some(c) = Self::get_constant(&args[0]) {
                    return Some(c);
                }
                if let Some(c) = Self::get_constant(&args[1]) {
                    return Some(c);
                }
                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // var - const = offset of -const
                if let Some(c) = Self::get_constant(&args[1]) {
                    return Some(-c);
                }
                None
            }
            _ => None,
        }
    }

    /// Find offset c where post_var = pre_var + c in constraint
    pub(in crate::pdr::solver) fn find_offset_in_constraint(
        constraint: &ChcExpr,
        pre_var: &str,
        post_var: &str,
    ) -> Option<i128> {
        // Look through AND conjuncts
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(offset) = Self::find_offset_in_constraint(arg, pre_var, post_var) {
                        return Some(offset);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check: post_var = f(pre_var)
                let (lhs, rhs) = (&args[0], &args[1]);

                // Check if lhs is post_var and rhs is pre_var + const
                if Self::is_var_expr(lhs, post_var) {
                    if let Some(offset) = Self::extract_addition_offset(rhs, pre_var) {
                        return Some(offset);
                    }
                }
                // Check the reverse: rhs is post_var
                if Self::is_var_expr(rhs, post_var) {
                    if let Some(offset) = Self::extract_addition_offset(lhs, pre_var) {
                        return Some(offset);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Extract offset c from expression pre_var + c
    pub(in crate::pdr::solver) fn extract_addition_offset(
        expr: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        match expr {
            ChcExpr::Var(v) if v.name == var_name => Some(0), // Identity: var + 0
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Check both orderings: (var + const) or (const + var)
                let (var_idx, const_idx) = if Self::is_var_expr(&args[0], var_name) {
                    (Some(0), 1)
                } else if Self::is_var_expr(&args[1], var_name) {
                    (Some(1), 0)
                } else {
                    (None, 0)
                };

                if var_idx.is_some() {
                    Self::get_constant(&args[const_idx])
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // var - const = var + (-const)
                if Self::is_var_expr(&args[0], var_name) {
                    Self::get_constant(&args[1]).map(|c| -c)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check if expression is a variable with the given name
    pub(in crate::pdr::solver) fn is_var_expr(expr: &ChcExpr, var_name: &str) -> bool {
        match expr {
            ChcExpr::Var(v) => v.name == var_name,
            _ => false,
        }
    }

    /// True when a sort can participate in the current numeric reasoning.
    ///
    /// Convex closure stores sample values as `i64`; parity helpers use `i128`.
    /// Keep BV support limited to widths that fit losslessly in that representation.
    pub(in crate::pdr::solver) fn supports_i64_numeric_sort(sort: &ChcSort) -> bool {
        match sort {
            ChcSort::Int => true,
            ChcSort::BitVec(width) => *width <= 63,
            _ => false,
        }
    }

    /// Get constant value from expression (handles negated constants and BV literals)
    pub(in crate::pdr::solver) fn get_constant(expr: &ChcExpr) -> Option<i128> {
        match expr {
            ChcExpr::Int(c) => Some(*c),
            // BV constants participate in numeric reasoning only when they fit losslessly.
            ChcExpr::BitVec(val, width) if *width <= 63 => i128::try_from(*val).ok(),
            // Handle (- c) pattern for negative constants
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                if let ChcExpr::Int(c) = args[0].as_ref() {
                    c.checked_neg()
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
