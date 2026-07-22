// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Algebraic parity verification and expression utilities.
//!
//! Contains purely algebraic (non-SMT) parity checks for transitions,
//! paired-sum parity analysis for OR-branching constraints, and low-level
//! expression utilities (variable definition lookup, offset extraction,
//! constant extraction, sort checks).

use super::super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

impl PdrSolver {
    /// Algebraically check if parity (mod k) is preserved from pre_expr to post_expr.
    ///
    /// Supports patterns:
    /// - Identity: post = pre
    /// - Constant offset: post = pre + c (parity preserved if c mod k == 0)
    /// - Constraint-defined: post_var = pre_var + c in constraint
    /// - Sum pattern: post_var = pre_var + sum of vars with paired updates
    pub(in crate::pdr::solver) fn algebraic_parity_preserved(
        pre_expr: &ChcExpr,
        post_expr: &ChcExpr,
        constraint: Option<&ChcExpr>,
        k: i128,
    ) -> bool {
        // Case 1: Identity (post = pre)
        if pre_expr == post_expr {
            return true;
        }

        // Get pre and post variable names if they're simple variables
        let pre_var = match pre_expr {
            ChcExpr::Var(v) => Some(v.name.as_str()),
            _ => None,
        };
        let post_var = match post_expr {
            ChcExpr::Var(v) => Some(v.name.as_str()),
            _ => None,
        };

        // Case 2: Both are variables - look in constraint for relationship
        if let (Some(pre_name), Some(post_name)) = (pre_var, post_var) {
            if let Some(constr) = constraint {
                // Look for post_var = pre_var + const in the constraint
                if let Some(offset) = Self::find_offset_in_constraint(constr, pre_name, post_name) {
                    return offset.rem_euclid(k) == 0;
                }

                // Case 4: Check for sum pattern: post_var = pre_var + sum of other vars
                // where the other vars have paired updates (all get same offset)
                if Self::check_paired_sum_parity(constr, pre_name, post_name, k) {
                    return true;
                }
            }
        }

        // Case 3: post_expr is already (pre_var + constant)
        if let Some(pre_name) = pre_var {
            if let Some(offset) = Self::extract_addition_offset(post_expr, pre_name) {
                return offset.rem_euclid(k) == 0;
            }
        }

        // Default: can't prove parity is preserved
        false
    }

    /// Check if post_var = pre_var + vars where vars are paired updates.
    /// This handles the pattern: F = C + D + E where D and E come from OR branches
    /// with the same offset (D = A ± delta, E = B ± delta), so D + E = A + B + 2*delta.
    /// If A and B are equal (from equality invariants), D + E = 2*A + 2*delta = even.
    pub(in crate::pdr::solver) fn check_paired_sum_parity(
        constraint: &ChcExpr,
        pre_var: &str,
        post_var: &str,
        k: i128,
    ) -> bool {
        // Find post_var = expr in constraint
        let sum_expr = match Self::find_var_definition(constraint, post_var) {
            Some(e) => e,
            None => return false,
        };

        // Extract sum terms from sum_expr
        let terms = Self::extract_sum_terms(&sum_expr);

        // Check if pre_var is in the sum
        let has_pre_var = terms.iter().any(|t| match t {
            ChcExpr::Var(v) => v.name == pre_var,
            _ => false,
        });
        if !has_pre_var {
            return false;
        }

        // Get the other terms (excluding pre_var)
        let other_terms: Vec<_> = terms
            .iter()
            .filter(|t| match t {
                ChcExpr::Var(v) => v.name != pre_var,
                _ => true,
            })
            .cloned()
            .collect();

        if other_terms.is_empty() {
            return true; // post_var = pre_var, identity
        }

        // Check if all other terms are variables that come from paired OR updates
        // Look for pattern where each var V has definition V = source + delta in OR branches
        let or_expr = match Self::find_or_constraint(constraint) {
            Some(e) => e,
            None => {
                // No OR: this clause may be the result of OR-splitting.
                // Check if the constraint directly provides constant offsets for
                // all sum terms. If so, verify the total offset is 0 mod k.
                let mut sum_offset = 0i128;
                let mut all_found = true;
                for term in &other_terms {
                    if let ChcExpr::Var(v) = term {
                        if let Some(offset) =
                            Self::find_var_offset_in_conjuncts(constraint, &v.name)
                        {
                            sum_offset = sum_offset.wrapping_add(offset);
                        } else {
                            all_found = false;
                            break;
                        }
                    } else if let Some(c) = Self::get_constant(term) {
                        sum_offset = sum_offset.wrapping_add(c);
                    } else {
                        all_found = false;
                        break;
                    }
                }
                return all_found && sum_offset.rem_euclid(k) == 0;
            }
        };
        let or_cases = match &or_expr {
            ChcExpr::Op(ChcOp::Or, args) => {
                args.iter().map(|a| (**a).clone()).collect::<Vec<ChcExpr>>()
            }
            _ => return false,
        };

        // For each OR case, collect the offsets for all other_term variables
        let mut case_sums: Vec<i128> = Vec::new();

        for case in &or_cases {
            let mut sum_offset = 0i128;
            let mut all_found = true;

            for term in &other_terms {
                if let ChcExpr::Var(v) = term {
                    // Find v = source + offset in this case
                    if let Some(offset) = Self::find_var_offset_in_conjuncts(case, &v.name) {
                        sum_offset = sum_offset.wrapping_add(offset);
                    } else {
                        all_found = false;
                        break;
                    }
                } else if let Some(c) = Self::get_constant(term) {
                    sum_offset = sum_offset.wrapping_add(c);
                } else {
                    all_found = false;
                    break;
                }
            }

            if all_found {
                case_sums.push(sum_offset);
            } else {
                return false;
            }
        }

        // Check if all case sums have the same parity mod k
        if case_sums.is_empty() {
            return false;
        }
        case_sums.iter().all(|s| s.rem_euclid(k) == 0)
    }

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

    pub(in crate::pdr::solver) fn extract_simple_parity_equality(
        &self,
        pred: PredicateId,
        formula: &ChcExpr,
    ) -> Option<(ChcVar, i128, i128)> {
        fn parse_mod_side(expr: &ChcExpr) -> Option<(String, i128)> {
            let ChcExpr::Op(ChcOp::Mod, args) = expr else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let ChcExpr::Var(v) = args[0].as_ref() else {
                return None;
            };
            let ChcExpr::Int(k) = args[1].as_ref() else {
                return None;
            };
            if *k <= 0 {
                return None;
            }
            Some((v.name.clone(), *k))
        }

        fn parse_const_side(expr: &ChcExpr) -> Option<i128> {
            let ChcExpr::Int(c) = expr else {
                return None;
            };
            Some(*c)
        }

        let ChcExpr::Op(ChcOp::Eq, args) = formula else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();
        let (var_name, k, c) = if let (Some((name, k)), Some(c)) =
            (parse_mod_side(lhs), parse_const_side(rhs))
        {
            (name, k, c)
        } else if let (Some((name, k)), Some(c)) = (parse_mod_side(rhs), parse_const_side(lhs)) {
            (name, k, c)
        } else {
            return None;
        };

        let canonical_var = self
            .canonical_vars(pred)?
            .iter()
            .find(|v| v.name == var_name && matches!(v.sort, ChcSort::Int))
            .cloned()?;
        Some((canonical_var, k, c.rem_euclid(k)))
    }
}
