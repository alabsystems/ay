// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Algebraic parity verification and expression utilities.
//!
//! Contains purely algebraic (non-SMT) parity checks for transitions,
//! paired-sum parity analysis for OR-branching constraints, and low-level
//! expression utilities (variable definition lookup, offset extraction,
//! constant extraction, sort checks).

mod expressions;

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
                let Some(sum_offset) = Self::sum_offset_for_terms(constraint, &other_terms) else {
                    return false;
                };
                return sum_offset.rem_euclid(k) == 0;
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
            let Some(sum_offset) = Self::sum_offset_for_terms(case, &other_terms) else {
                return false;
            };
            case_sums.push(sum_offset);
        }

        // Check if all case sums have the same parity mod k
        if case_sums.is_empty() {
            return false;
        }
        case_sums.iter().all(|s| s.rem_euclid(k) == 0)
    }

    /// Sum the constant offsets contributed by `terms` in one constraint branch.
    fn sum_offset_for_terms(constraint: &ChcExpr, terms: &[ChcExpr]) -> Option<i128> {
        let mut sum_offset = 0i128;
        for term in terms {
            if let ChcExpr::Var(v) = term {
                let offset = Self::find_var_offset_in_conjuncts(constraint, &v.name)?;
                sum_offset = sum_offset.wrapping_add(offset);
            } else if let Some(constant) = Self::get_constant(term) {
                sum_offset = sum_offset.wrapping_add(constant);
            } else {
                return None;
            }
        }
        Some(sum_offset)
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
