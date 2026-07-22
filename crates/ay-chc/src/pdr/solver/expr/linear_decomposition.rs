// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear expression decomposition utilities.
//!
//! Functions for decomposing CHC expressions into linear forms like
//! `(base_var, offset)` or `(base_var, Option<(term_var, coefficient)>)`.
//! Used by sum preservation and algebraic verification.

use super::super::PdrSolver;
use crate::{ChcExpr, ChcOp};

impl PdrSolver {
    /// Extract variable name and offset from two expressions that form an addition.
    pub(in crate::pdr::solver) fn extract_var_and_offset(
        e1: &ChcExpr,
        e2: &ChcExpr,
    ) -> (Option<String>, Option<i128>) {
        // Try e1=var, e2=const
        let var1 = Self::extract_var_name(e1);
        let const2 = Self::extract_constant(e2);
        if var1.is_some() && const2.is_some() {
            return (var1, const2);
        }

        // Try e1=const, e2=var
        let const1 = Self::extract_constant(e1);
        let var2 = Self::extract_var_name(e2);
        if const1.is_some() && var2.is_some() {
            return (var2, const1);
        }

        (None, None)
    }

    /// Extract a variable name from an expression.
    pub(in crate::pdr::solver) fn extract_var_name(e: &ChcExpr) -> Option<String> {
        match e {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        }
    }

    /// Extract a constant from an expression (handles Int and Neg(Int)).
    pub(in crate::pdr::solver) fn extract_constant(e: &ChcExpr) -> Option<i128> {
        match e {
            ChcExpr::Int(n) => Some(*n),
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                if let ChcExpr::Int(n) = args[0].as_ref() {
                    n.checked_neg()
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Handle (+ -1 A) which is represented as (+ (- 1) A)
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = args[0].as_ref() {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            return n.checked_neg();
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Decompose a linear expression into (base_var, offset).
    ///
    /// Examples:
    /// - A -> (A, 0)
    /// - (+ -1 A) -> (A, -1)
    /// - (+ A 1) -> (A, 1)
    pub(in crate::pdr::solver) fn decompose_linear_expr(expr: &ChcExpr) -> Option<(String, i128)> {
        match expr {
            ChcExpr::Var(v) => Some((v.name.clone(), 0)),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Try (+ const var) pattern
                let const_val = Self::extract_constant(&args[0]);
                let var_name = Self::extract_var_name(&args[1]);
                if let (Some(c), Some(v)) = (const_val, var_name) {
                    return Some((v, c));
                }

                // Try (+ var const) pattern
                let var_name = Self::extract_var_name(&args[0]);
                let const_val = Self::extract_constant(&args[1]);
                if let (Some(v), Some(c)) = (var_name, const_val) {
                    return Some((v, c));
                }

                // Try (+ (- 1) var) pattern for (var - 1)
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = args[0].as_ref() {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            if let ChcExpr::Var(v) = args[1].as_ref() {
                                return n.checked_neg().map(|neg| (v.name.clone(), neg));
                            }
                        }
                    }
                }

                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // (- var const) -> (var, -const)
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    return n.checked_neg().map(|neg| (v.name.clone(), neg));
                }
                None
            }
            _ => None,
        }
    }

    /// Extract a linear definition with variable terms: var = base + coef*term_var + const_offset
    /// Returns (base_var_name, Option<(term_var_name, coefficient)>)
    ///
    /// Handles patterns like:
    /// - D = B + F  => (B, Some((F, 1)))
    /// - E = C - F  => (C, Some((F, -1)))
    /// - E = (+ C (* (- 1) F)) => (C, Some((F, -1)))
    pub(in crate::pdr::solver) fn extract_var_linear_def_extended(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<(String, Option<(String, i128)>)> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                // Search conjuncts
                for arg in args {
                    if let Some(def) = Self::extract_var_linear_def_extended(arg, var_name) {
                        return Some(def);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());

                // Try var = expr
                if let ChcExpr::Var(v) = lhs {
                    if v.name == var_name {
                        return Self::decompose_to_base_and_var_term(rhs);
                    }
                }
                // Try expr = var
                if let ChcExpr::Var(v) = rhs {
                    if v.name == var_name {
                        return Self::decompose_to_base_and_var_term(lhs);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Decompose expression into (base_var, Option<(term_var, coef)>) form.
    ///
    /// Handles:
    /// - var1 => (var1, None)
    /// - (+ var1 var2) => (var1, Some((var2, 1)))
    /// - (+ var1 (* -1 var2)) => (var1, Some((var2, -1)))
    /// - (+ var1 (* (- 1) var2)) => (var1, Some((var2, -1)))
    pub(in crate::pdr::solver) fn decompose_to_base_and_var_term(
        expr: &ChcExpr,
    ) -> Option<(String, Option<(String, i128)>)> {
        match expr {
            ChcExpr::Var(v) => Some((v.name.clone(), None)),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                let (a0, a1) = (args[0].as_ref(), args[1].as_ref());

                // (+ var1 var2) - simple sum
                if let (ChcExpr::Var(base), ChcExpr::Var(term)) = (a0, a1) {
                    return Some((base.name.clone(), Some((term.name.clone(), 1))));
                }
                if let (ChcExpr::Var(term), ChcExpr::Var(base)) = (a0, a1) {
                    // Commutative - try other order
                    return Some((base.name.clone(), Some((term.name.clone(), 1))));
                }

                // (+ var1 (* coef var2)) - scaled term
                if let ChcExpr::Var(base) = a0 {
                    if let Some((term_var, coef)) = Self::extract_scaled_var(a1) {
                        return Some((base.name.clone(), Some((term_var, coef))));
                    }
                }
                if let ChcExpr::Var(base) = a1 {
                    if let Some((term_var, coef)) = Self::extract_scaled_var(a0) {
                        return Some((base.name.clone(), Some((term_var, coef))));
                    }
                }

                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // (- var1 var2) => (var1, Some((var2, -1)))
                if let (ChcExpr::Var(base), ChcExpr::Var(term)) =
                    (args[0].as_ref(), args[1].as_ref())
                {
                    return Some((base.name.clone(), Some((term.name.clone(), -1))));
                }
                None
            }
            _ => None,
        }
    }

    /// Extract a scaled variable: (* coef var) or (* (- n) var) => (var_name, coef)
    pub(in crate::pdr::solver) fn extract_scaled_var(expr: &ChcExpr) -> Option<(String, i128)> {
        match expr {
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                let (a0, a1) = (args[0].as_ref(), args[1].as_ref());

                // (* int var)
                if let (ChcExpr::Int(coef), ChcExpr::Var(v)) = (a0, a1) {
                    return Some((v.name.clone(), *coef));
                }
                // (* var int)
                if let (ChcExpr::Var(v), ChcExpr::Int(coef)) = (a0, a1) {
                    return Some((v.name.clone(), *coef));
                }
                // (* (- n) var)
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = a0 {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            if let ChcExpr::Var(v) = a1 {
                                return n.checked_neg().map(|neg| (v.name.clone(), neg));
                            }
                        }
                    }
                }
                // (* var (- n))
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = a1 {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            if let ChcExpr::Var(v) = a0 {
                                return n.checked_neg().map(|neg| (v.name.clone(), neg));
                            }
                        }
                    }
                }

                None
            }
            _ => None,
        }
    }

    /// Extract a linear definition of a variable from a constraint.
    ///
    /// Looks for patterns like:
    /// - (= var (+ base offset)) -> (base_name, offset)
    /// - (= var (+ offset base)) -> (base_name, offset)
    /// - (= var base) -> (base_name, 0)
    ///
    /// Returns (base_var_name, constant_offset) if found.
    pub(in crate::pdr::solver) fn extract_var_linear_def(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<(String, i128)> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                // Search conjuncts
                for arg in args {
                    if let Some(def) = Self::extract_var_linear_def(arg, var_name) {
                        return Some(def);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check if this is var = expr
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());

                // Try var = expr
                if let ChcExpr::Var(v) = lhs {
                    if v.name == var_name {
                        return Self::decompose_to_base_and_offset(rhs);
                    }
                }
                // Try expr = var
                if let ChcExpr::Var(v) = rhs {
                    if v.name == var_name {
                        return Self::decompose_to_base_and_offset(lhs);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Decompose an expression into (base_var, offset) form.
    ///
    /// Handles:
    /// - var -> (var, 0)
    /// - (+ var const) -> (var, const)
    /// - (+ const var) -> (var, const)
    /// - (+ (- 1) var) -> (var, -1)
    pub(in crate::pdr::solver) fn decompose_to_base_and_offset(
        expr: &ChcExpr,
    ) -> Option<(String, i128)> {
        match expr {
            ChcExpr::Var(v) => Some((v.name.clone(), 0)),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                let (a0, a1) = (args[0].as_ref(), args[1].as_ref());

                // (+ var const)
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (a0, a1) {
                    return Some((v.name.clone(), *n));
                }
                // (+ const var)
                if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (a0, a1) {
                    return Some((v.name.clone(), *n));
                }
                // (+ (- 1) var) representing var - 1
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = a0 {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            if let ChcExpr::Var(v) = a1 {
                                return n.checked_neg().map(|neg| (v.name.clone(), neg));
                            }
                        }
                    }
                }
                // (+ var (- 1)) representing var - 1
                if let ChcExpr::Op(ChcOp::Neg, neg_args) = a1 {
                    if neg_args.len() == 1 {
                        if let ChcExpr::Int(n) = neg_args[0].as_ref() {
                            if let ChcExpr::Var(v) = a0 {
                                return n.checked_neg().map(|neg| (v.name.clone(), neg));
                            }
                        }
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // (- var const)
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    return n.checked_neg().map(|neg| (v.name.clone(), neg));
                }
                None
            }
            _ => None,
        }
    }
}
