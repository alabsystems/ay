// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic bound extraction and linear coefficient normalization.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

use super::{BoundKind, Literal, Mbp};

impl Mbp {
    /// Check if a literal can be projected for a given variable (has extractable bounds).
    ///
    /// REQUIRES: Caller has verified that `lit.atom` contains `var` (e.g., via
    /// pre-computed per-literal variable sets). Callers that cannot guarantee this
    /// should check containment first.
    pub(super) fn is_projectable_literal(&self, lit: &Literal, var: &ChcVar) -> bool {
        match &var.sort {
            ChcSort::BitVec(_) => Self::extract_bv_bound(&lit.atom, var, lit.positive).is_some(),
            _ => self.extract_bound(&lit.atom, var, lit.positive).is_some(),
        }
    }

    /// Extract bound information from a comparison atom
    pub(super) fn extract_bound(
        &self,
        atom: &ChcExpr,
        var: &ChcVar,
        positive: bool,
    ) -> Option<BoundKind> {
        match atom {
            ChcExpr::Op(op, args) if args.len() == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                // Try to normalize to: coeff * var op term
                if let Some((coeff, term)) = self.factor_var(lhs, rhs, var) {
                    let (effective_op, effective_coeff) = if positive {
                        (*op, coeff)
                    } else {
                        // Negate the comparison
                        (self.negate_cmp(op), coeff)
                    };

                    // Determine bound type based on coefficient sign and comparison.
                    //
                    // The normalized form is `effective_coeff * var effective_op term`.
                    // When effective_coeff < 0, we multiply both sides by -1 to get
                    // |effective_coeff| * var FLIP(effective_op) -term.
                    // CRITICAL: both the comparison direction AND the term sign must flip.
                    match effective_op {
                        ChcOp::Eq => Some(BoundKind::Equality(effective_coeff, term)),
                        ChcOp::Le => {
                            if effective_coeff > 0 {
                                // coeff * var <= term → Upper bound
                                Some(BoundKind::Upper(effective_coeff, term, false))
                            } else {
                                // (-|c|) * var <= term → |c| * var >= -term → Lower bound
                                let neg = effective_coeff.checked_neg()?;
                                Some(BoundKind::Lower(neg, ChcExpr::neg(term), false))
                            }
                        }
                        ChcOp::Lt => {
                            if effective_coeff > 0 {
                                Some(BoundKind::Upper(effective_coeff, term, true))
                            } else {
                                let neg = effective_coeff.checked_neg()?;
                                Some(BoundKind::Lower(neg, ChcExpr::neg(term), true))
                            }
                        }
                        ChcOp::Ge => {
                            if effective_coeff > 0 {
                                // coeff * var >= term → Lower bound
                                Some(BoundKind::Lower(effective_coeff, term, false))
                            } else {
                                // (-|c|) * var >= term → |c| * var <= -term → Upper bound
                                let neg = effective_coeff.checked_neg()?;
                                Some(BoundKind::Upper(neg, ChcExpr::neg(term), false))
                            }
                        }
                        ChcOp::Gt => {
                            if effective_coeff > 0 {
                                Some(BoundKind::Lower(effective_coeff, term, true))
                            } else {
                                let neg = effective_coeff.checked_neg()?;
                                Some(BoundKind::Upper(neg, ChcExpr::neg(term), true))
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Try to express `lhs op rhs` as `coeff * var op term`
    /// Returns (coeff, term) where term is the expression with var factored out
    pub(super) fn factor_var(
        &self,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        var: &ChcVar,
    ) -> Option<(i128, ChcExpr)> {
        // Simple case: var op term or term op var
        if let ChcExpr::Var(v) = lhs {
            if v == var {
                return Some((1, rhs.clone()));
            }
        }
        if let ChcExpr::Var(v) = rhs {
            if v == var {
                return Some((-1, ChcExpr::neg(lhs.clone())));
            }
        }

        // Handle linear expressions
        let (lhs_coeff, lhs_rest) = Self::extract_var_coeff(lhs, var);
        let (rhs_coeff, rhs_rest) = Self::extract_var_coeff(rhs, var);

        let total_coeff = lhs_coeff.checked_sub(rhs_coeff)?;
        if total_coeff == 0 {
            return None; // Variable cancels out
        }

        // term = rhs_rest - lhs_rest (rearranging: total_coeff * var <= rhs_rest - lhs_rest)
        let term = ChcExpr::sub(rhs_rest, lhs_rest);
        Some((total_coeff, term))
    }

    /// Extract the coefficient of a variable in a linear term
    /// Returns (coefficient, remaining term without the variable)
    pub(super) fn extract_var_coeff(expr: &ChcExpr, var: &ChcVar) -> (i128, ChcExpr) {
        crate::expr::maybe_grow_expr_stack(|| {
            // At depth limit, conservatively report no variable occurrence
            if crate::expr::ExprDepthGuard::check().is_none() {
                return (0, expr.clone());
            }
            match expr {
                ChcExpr::Var(v) if v == var => (1, ChcExpr::Int(0)),
                ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Bool(_) | ChcExpr::Var(_) => {
                    (0, expr.clone())
                }
                ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                    let (c, rest) = Self::extract_var_coeff(&args[0], var);
                    match c.checked_neg() {
                        Some(neg_c) => (neg_c, ChcExpr::neg(rest)),
                        None => (0, expr.clone()),
                    }
                }
                ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                    let (c1, r1) = Self::extract_var_coeff(&args[0], var);
                    let (c2, r2) = Self::extract_var_coeff(&args[1], var);
                    match c1.checked_add(c2) {
                        Some(sum) => (sum, ChcExpr::add(r1, r2)),
                        None => (0, expr.clone()),
                    }
                }
                ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                    let (c1, r1) = Self::extract_var_coeff(&args[0], var);
                    let (c2, r2) = Self::extract_var_coeff(&args[1], var);
                    match c1.checked_sub(c2) {
                        Some(diff) => (diff, ChcExpr::sub(r1, r2)),
                        None => (0, expr.clone()),
                    }
                }
                ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                    // Check for c * var or var * c
                    if let ChcExpr::Int(c) = args[0].as_ref() {
                        if let ChcExpr::Var(v) = args[1].as_ref() {
                            if v == var {
                                return (*c, ChcExpr::Int(0));
                            }
                        }
                        let (inner_c, inner_r) = Self::extract_var_coeff(&args[1], var);
                        return match c.checked_mul(inner_c) {
                            Some(prod) => (prod, ChcExpr::mul(ChcExpr::Int(*c), inner_r)),
                            None => (0, expr.clone()),
                        };
                    }
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        if let ChcExpr::Var(v) = args[0].as_ref() {
                            if v == var {
                                return (*c, ChcExpr::Int(0));
                            }
                        }
                        let (inner_c, inner_r) = Self::extract_var_coeff(&args[0], var);
                        return match c.checked_mul(inner_c) {
                            Some(prod) => (prod, ChcExpr::mul(inner_r, ChcExpr::Int(*c))),
                            None => (0, expr.clone()),
                        };
                    }
                    (0, expr.clone())
                }
                _ => (0, expr.clone()),
            }
        })
    }

    /// Negate a comparison operator
    pub(super) fn negate_cmp(&self, op: &ChcOp) -> ChcOp {
        op.negate_comparison().unwrap_or_else(|| *op)
    }
}
