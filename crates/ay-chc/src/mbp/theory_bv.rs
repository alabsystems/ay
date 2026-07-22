// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV-specific variable projection (Fourier-Motzkin analogue for bitvectors).

use crate::bv_util::bv_to_signed;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{Literal, Mbp};

impl Mbp {
    /// Project out a bitvector variable using unsigned interval elimination.
    ///
    /// BV comparisons are structurally simpler than arithmetic: always
    /// `x CMP term` or `term CMP x`, no linear coefficients. The projection
    /// extracts BV bounds, uses equality substitution when available, and
    /// resolves lower/upper bound pairs (FM-style) to eliminate the variable.
    ///
    /// Signed comparisons are handled with independent signed interval
    /// resolution (using `bvslt`/`bvsle`), separate from unsigned bounds.
    pub(super) fn project_bitvec_var(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        mut without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let mut lower_bounds: Vec<(ChcExpr, bool)> = Vec::new(); // unsigned (term, strict)
        let mut upper_bounds: Vec<(ChcExpr, bool)> = Vec::new();
        let mut signed_lower_bounds: Vec<(ChcExpr, bool)> = Vec::new();
        let mut signed_upper_bounds: Vec<(ChcExpr, bool)> = Vec::new();
        let mut unhandled: Vec<usize> = Vec::new();
        let mut bound_indices: Vec<usize> = Vec::new();
        let mut signed_bound_indices: Vec<usize> = Vec::new();

        for (i, lit) in with_var.iter().enumerate() {
            if let Some(bound) = Self::extract_bv_bound(&lit.atom, var, lit.positive) {
                match bound {
                    BvBound::Equality(term) => {
                        // Equality: substitute var = term in all other with_var literals
                        for (j, other) in with_var.iter().enumerate() {
                            if j == i {
                                continue;
                            }
                            let new_atom = other.atom.substitute(&[(var.clone(), term.clone())]);
                            let simplified = new_atom.simplify_constants();
                            if simplified != ChcExpr::Bool(true) {
                                without_var.push(Literal::new(simplified, other.positive));
                            }
                        }
                        return without_var;
                    }
                    BvBound::Lower(term, strict) => {
                        lower_bounds.push((term, strict));
                        bound_indices.push(i);
                    }
                    BvBound::Upper(term, strict) => {
                        upper_bounds.push((term, strict));
                        bound_indices.push(i);
                    }
                    BvBound::SignedLower(term, strict) => {
                        signed_lower_bounds.push((term, strict));
                        signed_bound_indices.push(i);
                    }
                    BvBound::SignedUpper(term, strict) => {
                        signed_upper_bounds.push((term, strict));
                        signed_bound_indices.push(i);
                    }
                }
            } else {
                unhandled.push(i);
            }
        }

        // For unhandled literals: substitute var with model value
        if let Some(val) = Self::model_value_expr(var, model) {
            for &idx in &unhandled {
                let lit = &with_var[idx];
                let new_atom = lit.atom.substitute(&[(var.clone(), val.clone())]);
                let simplified = new_atom.simplify_constants();
                if simplified != ChcExpr::Bool(true) {
                    without_var.push(Literal::new(simplified, lit.positive));
                }
            }
        }

        // Resolve unsigned bounds: select tightest lower and upper, eliminate var
        // by asserting lower <=_u upper (the interval is non-empty).
        let unsigned_resolved = if !lower_bounds.is_empty() && !upper_bounds.is_empty() {
            let best_lb = self.pick_tightest_bv_lower(&lower_bounds, model);
            let best_ub = self.pick_tightest_bv_upper(&upper_bounds, model);
            if let (Some((lb_term, lb_strict)), Some((ub_term, ub_strict))) = (best_lb, best_ub) {
                let cmp_op = if lb_strict || ub_strict {
                    ChcOp::BvULt
                } else {
                    ChcOp::BvULe
                };
                let cmp = ChcExpr::Op(cmp_op, vec![Arc::new(lb_term), Arc::new(ub_term)]);
                let simplified = cmp.simplify_constants();
                if simplified != ChcExpr::Bool(true) {
                    without_var.push(Literal::new(simplified, true));
                }
                true
            } else {
                false
            }
        } else {
            false
        };

        // When unsigned bounds can't be paired, fall back to model-value substitution.
        if !unsigned_resolved && !bound_indices.is_empty() {
            if let Some(val) = Self::model_value_expr(var, model) {
                for &idx in &bound_indices {
                    let lit = &with_var[idx];
                    let new_atom = lit.atom.substitute(&[(var.clone(), val.clone())]);
                    let simplified = new_atom.simplify_constants();
                    if simplified != ChcExpr::Bool(true) {
                        without_var.push(Literal::new(simplified, lit.positive));
                    }
                }
            }
        }

        // Resolve signed bounds independently: select tightest signed lower and
        // upper, eliminate var by asserting lb <=_s ub.
        let signed_resolved = if !signed_lower_bounds.is_empty() && !signed_upper_bounds.is_empty()
        {
            let best_lb = self.pick_tightest_bv_signed_lower(&signed_lower_bounds, var, model);
            let best_ub = self.pick_tightest_bv_signed_upper(&signed_upper_bounds, var, model);
            if let (Some((lb_term, lb_strict)), Some((ub_term, ub_strict))) = (best_lb, best_ub) {
                let cmp_op = if lb_strict || ub_strict {
                    ChcOp::BvSLt
                } else {
                    ChcOp::BvSLe
                };
                let cmp = ChcExpr::Op(cmp_op, vec![Arc::new(lb_term), Arc::new(ub_term)]);
                let simplified = cmp.simplify_constants();
                if simplified != ChcExpr::Bool(true) {
                    without_var.push(Literal::new(simplified, true));
                }
                true
            } else {
                false
            }
        } else {
            false
        };

        // When signed bounds can't be paired, fall back to model-value substitution.
        if !signed_resolved && !signed_bound_indices.is_empty() {
            if let Some(val) = Self::model_value_expr(var, model) {
                for &idx in &signed_bound_indices {
                    let lit = &with_var[idx];
                    let new_atom = lit.atom.substitute(&[(var.clone(), val.clone())]);
                    let simplified = new_atom.simplify_constants();
                    if simplified != ChcExpr::Bool(true) {
                        without_var.push(Literal::new(simplified, lit.positive));
                    }
                }
            }
        }

        without_var
    }

    /// Extract a BV bound from a comparison literal.
    ///
    /// BV comparisons have no coefficients (unlike arithmetic). The bound
    /// is always `var CMP term` or `term CMP var`.
    pub(super) fn extract_bv_bound(
        atom: &ChcExpr,
        var: &ChcVar,
        positive: bool,
    ) -> Option<BvBound> {
        match atom {
            ChcExpr::Op(op, args) if args.len() == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];
                let var_on_lhs = matches!(lhs.as_ref(), ChcExpr::Var(v) if v == var);
                let var_on_rhs = matches!(rhs.as_ref(), ChcExpr::Var(v) if v == var);

                if !var_on_lhs && !var_on_rhs {
                    return None;
                }

                // The OTHER side must not contain var
                let other = if var_on_lhs { rhs } else { lhs };
                if other.contains_var_name(&var.name) {
                    return None;
                }

                // Effective op after polarity negation
                let effective_op = if positive {
                    *op
                } else {
                    op.negate_comparison()?
                };

                // Normalize to var on LHS: var OP term
                let (norm_op, term) = if var_on_lhs {
                    (effective_op, rhs.as_ref().clone())
                } else {
                    (Self::flip_bv_cmp(&effective_op)?, lhs.as_ref().clone())
                };

                match norm_op {
                    ChcOp::Eq => Some(BvBound::Equality(term)),
                    ChcOp::BvULe => Some(BvBound::Upper(term, false)),
                    ChcOp::BvULt => Some(BvBound::Upper(term, true)),
                    ChcOp::BvUGe => Some(BvBound::Lower(term, false)),
                    ChcOp::BvUGt => Some(BvBound::Lower(term, true)),
                    ChcOp::BvSLe => Some(BvBound::SignedUpper(term, false)),
                    ChcOp::BvSLt => Some(BvBound::SignedUpper(term, true)),
                    ChcOp::BvSGe => Some(BvBound::SignedLower(term, false)),
                    ChcOp::BvSGt => Some(BvBound::SignedLower(term, true)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Flip a BV comparison direction: `(a OP b)` becomes `(b FLIP(OP) a)`.
    fn flip_bv_cmp(op: &ChcOp) -> Option<ChcOp> {
        match op {
            ChcOp::BvULe => Some(ChcOp::BvUGe),
            ChcOp::BvULt => Some(ChcOp::BvUGt),
            ChcOp::BvUGe => Some(ChcOp::BvULe),
            ChcOp::BvUGt => Some(ChcOp::BvULt),
            ChcOp::BvSLe => Some(ChcOp::BvSGe),
            ChcOp::BvSLt => Some(ChcOp::BvSGt),
            ChcOp::BvSGe => Some(ChcOp::BvSLe),
            ChcOp::BvSGt => Some(ChcOp::BvSLt),
            ChcOp::Eq => Some(ChcOp::Eq),
            _ => None,
        }
    }

    /// Pick the tightest BV lower bound by evaluating under model.
    fn pick_tightest_bv_lower(
        &self,
        bounds: &[(ChcExpr, bool)],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(ChcExpr, bool)> {
        bounds
            .iter()
            .max_by_key(|(term, _)| self.eval_bv(term, model).map(|(v, _)| v).unwrap_or(0))
            .cloned()
    }

    /// Pick the tightest BV upper bound by evaluating under model.
    fn pick_tightest_bv_upper(
        &self,
        bounds: &[(ChcExpr, bool)],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(ChcExpr, bool)> {
        bounds
            .iter()
            .min_by_key(|(term, _)| {
                self.eval_bv(term, model)
                    .map(|(v, _)| v)
                    .unwrap_or(u128::MAX)
            })
            .cloned()
    }

    /// Pick the tightest signed BV lower bound (max value in signed order).
    fn pick_tightest_bv_signed_lower(
        &self,
        bounds: &[(ChcExpr, bool)],
        var: &ChcVar,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(ChcExpr, bool)> {
        let w = match &var.sort {
            ChcSort::BitVec(w) => *w,
            _ => return bounds.first().cloned(),
        };
        bounds
            .iter()
            .max_by_key(|(term, _)| {
                self.eval_bv(term, model)
                    .map(|(v, _)| bv_to_signed(v, w))
                    .unwrap_or(i128::MIN)
            })
            .cloned()
    }

    /// Pick the tightest signed BV upper bound (min value in signed order).
    fn pick_tightest_bv_signed_upper(
        &self,
        bounds: &[(ChcExpr, bool)],
        var: &ChcVar,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(ChcExpr, bool)> {
        let w = match &var.sort {
            ChcSort::BitVec(w) => *w,
            _ => return bounds.first().cloned(),
        };
        bounds
            .iter()
            .min_by_key(|(term, _)| {
                self.eval_bv(term, model)
                    .map(|(v, _)| bv_to_signed(v, w))
                    .unwrap_or(i128::MAX)
            })
            .cloned()
    }
}

/// BV bound classification for interval elimination.
pub(super) enum BvBound {
    /// `var >=_u term` (strict if bool is true: `var >_u term`)
    Lower(ChcExpr, bool),
    /// `var <=_u term` (strict if bool is true: `var <_u term`)
    Upper(ChcExpr, bool),
    /// `var >=_s term` (strict if bool is true: `var >_s term`)
    SignedLower(ChcExpr, bool),
    /// `var <=_s term` (strict if bool is true: `var <_s term`)
    SignedUpper(ChcExpr, bool),
    /// `var = term`
    Equality(ChcExpr),
}
