// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounds-from-init hint provider: extracts variable bounds from fact clauses.

use super::*;

/// Provider that extracts bounds from init (fact) clauses.
///
/// For each fact clause `constraint => pred(args)`, extracts bounds like:
/// - `var >= const` -> `canonical_var >= const`
/// - `var <= const` -> `canonical_var <= const`
///
/// These are often valid invariants that hold throughout execution.
pub(crate) struct BoundsFromInitProvider;

impl BoundsFromInitProvider {
    const SOURCE: &'static str = "bounds-from-init-v1";
    const PRIORITY: u16 = 100; // High priority - init bounds are usually valid

    /// Extract atomic bounds from an expression.
    ///
    /// Returns (var_name, bound_expr, is_lower_bound) tuples.
    /// - is_lower_bound=true means var >= bound
    /// - is_lower_bound=false means var <= bound
    pub(super) fn extract_bounds(expr: &ChcExpr) -> Vec<(String, ChcExpr, bool)> {
        let mut bounds = Vec::new();
        Self::extract_bounds_recursive(expr, &mut bounds);
        bounds
    }

    /// Rewritten to use shared `walk_comparison_bounds` traversal (#3786).
    fn extract_bounds_recursive(expr: &ChcExpr, bounds: &mut Vec<(String, ChcExpr, bool)>) {
        use crate::expr::{walk_comparison_bounds, ChcOp};

        walk_comparison_bounds(expr, false, false, &mut |left, op, right| {
            match op {
                // Non-strict: accept any constant bound (Int, Real, Bool)
                ChcOp::Ge => {
                    if let ChcExpr::Var(v) = left {
                        if Self::is_constant(right) {
                            bounds.push((v.name.clone(), right.clone(), true));
                        }
                    }
                    if let ChcExpr::Var(v) = right {
                        if Self::is_constant(left) {
                            bounds.push((v.name.clone(), left.clone(), false));
                        }
                    }
                }
                ChcOp::Le => {
                    if let ChcExpr::Var(v) = left {
                        if Self::is_constant(right) {
                            bounds.push((v.name.clone(), right.clone(), false));
                        }
                    }
                    if let ChcExpr::Var(v) = right {
                        if Self::is_constant(left) {
                            bounds.push((v.name.clone(), left.clone(), true));
                        }
                    }
                }
                // Strict: convert to non-strict (only for Int)
                ChcOp::Gt => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (left, right) {
                        bounds.push((v.name.clone(), ChcExpr::Int(n.saturating_add(1)), true));
                    }
                    if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (left, right) {
                        bounds.push((v.name.clone(), ChcExpr::Int(n.saturating_sub(1)), false));
                    }
                }
                ChcOp::Lt => {
                    if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (left, right) {
                        bounds.push((v.name.clone(), ChcExpr::Int(n.saturating_sub(1)), false));
                    }
                    if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (left, right) {
                        bounds.push((v.name.clone(), ChcExpr::Int(n.saturating_add(1)), true));
                    }
                }
                _ => {}
            }
        });
    }

    fn is_constant(expr: &ChcExpr) -> bool {
        matches!(
            expr,
            ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Bool(_)
        )
    }
}

impl LemmaHintProvider for BoundsFromInitProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        if req.stage != HintStage::Startup {
            return;
        }
        for fact in req.problem.facts() {
            let (pred_id, head_args) = match &fact.head {
                crate::ClauseHead::Predicate(id, args) => (*id, args),
                crate::ClauseHead::False => continue,
            };
            let canonical_vars = match req.canonical_vars(pred_id) {
                Some(vars) => vars,
                None => continue,
            };
            let mut arg_to_canonical: ay_core::kani_compat::DetHashMap<String, &ChcVar> =
                Default::default();
            for (i, arg) in head_args.iter().enumerate() {
                if let Some(canonical) = canonical_vars.get(i) {
                    match arg {
                        ChcExpr::Var(v) => {
                            arg_to_canonical.insert(v.name.clone(), canonical);
                        }
                        expr => {
                            for v in expr.vars() {
                                arg_to_canonical.entry(v.name.clone()).or_insert(canonical);
                            }
                        }
                    }
                }
            }
            if let Some(constraint) = &fact.body.constraint {
                let bounds = Self::extract_bounds(constraint);
                for (var_name, bound_val, is_lower) in bounds {
                    if let Some(canonical_var) = arg_to_canonical.get(&var_name) {
                        let hint_formula = if is_lower {
                            ChcExpr::ge(ChcExpr::var((*canonical_var).clone()), bound_val)
                        } else {
                            ChcExpr::le(ChcExpr::var((*canonical_var).clone()), bound_val)
                        };
                        out.push(LemmaHint::new(
                            pred_id,
                            hint_formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                    }
                }
            }
        }
    }
}

pub(super) static BOUNDS_FROM_INIT_PROVIDER: BoundsFromInitProvider = BoundsFromInitProvider;
