// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MBQI-style term substitution for unprojectable variables.
//!
//! Per Z3's `index_term_finder` in spacer_util.cpp:854-907, we collect
//! candidate terms from the formula and find equivalent terms for variables
//! that cannot be eliminated by bound-based projection.

use crate::{ChcExpr, ChcOp, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::Mbp;

impl Mbp {
    /// Collect candidate terms for MBQI-style substitution (#892).
    ///
    /// Per Z3's `index_term_finder` in spacer_util.cpp:854-907, we collect:
    /// - Arguments of equality operations
    /// - Arguments of arithmetic operations
    /// - Subterms from function applications
    ///
    /// These are terms that could potentially replace a variable if they
    /// evaluate to the same value under the model.
    pub(super) fn collect_candidate_terms(formula: &ChcExpr) -> Vec<ChcExpr> {
        let mut terms = Vec::new();
        Self::collect_candidate_terms_inner(formula, &mut terms);
        terms
    }

    fn collect_candidate_terms_inner(expr: &ChcExpr, terms: &mut Vec<ChcExpr>) {
        crate::expr::maybe_grow_expr_stack(|| {
            if crate::expr::ExprDepthGuard::check().is_none() {
                return;
            }
            match expr {
                ChcExpr::Int(_) => {
                    // Constants are trivially usable but not interesting for generalization
                }
                ChcExpr::Var(_) => {
                    // Variables themselves are candidates
                    terms.push(expr.clone());
                }
                ChcExpr::Op(op, args) => {
                    // For equality/comparison, collect both sides as candidate terms
                    if matches!(
                        op,
                        ChcOp::Eq | ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Ne
                    ) {
                        for arg in args {
                            terms.push((**arg).clone());
                        }
                    }
                    // For arithmetic ops, the result is also a candidate term
                    if matches!(op, ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Neg) {
                        terms.push(expr.clone());
                    }
                    // Recurse into subexpressions
                    for arg in args {
                        Self::collect_candidate_terms_inner(arg, terms);
                    }
                }
                ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, _) => {}
                ChcExpr::PredicateApp(_, _, args) => {
                    for arg in args {
                        Self::collect_candidate_terms_inner(arg, terms);
                    }
                }
                ChcExpr::FuncApp(_, _, args) => {
                    terms.push(expr.clone());
                    for arg in args {
                        Self::collect_candidate_terms_inner(arg, terms);
                    }
                }
                ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_)
                | ChcExpr::ConstArray(_, _) => {}
            }
        })
    }

    /// Find an equivalent term for a variable using MBQI-style substitution (#892).
    ///
    /// Per Z3's `mbqi_project_var` in spacer_util.cpp:854-907:
    /// - Get model value of variable
    /// - Find a term in candidates that evaluates to the same value
    /// - The term must NOT contain the variable (no cyclic substitution)
    ///
    /// Returns `Some(term)` if found, `None` if we should fall back to model value.
    pub(super) fn find_equivalent_term(
        &self,
        var: &ChcVar,
        candidates: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        // Get the model value of the variable
        let var_value = match model.get(&var.name) {
            Some(SmtValue::Int(n)) => *n,
            _ => return None, // No model value, can't find equivalent
        };

        // Search for a term that:
        // 1. Evaluates to the same value under model
        // 2. Does not contain the variable
        // 3. Is more general than just a constant (contains other variables)
        for term in candidates {
            // Skip if term contains the variable we're eliminating
            if term.contains_var_name(&var.name) {
                continue;
            }

            // Skip bare constants - we want something more general
            if matches!(term, ChcExpr::Int(_)) {
                continue;
            }

            // Skip the variable itself
            if let ChcExpr::Var(v) = term {
                if v == var {
                    continue;
                }
            }

            // Evaluate term under model
            if let Some(term_value) = self.eval_arith(term, model) {
                if term_value == var_value {
                    // Found an equivalent term!
                    return Some(term.clone());
                }
            }
        }

        None
    }
}
