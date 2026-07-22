// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! POB Concretization for non-linear patterns
//!
//! When the global generalizer encounters non-linear patterns (e.g., `k * x`
//! where k is a pattern variable), generalization is unsound. Instead, we
//! concretize the POB into simpler literals using model values.
//!
//! # Algorithm (from Z3 Spacer)
//!
//! 1. **Mark pattern variables**: Scan pattern for `mul(var, expr)` patterns;
//!    mark the non-var side (the coefficient that will be concretized).
//!
//! 2. **Apply to cube**: For each literal in the POB:
//!    - If it's an arithmetic inequality with `+` on LHS
//!    - For each add-term that is marked: emit a bound using model value
//!    - Reconstruct remaining terms with model-evaluated RHS
//!
//! # Example
//!
//! Given pattern with `var * k` (marking k) and POB `2*k + x <= 10` with
//! model `{k=3, x=4}`:
//!
//! ```text
//! Input:  2*k + x <= 10   (k is marked)
//! Output: k <= 3 ∧ x <= 4 (split marked vars, evaluate remainder)
//! ```
//!
//! # References
//!
//! - Z3 spacer_concretize.cpp: `reference/z3/src/muz/spacer/spacer_concretize.cpp`
//! - Design: the development design notes
//!
//! Part of #1874, #1675

use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcVar};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

/// POB Concretizer that simplifies non-linear patterns using model values.
pub(crate) struct PobConcretizer<'a> {
    /// Pattern expression (used to identify marked variables)
    pattern: &'a ChcExpr,
    /// Pattern variables (constants abstracted out during clustering)
    pattern_vars: &'a [ChcVar],
    /// SMT model for evaluation
    model: &'a HashMap<String, SmtValue>,
    /// Marked expressions (non-variable sides of mul in pattern)
    marked: FxHashSet<ChcExpr>,
    /// Expressions already emitted to output (for deduplication)
    emitted: FxHashSet<ChcExpr>,
}

impl<'a> PobConcretizer<'a> {
    /// Create a new concretizer for the given pattern and model.
    pub(crate) fn new(
        pattern: &'a ChcExpr,
        pattern_vars: &'a [ChcVar],
        model: &'a HashMap<String, SmtValue>,
    ) -> Self {
        Self {
            pattern,
            pattern_vars,
            model,
            marked: FxHashSet::default(),
            emitted: FxHashSet::default(),
        }
    }

    /// Concretize a cube (conjunction of literals) using the model.
    ///
    /// Returns `Some(concretized_literals)` if concretization succeeded,
    /// `None` if concretization failed (shouldn't happen in normal use).
    pub(crate) fn apply(&mut self, cube: &[ChcExpr]) -> Option<Vec<ChcExpr>> {
        // Step 1: Mark pattern variables
        self.mark_pattern_vars();

        // Step 2: Apply to each literal
        let mut out = Vec::new();
        for lit in cube {
            self.apply_lit(lit, &mut out);
        }

        Some(out)
    }

    /// Mark expressions in pattern that are non-variable sides of mul.
    ///
    /// For `mul(var, expr)` or `mul(expr, var)`, marks `expr`.
    /// This identifies terms that should be concretized.
    fn mark_pattern_vars(&mut self) {
        self.mark_pattern_vars_inner(self.pattern);
    }

    fn is_pattern_var(&self, expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Var(v) => self.pattern_vars.iter().any(|pv| pv.name == v.name),
            _ => false,
        }
    }

    fn mark_pattern_vars_inner(&mut self, expr: &ChcExpr) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                let e1 = args[0].as_ref();
                let e2 = args[1].as_ref();

                // Mark the "non pattern-var" side of mul(pattern_var, expr).
                //
                // Z3's `is_var` checks for De Bruijn vars (pattern vars) and excludes
                // state variables (which are `app`). In AY both are `ChcExpr::Var`, so we
                // must check membership in the cluster's pattern var set.
                if self.is_pattern_var(e1) && !self.is_pattern_var(e2) {
                    self.marked.insert(e2.clone());
                } else if self.is_pattern_var(e2) && !self.is_pattern_var(e1) {
                    self.marked.insert(e1.clone());
                }

                // Recurse into children
                self.mark_pattern_vars_inner(e1);
                self.mark_pattern_vars_inner(e2);
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    self.mark_pattern_vars_inner(arg);
                }
            }
            ChcExpr::PredicateApp(_, _, args) => {
                for arg in args {
                    self.mark_pattern_vars_inner(arg);
                }
            }
            _ => {}
        });
    }

    /// Apply concretization to a single literal.
    fn apply_lit(&mut self, lit: &ChcExpr, out: &mut Vec<ChcExpr>) {
        // Check for negation
        let (inner, is_neg) = if let ChcExpr::Op(ChcOp::Not, args) = lit {
            if args.len() == 1 {
                (args[0].as_ref(), true)
            } else {
                (lit, false)
            }
        } else {
            (lit, false)
        };

        // Handle arithmetic comparisons with + on LHS
        if let ChcExpr::Op(op, args) = inner {
            if args.len() == 2 {
                let lhs = args[0].as_ref();
                let rhs = args[1].as_ref();

                // Check if this is a comparison with add on LHS
                if matches!(lhs, ChcExpr::Op(ChcOp::Add, _)) && is_numeral(rhs) {
                    match op {
                        ChcOp::Le | ChcOp::Lt => {
                            if !is_neg {
                                self.split_lit_le_lt(lit, out);
                            } else {
                                self.split_lit_ge_gt(lit, out);
                            }
                            return;
                        }
                        ChcOp::Ge | ChcOp::Gt => {
                            if !is_neg {
                                self.split_lit_ge_gt(lit, out);
                            } else {
                                self.split_lit_le_lt(lit, out);
                            }
                            return;
                        }
                        _ => {}
                    }
                }
            }
        }

        // Default: emit literal unchanged
        self.push_out(out, lit.clone());
    }

    /// Split a literal for <= or < comparisons.
    ///
    /// For marked terms: emit `term <= model(term)`
    /// For remaining terms: reconstruct with model-evaluated RHS
    fn split_lit_le_lt(&mut self, lit: &ChcExpr, out: &mut Vec<ChcExpr>) {
        let inner = if let ChcExpr::Op(ChcOp::Not, args) = lit {
            if args.len() == 1 {
                args[0].as_ref()
            } else {
                lit
            }
        } else {
            lit
        };

        let Some(lhs) = (match inner {
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Gt | ChcOp::Ge, args) if args.len() == 2 => {
                Some(args[0].as_ref())
            }
            _ => None,
        }) else {
            self.push_out(out, lit.clone());
            return;
        };

        let ChcExpr::Op(ChcOp::Add, args) = lhs else {
            self.push_out(out, lit.clone());
            return;
        };

        let mut remaining = Vec::new();

        for arg in args {
            if let Some((var, pos)) = self.is_split_var(arg) {
                let val = self.eval(&var);
                let bound = if pos {
                    ChcExpr::le(var, val)
                } else {
                    ChcExpr::ge(var, val)
                };
                self.push_out(out, bound);
            } else {
                remaining.push(arg.clone());
            }
        }

        if remaining.is_empty() {
            return;
        }

        // Nothing was split - emit original literal unchanged
        if remaining.len() == args.len() {
            self.push_out(out, lit.clone());
            return;
        }

        // Create new literal with remaining terms
        let new_lhs = if remaining.len() == 1 {
            remaining.pop().expect("len == 1").as_ref().clone()
        } else {
            ChcExpr::Op(ChcOp::Add, remaining)
        };

        let new_rhs = self.eval(&new_lhs);
        self.push_out(out, ChcExpr::le(new_lhs, new_rhs));
    }

    /// Split a literal for >= or > comparisons.
    fn split_lit_ge_gt(&mut self, lit: &ChcExpr, out: &mut Vec<ChcExpr>) {
        let inner = if let ChcExpr::Op(ChcOp::Not, args) = lit {
            if args.len() == 1 {
                args[0].as_ref()
            } else {
                lit
            }
        } else {
            lit
        };

        let Some(lhs) = (match inner {
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Gt | ChcOp::Ge, args) if args.len() == 2 => {
                Some(args[0].as_ref())
            }
            _ => None,
        }) else {
            self.push_out(out, lit.clone());
            return;
        };

        let ChcExpr::Op(ChcOp::Add, args) = lhs else {
            self.push_out(out, lit.clone());
            return;
        };

        let mut remaining = Vec::new();

        for arg in args {
            if let Some((var, pos)) = self.is_split_var(arg) {
                let val = self.eval(&var);
                let bound = if pos {
                    ChcExpr::ge(var, val)
                } else {
                    ChcExpr::le(var, val)
                };
                self.push_out(out, bound);
            } else {
                remaining.push(arg.clone());
            }
        }

        if remaining.is_empty() {
            return;
        }

        // Nothing was split - emit original literal unchanged
        if remaining.len() == args.len() {
            self.push_out(out, lit.clone());
            return;
        }

        // Create new literal with remaining terms
        let new_lhs = if remaining.len() == 1 {
            remaining.pop().expect("len == 1").as_ref().clone()
        } else {
            ChcExpr::Op(ChcOp::Add, remaining)
        };

        let new_rhs = self.eval(&new_lhs);
        self.push_out(out, ChcExpr::ge(new_lhs, new_rhs));
    }

    /// Check if an expression is a marked variable or coefficient * marked.
    ///
    /// Returns `Some((expr_to_bound, positive))` if this is a split variable,
    /// where `positive` indicates the sign direction.
    fn is_split_var(&self, expr: &Arc<ChcExpr>) -> Option<(ChcExpr, bool)> {
        // Direct marked expression
        if self.marked.contains(expr.as_ref()) {
            return Some((expr.as_ref().clone(), true));
        }

        // coeff * marked_expr
        if let ChcExpr::Op(ChcOp::Mul, args) = expr.as_ref() {
            if args.len() == 2 {
                let e1 = args[0].as_ref();
                let e2 = args[1].as_ref();

                if let ChcExpr::Int(n) = e1 {
                    if self.marked.contains(e2) {
                        return Some((e2.clone(), *n >= 0));
                    }
                }
                if let ChcExpr::Int(n) = e2 {
                    if self.marked.contains(e1) {
                        return Some((e1.clone(), *n >= 0));
                    }
                }
            }
        }

        None
    }

    /// Evaluate an expression using the model.
    fn eval(&self, expr: &ChcExpr) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| {
            match expr {
                ChcExpr::Var(v) => {
                    if let Some(val) = self.model.get(&v.name) {
                        match val {
                            SmtValue::Int(n) => ChcExpr::Int(*n),
                            SmtValue::Bool(b) => ChcExpr::Bool(*b),
                            _ => expr.clone(),
                        }
                    } else {
                        expr.clone()
                    }
                }
                ChcExpr::Int(_) | ChcExpr::Bool(_) | ChcExpr::Real(_, _) => expr.clone(),
                ChcExpr::Op(op, args) => {
                    let evaled: Vec<_> = args.iter().map(|a| self.eval(a)).collect();

                    // Try to simplify arithmetic
                    match op {
                        ChcOp::Add if evaled.iter().all(|e| matches!(e, ChcExpr::Int(_))) => {
                            let sum: Option<i128> = evaled
                                .iter()
                                .map(|e| if let ChcExpr::Int(n) = e { *n } else { 0 })
                                .try_fold(0i128, i128::checked_add);
                            if let Some(sum) = sum {
                                return ChcExpr::Int(sum);
                            }
                        }
                        ChcOp::Mul if evaled.iter().all(|e| matches!(e, ChcExpr::Int(_))) => {
                            let prod: Option<i128> = evaled
                                .iter()
                                .map(|e| if let ChcExpr::Int(n) = e { *n } else { 1 })
                                .try_fold(1i128, i128::checked_mul);
                            if let Some(prod) = prod {
                                return ChcExpr::Int(prod);
                            }
                        }
                        ChcOp::Sub if evaled.len() == 2 => {
                            if let (ChcExpr::Int(a), ChcExpr::Int(b)) = (&evaled[0], &evaled[1]) {
                                if let Some(diff) = a.checked_sub(*b) {
                                    return ChcExpr::Int(diff);
                                }
                            }
                        }
                        ChcOp::Neg if evaled.len() == 1 => {
                            if let ChcExpr::Int(n) = &evaled[0] {
                                if let Some(neg) = n.checked_neg() {
                                    return ChcExpr::Int(neg);
                                }
                            }
                        }
                        _ => {}
                    }

                    ChcExpr::Op(*op, evaled.into_iter().map(Arc::new).collect())
                }
                _ => expr.clone(),
            }
        })
    }

    /// Push an expression to output if not already emitted.
    fn push_out(&mut self, out: &mut Vec<ChcExpr>, expr: ChcExpr) {
        if !self.emitted.contains(&expr) {
            self.emitted.insert(expr.clone());
            out.push(expr);
        }
    }
}

fn is_numeral(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Int(_) | ChcExpr::Real(_, _) => true,
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => is_numeral(args[0].as_ref()),
        _ => false,
    }
}

/// Check if a pattern contains non-linear terms (mul with variable).
///
/// Used by global generalizer to decide when to trigger concretization.
pub(crate) fn has_nonlinear_pattern_vars(pattern: &ChcExpr, pattern_vars: &[ChcVar]) -> bool {
    let is_pattern_var = |e: &ChcExpr| match e {
        ChcExpr::Var(v) => pattern_vars.iter().any(|pv| pv.name == v.name),
        _ => false,
    };

    crate::expr::maybe_grow_expr_stack(|| match pattern {
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            let e1 = args[0].as_ref();
            let e2 = args[1].as_ref();

            // Z3 semantics: multiplication of a pattern var by a non-numeral term.
            if (is_pattern_var(e1) && !is_numeral(e2)) || (is_pattern_var(e2) && !is_numeral(e1)) {
                return true;
            }

            // Recurse
            has_nonlinear_pattern_vars(e1, pattern_vars)
                || has_nonlinear_pattern_vars(e2, pattern_vars)
        }
        ChcExpr::Op(_, args) => args
            .iter()
            .any(|a| has_nonlinear_pattern_vars(a, pattern_vars)),
        ChcExpr::PredicateApp(_, _, args) => args
            .iter()
            .any(|a| has_nonlinear_pattern_vars(a, pattern_vars)),
        ChcExpr::FuncApp(_, _, args) => args
            .iter()
            .any(|a| has_nonlinear_pattern_vars(a, pattern_vars)),
        ChcExpr::ConstArray(_ks, elem) => has_nonlinear_pattern_vars(elem.as_ref(), pattern_vars),
        _ => false,
    })
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
