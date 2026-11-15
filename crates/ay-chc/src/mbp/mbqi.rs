// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MBQI-style term substitution for unprojectable variables.
//!
//! Per Z3's `index_term_finder` in spacer_util.cpp:854-907, we collect
//! candidate terms from the formula and find equivalent terms for variables
//! that cannot be eliminated by bound-based projection.

use std::sync::Arc;

use crate::expr::dag::{eval_memo, has_children};
use crate::{ChcExpr, ChcOp, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::Mbp;

/// Child visits [`CandidateWalk`] makes before it starts skipping shared
/// children it has already explored (keeps small formulas free of hashing).
const CANDIDATE_PLAIN_VISITS: usize = 4096;

/// The candidate-term walk of [`Mbp::collect_candidate_terms`], DAG-linear
/// (WP-F): a shared child `Arc` is explored once per depth class. Nodes stay
/// alive (borrowed from the formula) for the whole walk, so an address keys
/// one node.
struct CandidateWalk {
    terms: Vec<ChcExpr>,
    plain_visits_left: usize,
    /// Child `Arc` address -> smallest depth at which it was fully explored.
    explored_at: FxHashMap<*const ChcExpr, usize>,
}

impl CandidateWalk {
    fn visit(&mut self, expr: &ChcExpr, depth: usize) {
        crate::expr::maybe_grow_expr_stack(|| {
            if crate::expr::ExprDepthGuard::check().is_none() {
                return;
            }
            match expr {
                ChcExpr::ArrayLambda(lambda) => {
                    for value in lambda.captures() {
                        self.visit_child(value, depth + 1);
                    }
                }
                ChcExpr::Int(_) => {
                    // Constants are trivially usable but not interesting for generalization
                }
                ChcExpr::Var(_) => {
                    // Variables themselves are candidates
                    self.terms.push(expr.clone());
                }
                ChcExpr::Op(op, args) => {
                    // For equality/comparison, collect both sides as candidate terms
                    if matches!(
                        op,
                        ChcOp::Eq | ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Ne
                    ) {
                        for arg in args {
                            self.terms.push((**arg).clone());
                        }
                    }
                    // For arithmetic ops, the result is also a candidate term
                    if matches!(op, ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Neg) {
                        self.terms.push(expr.clone());
                    }
                    // Recurse into subexpressions
                    for arg in args {
                        self.visit_child(arg, depth + 1);
                    }
                }
                ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, _) => {}
                ChcExpr::PredicateApp(_, _, args) => {
                    for arg in args {
                        self.visit_child(arg, depth + 1);
                    }
                }
                ChcExpr::FuncApp(_, _, args) => {
                    self.terms.push(expr.clone());
                    for arg in args {
                        self.visit_child(arg, depth + 1);
                    }
                }
                ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_)
                | ChcExpr::ConstArray(_, _) => {}
            }
        })
    }

    /// Visit `child` unless it was already explored at this depth or a
    /// smaller one: the earlier exploration pushed everything this one would
    /// (the same subtree under the same or a looser depth cut-off), and the
    /// only consumer, [`Mbp::find_equivalent_term`], returns the FIRST
    /// candidate that fits, so dropping later duplicates changes no answer.
    /// A leaf is pushed once per distinct `Arc`.
    fn visit_child(&mut self, child: &Arc<ChcExpr>, depth: usize) {
        if self.plain_visits_left > 0 {
            self.plain_visits_left -= 1;
            self.visit(child, depth);
            return;
        }
        let key = Arc::as_ptr(child);
        if let Some(&explored) = self.explored_at.get(&key) {
            if explored <= depth || !has_children(child) {
                return;
            }
        }
        self.explored_at.insert(key, depth);
        self.visit(child, depth);
    }
}

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
    ///
    /// DAG-linear (WP-F): the tree walk pushed one entry per OCCURRENCE, which
    /// on a shared transition relation is its tree size (PDKIND's projection
    /// ran the process out of memory in 3 s on `token_ring.1`). The walk now
    /// explores a shared child once per depth class ([`CandidateWalk`]); the
    /// first candidate that [`Self::find_equivalent_term`] accepts is the same.
    pub(super) fn collect_candidate_terms(formula: &ChcExpr) -> Vec<ChcExpr> {
        let mut walk = CandidateWalk {
            terms: Vec::new(),
            plain_visits_left: CANDIDATE_PLAIN_VISITS,
            explored_at: FxHashMap::default(),
        };
        walk.visit(formula, 0);
        walk.terms
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

        // One evaluation memo for every candidate: they are terms of one
        // formula, evaluated under one model (WP-F).
        let _memo = eval_memo::EvalScope::enter(candidates.iter(), model);

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
