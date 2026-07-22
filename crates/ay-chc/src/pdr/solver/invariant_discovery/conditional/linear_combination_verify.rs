// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification helpers for linear combination and step-bounded invariants.

use super::*;

impl PdrSolver {
    /// Verify that linear combination bound is preserved by transitions
    pub(in crate::pdr::solver) fn verify_linear_combination_preserved(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        var_c: &ChcVar,
        coeff: i128,
        bound: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);
        let c_idx = canonical_vars.iter().position(|v| v.name == var_c.name);

        let (a_idx, b_idx, c_idx) = match (a_idx, b_idx, c_idx) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            _ => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Collect clauses upfront to avoid borrowing self.problem across
        // the mutable self.check_sat_via_executor_backend() call (#7984).
        let clauses: Vec<_> = self.problem.clauses_defining(predicate).cloned().collect();
        for clause in &clauses {
            if clause.body.predicates.is_empty() {
                continue;
            }
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let pre_a = &body_args[a_idx];
            let pre_b = &body_args[b_idx];
            let pre_c = &body_args[c_idx];
            let post_a = &head_args[a_idx];
            let post_b = &head_args[b_idx];
            let post_c = &head_args[c_idx];

            // Pre invariant: a + coeff*c < b + bound
            let pre_lhs = if coeff == 1 {
                ChcExpr::add(pre_a.clone(), pre_c.clone())
            } else {
                ChcExpr::add(
                    pre_a.clone(),
                    ChcExpr::mul(ChcExpr::Int(coeff), pre_c.clone()),
                )
            };
            let pre_rhs = ChcExpr::add(pre_b.clone(), ChcExpr::Int(bound));
            let pre_invariant = ChcExpr::lt(pre_lhs, pre_rhs);

            // Post violation: a' + coeff*c' >= b' + bound
            let post_lhs = if coeff == 1 {
                ChcExpr::add(post_a.clone(), post_c.clone())
            } else {
                ChcExpr::add(
                    post_a.clone(),
                    ChcExpr::mul(ChcExpr::Int(coeff), post_c.clone()),
                )
            };
            let post_rhs = ChcExpr::add(post_b.clone(), ChcExpr::Int(bound));
            let post_violation = ChcExpr::ge(post_lhs, post_rhs);

            let mut query = ChcExpr::and(pre_invariant, post_violation);
            if let Some(c) = &clause.body.constraint {
                query = ChcExpr::and(c.clone(), query);
            }

            // #7984: Use persistent executor backend for integer arithmetic.
            match self.check_sat_via_executor_backend(&query) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => return false,
            }
        }

        // If zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }

    /// Extract the "other" variable from a guard pattern: NOT (other <= var) meaning var < other
    pub(in crate::pdr::solver) fn extract_lt_guard_other_var(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<String> {
        match constraint {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                // NOT (other <= var) means var < other
                if let ChcExpr::Op(ChcOp::Le, inner_args) = args[0].as_ref() {
                    if inner_args.len() == 2 {
                        // (<= other var) where var matches var_name
                        if let (ChcExpr::Var(other_var), ChcExpr::Var(var)) =
                            (inner_args[0].as_ref(), inner_args[1].as_ref())
                        {
                            if var.name == var_name {
                                return Some(other_var.name.clone());
                            }
                        }
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::And, args) => {
                // Search conjuncts
                for arg in args {
                    if let Some(other) = Self::extract_lt_guard_other_var(arg, var_name) {
                        return Some(other);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Check if step-bounded invariant var_i < var_j + step is valid at init
    pub(in crate::pdr::solver) fn is_step_bounded_valid_at_init(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        step: i128,
    ) -> bool {
        // Get init values
        let init_values = self.get_init_values(predicate);

        let bounds_i = init_values.get(&var_i.name);
        let bounds_j = init_values.get(&var_j.name);

        match (bounds_i, bounds_j) {
            (Some(bi), Some(bj)) => {
                // Need max(var_i) < min(var_j) + step for the invariant to hold
                // i.e., bi.max < bj.min + step
                bi.max < bj.min + step
            }
            _ => {
                // No init bounds - verify using SMT
                // Check: init_constraint => var_i < var_j + step
                let canonical_vars = match self.canonical_vars(predicate) {
                    Some(v) => v.to_vec(),
                    None => return false,
                };

                // Collect fact clauses upfront to avoid borrowing self.problem across
                // the mutable self.check_sat_via_executor_backend() call (#7984).
                let clauses: Vec<_> = self.problem.clauses_defining(predicate).cloned().collect();
                for clause in &clauses {
                    if !clause.body.predicates.is_empty() {
                        continue;
                    }

                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                        crate::ClauseHead::False => continue,
                    };

                    if head_args.len() != canonical_vars.len() {
                        continue;
                    }

                    // Build query: init_constraint AND NOT (var_i < var_j + step)
                    // If UNSAT, the invariant holds at init
                    let var_i_idx = canonical_vars.iter().position(|v| v.name == var_i.name);
                    let var_j_idx = canonical_vars.iter().position(|v| v.name == var_j.name);

                    if let (Some(i_idx), Some(j_idx)) = (var_i_idx, var_j_idx) {
                        let val_i = &head_args[i_idx];
                        let val_j = &head_args[j_idx];

                        // var_i >= var_j + step (negation of var_i < var_j + step)
                        let bound_expr = ChcExpr::add(val_j.clone(), ChcExpr::Int(step));
                        let violation = ChcExpr::ge(val_i.clone(), bound_expr);

                        let query = if let Some(c) = &clause.body.constraint {
                            ChcExpr::and(c.clone(), violation)
                        } else {
                            violation
                        };

                        // #7984: Use persistent executor backend for integer arithmetic.
                        match self.check_sat_via_executor_backend(&query) {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                // Invariant holds at init
                            }
                            _ => {
                                // Invariant may not hold at init
                                return false;
                            }
                        }
                    }
                }
                true
            }
        }
    }

    /// Check if step-bounded invariant var_i < var_j + step is preserved by transitions
    pub(in crate::pdr::solver) fn is_step_bounded_preserved(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        step: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_i_idx = canonical_vars.iter().position(|v| v.name == var_i.name);
        let var_j_idx = canonical_vars.iter().position(|v| v.name == var_j.name);

        let (i_idx, j_idx) = match (var_i_idx, var_j_idx) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Collect clauses upfront to avoid borrowing self.problem across
        // the mutable self.check_sat_via_executor_backend() call (#7984).
        let clauses: Vec<_> = self.problem.clauses_defining(predicate).cloned().collect();
        for clause in &clauses {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only handle single-predicate bodies for now
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            // Build the preservation check:
            // pre_var_i < pre_var_j + step AND constraint => post_var_i < post_var_j + step
            // Equivalent to checking: pre_var_i < pre_var_j + step AND constraint AND post_var_i >= post_var_j + step is UNSAT

            let pre_var_i = &body_args[i_idx];
            let pre_var_j = &body_args[j_idx];
            let post_var_i = &head_args[i_idx];
            let post_var_j = &head_args[j_idx];

            // pre_invariant: pre_var_i < pre_var_j + step
            let pre_bound = ChcExpr::add(pre_var_j.clone(), ChcExpr::Int(step));
            let pre_invariant = ChcExpr::lt(pre_var_i.clone(), pre_bound);

            // post_violation: post_var_i >= post_var_j + step
            let post_bound = ChcExpr::add(post_var_j.clone(), ChcExpr::Int(step));
            let post_violation = ChcExpr::ge(post_var_i.clone(), post_bound);

            // Build query: pre_invariant AND constraint AND post_violation
            let mut query = ChcExpr::and(pre_invariant, post_violation);
            if let Some(c) = &clause.body.constraint {
                query = ChcExpr::and(c.clone(), query);
            }

            // #7984: Use persistent executor backend for integer arithmetic.
            match self.check_sat_via_executor_backend(&query) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Preservation holds for this transition
                }
                _ => {
                    // Preservation may not hold
                    return false;
                }
            }
        }

        // If zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }
}
