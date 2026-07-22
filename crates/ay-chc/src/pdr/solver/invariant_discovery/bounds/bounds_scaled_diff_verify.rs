// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation and helper methods for scaled difference bound invariants.
//!
//! Companion to `bounds_scaled_diff.rs`: contains the init/preservation checks
//! and coefficient/constant extraction helpers, while the parent file retains
//! the top-level discovery orchestrator.

use super::*;

impl PdrSolver {
    /// Extract multiplication coefficients from an expression.
    /// E.g., `(* 5 C)` yields 5, `(* (- 1) B)` yields -1.
    pub(in crate::pdr::solver) fn collect_mul_coefficients(
        expr: &ChcExpr,
        coefficients: &mut Vec<i128>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(k), ChcExpr::Var(_)) | (ChcExpr::Var(_), ChcExpr::Int(k)) => {
                        coefficients.push(*k);
                    }
                    _ => {}
                }
                for a in args {
                    Self::collect_mul_coefficients(a, coefficients);
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_mul_coefficients(a, coefficients);
                }
            }
            _ => {}
        });
    }

    /// Extract equality constants from a constraint expression.
    /// E.g., `(= 10 v_0)` yields 10, `(and (= 10 v_0) (= 20 v_1))` yields 10, 20.
    /// Used to derive scale factors from init values (#5480).
    pub(in crate::pdr::solver) fn collect_equality_constants(
        expr: &ChcExpr,
        constants: &mut Vec<i128>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(k), ChcExpr::Var(_)) | (ChcExpr::Var(_), ChcExpr::Int(k)) => {
                        constants.push(*k);
                    }
                    _ => {}
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_equality_constants(a, constants);
                }
            }
            _ => {}
        });
    }

    /// Check if B - k*A >= c holds for all states injected by incoming
    /// inter-predicate transitions into a derived predicate (#5480).
    ///
    /// For predicates without fact clauses, initial states come from clauses
    /// where another predicate maps to this one. We verify the bound holds
    /// on the head args given the clause constraint and source invariants.
    pub(in crate::pdr::solver) fn is_scaled_diff_bound_incoming_valid(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        k: i128,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        let mut checked_any = false;

        for clause in self.problem.clauses_defining(predicate) {
            // Skip self-loops (handled by preservation) and facts
            if clause.body.predicates.is_empty() {
                continue;
            }
            if clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == predicate {
                continue;
            }

            // This is an incoming inter-predicate transition
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any = true;

            let expr_a = &head_args[var_a_idx];
            let expr_b = &head_args[var_b_idx];

            // Build B_head - k * A_head < c (violation)
            let diff_expr = ChcExpr::sub(
                expr_b.clone(),
                ChcExpr::mul(ChcExpr::Int(k), expr_a.clone()),
            );
            let violation = ChcExpr::lt(diff_expr, ChcExpr::Int(c));

            // Clause constraint
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let mut parts: Vec<ChcExpr> = vec![clause_constraint, violation];

            // Add source predicate invariants from frame[1]
            for (body_pred, body_args) in &clause.body.predicates {
                if let Some(f1) = self.cumulative_frame_constraint(1, *body_pred) {
                    if let Some(f1_on_body) = self.apply_to_args(*body_pred, &f1, body_args) {
                        parts.push(f1_on_body);
                    }
                }
            }

            let query = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));

            self.smt.reset();
            let result = self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500));
            match result {
                SmtResult::Sat(_) => return false, // Bound violated by incoming transition
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        // Must have checked at least one incoming transition
        checked_any
    }

    /// Check if B - k*A >= c holds for all init states of the predicate.
    pub(in crate::pdr::solver) fn is_scaled_diff_bound_init_valid(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        k: i128,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        // Check all fact clauses
        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get the expressions for A and B from the fact clause
            let expr_a = &head_args[var_a_idx];
            let expr_b = &head_args[var_b_idx];

            // Build query: constraint AND B - k*A < c (violation of the bound)
            let diff_expr = ChcExpr::sub(
                expr_b.clone(),
                ChcExpr::mul(ChcExpr::Int(k), expr_a.clone()),
            );
            let violation = ChcExpr::lt(diff_expr, ChcExpr::Int(c));
            let query = ChcExpr::and(constraint, violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false, // Bound violated at init
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        true
    }

    /// Check if B - k*A >= c is preserved by all transitions.
    pub(in crate::pdr::solver) fn is_scaled_diff_bound_preserved(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        k: i128,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        // Cache per-predicate invariants at level 1 to allow relative inductiveness checks.
        // This is needed for cases like dillig12 where `D = 2*C` is only preserved assuming
        // the already-learned equality `A = B` (see #1411).
        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses (self-loops)
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only check self-loops for now
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            // Get pre and post expressions for A and B
            let pre_a = &body_args[var_a_idx];
            let pre_b = &body_args[var_b_idx];
            let post_a = &head_args[var_a_idx];
            let post_b = &head_args[var_b_idx];

            // Pre-condition: B - k*A >= c
            let pre_diff =
                ChcExpr::sub(pre_b.clone(), ChcExpr::mul(ChcExpr::Int(k), pre_a.clone()));
            let pre_cond = ChcExpr::ge(pre_diff, ChcExpr::Int(c));

            // Post-condition: B' - k*A' >= c
            let post_diff = ChcExpr::sub(
                post_b.clone(),
                ChcExpr::mul(ChcExpr::Int(k), post_a.clone()),
            );
            let post_violation = ChcExpr::lt(post_diff, ChcExpr::Int(c));

            // Query: pre_cond AND f1(body_args) AND clause_constraint AND post_violation should be UNSAT
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Build parts: pre_cond, clause_constraint, and optionally F1 on body
            let mut parts: Vec<ChcExpr> = vec![pre_cond, clause_constraint];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(base, post_violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(ref model) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Scaled diff bound {} - {}*{} >= {} NOT preserved (f1={}, clause_constraint_len={})",
                            var_b.name,
                            k,
                            var_a.name,
                            c,
                            f1_constraint.is_some(),
                            clause.body.constraint.as_ref().map_or(0, |c| c.to_string().len()),
                        );
                        if var_b.name.contains("a3") && var_a.name.contains("a2") && k == 2 {
                            safe_eprintln!(
                                "PDR: D13-diag: query={}, model={:?}",
                                query,
                                model
                                    .iter()
                                    .map(|(k, v)| format!("{k}={v:?}"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            );
                        }
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => {
                    // ITE case-split fallback (#5480): transitions with
                    // ite(mod(B,2)=0, ...) cause Unknown because the SMT solver
                    // can't handle nonlinear mod. Case-splitting on the ITE
                    // condition eliminates the mod, making each branch a pure
                    // linear query. Sound: if neither branch admits a violation,
                    // the bound holds for all states.
                    let mut ite_conditions = Vec::new();
                    Self::extract_ite_conditions(&query, &mut ite_conditions);
                    if !ite_conditions.is_empty() {
                        let cond = &ite_conditions[0];
                        let query_true = ChcExpr::and(query.clone(), cond.clone());
                        self.smt.reset();
                        let case_true_ok = matches!(
                            self.smt.check_sat_with_timeout(
                                &query_true,
                                std::time::Duration::from_millis(500),
                            ),
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        );
                        if case_true_ok {
                            let query_false =
                                ChcExpr::and(query.clone(), ChcExpr::not(cond.clone()));
                            self.smt.reset();
                            if matches!(
                                self.smt.check_sat_with_timeout(
                                    &query_false,
                                    std::time::Duration::from_millis(500),
                                ),
                                SmtResult::Unsat
                                    | SmtResult::UnsatWithCore(_)
                                    | SmtResult::UnsatWithFarkas(_)
                            ) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Scaled diff bound {} - {}*{} >= {} preserved via ITE case-split",
                                        var_b.name, k, var_a.name, c
                                    );
                                }
                                continue;
                            }
                        }
                    }
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
