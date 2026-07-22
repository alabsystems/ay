// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Triple-sum invariant extraction and verification helpers.
//!
//! Zero-constrained variable extraction, init-validity checking, and
//! transition-preservation checking for triple sum invariants (a+b+c = d).

use super::*;

impl PdrSolver {
    /// Extract body arg indices that are constrained to 0 in the clause constraint.
    ///
    /// Looks for patterns like `(= A 0)`, `(= 0 A)` in the constraint, and maps
    /// the variable name to the corresponding body arg index.
    pub(super) fn extract_zero_constrained_vars(
        constraint: &ChcExpr,
        body_args: &[ChcExpr],
    ) -> Vec<usize> {
        let mut result = Vec::new();

        // Collect all (var_name = 0) equalities from the constraint
        let mut zero_vars: Vec<String> = Vec::new();
        Self::collect_zero_equalities(constraint, &mut zero_vars);

        // Map var names to body arg positions
        for var_name in &zero_vars {
            for (idx, arg) in body_args.iter().enumerate() {
                if let ChcExpr::Var(v) = arg {
                    if v.name == *var_name {
                        result.push(idx);
                        break;
                    }
                }
            }
        }

        result
    }

    /// Recursively collect variable names that are equated to 0 in an expression.
    fn collect_zero_equalities(expr: &ChcExpr, out: &mut Vec<String>) {
        match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // (= var 0) or (= 0 var)
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(0)) | (ChcExpr::Int(0), ChcExpr::Var(v)) => {
                        out.push(v.name.clone());
                    }
                    _ => {}
                }
            }
            ChcExpr::Op(ChcOp::And, children) => {
                for child in children {
                    Self::collect_zero_equalities(child, out);
                }
            }
            _ => {}
        }
    }

    /// Check if init constraints imply var_i + var_j + var_k = var_l using SMT.
    pub(in crate::pdr::solver) fn check_triple_sum_holds_at_init(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        var_k: &ChcVar,
        var_l: &ChcVar,
    ) -> bool {
        // Get the fact clauses (init constraints) for this predicate
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find indices
        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let idx_l = canonical_vars.iter().position(|v| v.name == var_l.name);

        let (idx_i, idx_j, idx_k, idx_l) = match (idx_i, idx_j, idx_k, idx_l) {
            (Some(i), Some(j), Some(k), Some(l)) => (i, j, k, l),
            _ => return false,
        };

        let mut found_fact = false;

        // Check all fact clauses
        for clause in self.problem.clauses_defining(predicate) {
            // Only check fact clauses (no body predicates)
            if !clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            found_fact = true;

            // Get the init constraint
            let init_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Get the head arguments for our variables
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let head_k = &head_args[idx_k];
            let head_l = &head_args[idx_l];

            // Build sum: head_i + head_j + head_k
            let sum_expr =
                ChcExpr::add(ChcExpr::add(head_i.clone(), head_j.clone()), head_k.clone());

            // Query: init_constraint AND sum != head_l (should be UNSAT)
            let sum_ne_l = ChcExpr::ne(sum_expr, head_l.clone());
            let query = ChcExpr::and(init_constraint, sum_ne_l);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(200))
            {
                SmtResult::Sat(_) => {
                    // Init does NOT imply the sum equality
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Good, init implies sum = l for this clause
                    continue;
                }
                SmtResult::Unknown => {
                    // Be conservative
                    return false;
                }
            }
        }

        // Only return true if we actually found and checked at least one fact clause
        found_fact
    }

    /// Check if the triple sum var_i + var_j + var_k = var_l is preserved by all transitions.
    pub(in crate::pdr::solver) fn is_triple_sum_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        var_k: &ChcVar,
        var_l: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the indices
        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let idx_l = canonical_vars.iter().position(|v| v.name == var_l.name);

        let (idx_i, idx_j, idx_k, idx_l) = match (idx_i, idx_j, idx_k, idx_l) {
            (Some(i), Some(j), Some(k), Some(l)) => (i, j, k, l),
            _ => return false,
        };

        if self.config.verbose && var_i.name.ends_with("a0") && var_l.name.ends_with("a1") {
            safe_eprintln!("PDR: Triple sum transition check for pred {}: idx_i={}, idx_j={}, idx_k={}, idx_l={}",
                predicate.index(), idx_i, idx_j, idx_k, idx_l);
        }

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        let mut clause_count = 0;
        // Check all transition clauses
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }
            clause_count += 1;
            if self.config.verbose && var_i.name.ends_with("a0") && var_l.name.ends_with("a1") {
                safe_eprintln!(
                    "PDR: Processing clause {} for triple sum check",
                    clause_count
                );
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // For single-predicate body
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            // Get pre and post values
            let pre_i = &body_args[idx_i];
            let pre_j = &body_args[idx_j];
            let pre_k = &body_args[idx_k];
            let pre_l = &body_args[idx_l];

            let post_i = &head_args[idx_i];
            let post_j = &head_args[idx_j];
            let post_k = &head_args[idx_k];
            let post_l = &head_args[idx_l];

            if self.config.verbose && var_i.name.ends_with("a0") && var_l.name.ends_with("a1") {
                safe_eprintln!("PDR: body_args = {:?}", body_args);
                safe_eprintln!("PDR: head_args = {:?}", head_args);
                safe_eprintln!("PDR: pre_i = {:?}", pre_i);
                safe_eprintln!("PDR: pre_j = {:?}", pre_j);
                safe_eprintln!("PDR: pre_k = {:?}", pre_k);
                safe_eprintln!("PDR: pre_l = {:?}", pre_l);
            }

            // Check: post_i + post_j + post_k = post_l given pre_i + pre_j + pre_k = pre_l and constraint
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let pre_sum = ChcExpr::add(ChcExpr::add(pre_i.clone(), pre_j.clone()), pre_k.clone());
            let post_sum =
                ChcExpr::add(ChcExpr::add(post_i.clone(), post_j.clone()), post_k.clone());

            // The invariant should preserve: post_sum = post_l given pre_sum = pre_l
            let pre_invariant = ChcExpr::eq(pre_sum, pre_l.clone());
            let post_invariant = ChcExpr::ne(post_sum, post_l.clone());

            // Extract OR cases for case-splitting to work around AY's SMT solver limitation
            // with OR constraints returning Unknown instead of UNSAT
            let or_cases = Self::extract_or_cases_from_constraint(&clause_constraint);

            if self.config.verbose && var_i.name.ends_with("a0") && var_l.name.ends_with("a1") {
                safe_eprintln!(
                    "PDR: Triple sum extracted {} OR cases from constraint",
                    or_cases.len()
                );
            }

            // For each OR case, check if the invariant is preserved
            // ALL cases must return UNSAT for the invariant to be valid
            let mut all_cases_unsat = true;
            for (case_idx, case_constraint) in or_cases.iter().enumerate() {
                // Query: case_constraint AND pre_invariant AND NOT post_invariant (should be UNSAT)
                let query = ChcExpr::and(
                    ChcExpr::and(case_constraint.clone(), pre_invariant.clone()),
                    post_invariant.clone(),
                );

                if self.config.verbose && var_i.name.ends_with("a0") && var_l.name.ends_with("a1") {
                    safe_eprintln!("PDR: Triple sum case {} query: {}", case_idx, query);
                }

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                {
                    SmtResult::Sat(model) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Triple sum ({} + {} + {} = {}) is NOT preserved by transition (case {})",
                                var_i.name, var_j.name, var_k.name, var_l.name, case_idx
                            );
                            safe_eprintln!("  pre_sum = {} + {} + {}", pre_i, pre_j, pre_k);
                            safe_eprintln!("  post_sum = {} + {} + {}", post_i, post_j, post_k);
                            safe_eprintln!("  pre_l = {}, post_l = {}", pre_l, post_l);
                            safe_eprintln!("  SAT model: {:?}", model);
                        }
                        return false;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // This case is good, continue to next case
                        if self.config.verbose
                            && var_i.name.ends_with("a0")
                            && var_l.name.ends_with("a1")
                        {
                            safe_eprintln!(
                                "PDR: Triple sum case {} returned UNSAT (good)",
                                case_idx
                            );
                        }
                        continue;
                    }
                    SmtResult::Unknown => {
                        // SMT returned Unknown - try algebraic verification as fallback
                        // Check if delta_sum = delta_l by computing symbolic deltas
                        if Self::verify_triple_sum_algebraically(
                            pre_i,
                            pre_j,
                            pre_k,
                            pre_l,
                            post_i,
                            post_j,
                            post_k,
                            post_l,
                            case_constraint,
                        ) {
                            if self.config.verbose
                                && var_i.name.ends_with("a0")
                                && var_l.name.ends_with("a1")
                            {
                                safe_eprintln!(
                                    "PDR: Triple sum case {} verified algebraically (UNSAT)",
                                    case_idx
                                );
                            }
                            continue;
                        }
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Triple sum ({} + {} + {} = {}) SMT unknown on transition check (case {})",
                                var_i.name, var_j.name, var_k.name, var_l.name, case_idx
                            );
                        }
                        all_cases_unsat = false;
                        break;
                    }
                }
            }

            if !all_cases_unsat {
                return false;
            }
        }

        // All self-loop transitions preserve the triple sum.
        // But if zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }
}
