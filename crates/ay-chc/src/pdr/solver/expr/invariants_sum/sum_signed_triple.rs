// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Signed triple-sum invariant discovery.
//!
//! Discovers invariants of the form `a + b - c = d` (signed linear combinations
//! of 4 variables) that are preserved by transitions. This extends the
//! `discover_triple_sum_invariants` (which only finds `a + b + c = d`) to
//! handle cases where one variable is subtracted.
//!
//! Example: `bouncy_three_counters_merged` needs `D = A + C - B`.

use super::*;

impl PdrSolver {
    /// Discover signed triple-sum invariants: `var_i + var_j - var_k = var_l`.
    ///
    /// For each predicate with 4+ integer variables, tries all 4-tuples (i, j, k, l)
    /// where i < j, k != i, k != j, l != i, l != j, l != k, checking:
    /// 1. `init[i] + init[j] - init[k] = init[l]`
    /// 2. Preservation by all self-loop transitions
    pub(in crate::pdr::solver) fn discover_signed_triple_sum_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if canonical_vars.len() < 4 {
                continue;
            }

            let int_var_count = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int))
                .count();
            if int_var_count > 10 {
                continue;
            }

            let init_values = self.get_init_values(pred.id);
            let n = canonical_vars.len();

            // Try all (i, j, k, l) where i < j, k and l distinct from each other and from {i,j}
            for i in 0..n {
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..n {
                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];
                    if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                        continue;
                    }

                    for k in 0..n {
                        if k == i || k == j {
                            continue;
                        }
                        let var_k = &canonical_vars[k];
                        if !matches!(var_k.sort, ChcSort::Int) {
                            continue;
                        }

                        for (l, var_l) in canonical_vars.iter().enumerate().take(n) {
                            if l == i || l == j || l == k {
                                continue;
                            }
                            if !matches!(var_l.sort, ChcSort::Int) {
                                continue;
                            }

                            // Check init: var_i + var_j - var_k = var_l
                            let holds_at_init = match (
                                init_values.get(&var_i.name),
                                init_values.get(&var_j.name),
                                init_values.get(&var_k.name),
                                init_values.get(&var_l.name),
                            ) {
                                (Some(bi), Some(bj), Some(bk), Some(bl))
                                    if bi.min == bi.max
                                        && bj.min == bj.max
                                        && bk.min == bk.max
                                        && bl.min == bl.max =>
                                {
                                    bi.min + bj.min - bk.min == bl.min
                                }
                                _ => self.check_signed_triple_sum_holds_at_init(
                                    pred.id, var_i, var_j, var_k, var_l,
                                ),
                            };

                            if !holds_at_init {
                                continue;
                            }

                            // Check preservation by transitions
                            if !self
                                .is_signed_triple_sum_preserved(pred.id, var_i, var_j, var_k, var_l)
                            {
                                continue;
                            }

                            // Found a valid signed triple sum invariant
                            let inv = ChcExpr::eq(
                                ChcExpr::sub(
                                    ChcExpr::add(
                                        ChcExpr::var(var_i.clone()),
                                        ChcExpr::var(var_j.clone()),
                                    ),
                                    ChcExpr::var(var_k.clone()),
                                ),
                                ChcExpr::var(var_l.clone()),
                            );

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered signed triple sum invariant for pred {}: {} + {} - {} = {}",
                                    pred.id.index(),
                                    var_i.name,
                                    var_j.name,
                                    var_k.name,
                                    var_l.name
                                );
                            }

                            self.add_discovered_invariant_algebraic(pred.id, inv, 1);
                        }
                    }
                }
            }
        }
    }

    /// Check if init constraints imply var_i + var_j - var_k = var_l using SMT.
    fn check_signed_triple_sum_holds_at_init(
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

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let idx_l = canonical_vars.iter().position(|v| v.name == var_l.name);

        let (idx_i, idx_j, idx_k, idx_l) = match (idx_i, idx_j, idx_k, idx_l) {
            (Some(i), Some(j), Some(k), Some(l)) => (i, j, k, l),
            _ => return false,
        };

        let mut found_fact = false;

        for clause in self.problem.clauses_defining(predicate) {
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

            let init_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let head_k = &head_args[idx_k];
            let head_l = &head_args[idx_l];

            // sum = head_i + head_j - head_k
            let sum_expr =
                ChcExpr::sub(ChcExpr::add(head_i.clone(), head_j.clone()), head_k.clone());

            let sum_ne_l = ChcExpr::ne(sum_expr, head_l.clone());
            let query = ChcExpr::and(init_constraint, sum_ne_l);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(200))
            {
                SmtResult::Sat(_) => return false,
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue;
                }
                SmtResult::Unknown => return false,
            }
        }

        found_fact
    }

    /// Check if var_i + var_j - var_k = var_l is preserved by all self-loop transitions.
    fn is_signed_triple_sum_preserved(
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

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let idx_l = canonical_vars.iter().position(|v| v.name == var_l.name);

        let (idx_i, idx_j, idx_k, idx_l) = match (idx_i, idx_j, idx_k, idx_l) {
            (Some(i), Some(j), Some(k), Some(l)) => (i, j, k, l),
            _ => return false,
        };

        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;

            let pre_i = &body_args[idx_i];
            let pre_j = &body_args[idx_j];
            let pre_k = &body_args[idx_k];
            let pre_l = &body_args[idx_l];

            let post_i = &head_args[idx_i];
            let post_j = &head_args[idx_j];
            let post_k = &head_args[idx_k];
            let post_l = &head_args[idx_l];

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let pre_sum = ChcExpr::sub(ChcExpr::add(pre_i.clone(), pre_j.clone()), pre_k.clone());
            let post_sum =
                ChcExpr::sub(ChcExpr::add(post_i.clone(), post_j.clone()), post_k.clone());

            let pre_invariant = ChcExpr::eq(pre_sum, pre_l.clone());
            let post_invariant_violated = ChcExpr::ne(post_sum.clone(), post_l.clone());

            // Case-split on OR clauses (same approach as triple sum)
            let or_cases = Self::extract_or_cases_from_constraint(&clause_constraint);

            let mut all_cases_unsat = true;
            for case_constraint in &or_cases {
                let query = ChcExpr::and(
                    ChcExpr::and(case_constraint.clone(), pre_invariant.clone()),
                    post_invariant_violated.clone(),
                );

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                {
                    SmtResult::Sat(_) => return false,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => {
                        // Try algebraic verification as fallback
                        if self.verify_signed_triple_sum_algebraically(
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
                            continue;
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

        if !checked_any_self_loop {
            return false;
        }
        true
    }

    /// Algebraically verify that a signed triple sum is preserved by a transition case.
    ///
    /// Checks if `(post_i + post_j - post_k) - (pre_i + pre_j - pre_k) = post_l - pre_l`
    /// by extracting delta expressions from the case constraint.
    fn verify_signed_triple_sum_algebraically(
        &self,
        pre_i: &ChcExpr,
        pre_j: &ChcExpr,
        pre_k: &ChcExpr,
        pre_l: &ChcExpr,
        post_i: &ChcExpr,
        post_j: &ChcExpr,
        post_k: &ChcExpr,
        post_l: &ChcExpr,
        case_constraint: &ChcExpr,
    ) -> bool {
        // Extract deltas: for each var, compute post - pre
        let delta = |post: &ChcExpr, pre: &ChcExpr| -> Option<i128> {
            Self::extract_constant_delta_from_constraint(post, pre, case_constraint)
        };

        let delta_i = delta(post_i, pre_i);
        let delta_j = delta(post_j, pre_j);
        let delta_k = delta(post_k, pre_k);
        let delta_l = delta(post_l, pre_l);

        match (delta_i, delta_j, delta_k, delta_l) {
            (Some(di), Some(dj), Some(dk), Some(dl)) => {
                // Check: di + dj - dk == dl
                di + dj - dk == dl
            }
            _ => false,
        }
    }

    /// Extract a constant integer delta between post and pre expressions.
    ///
    /// Handles patterns like:
    /// - post = (+ pre 1) → delta = 1
    /// - post = pre → delta = 0
    /// - post = (+ -1 pre) → delta = -1
    fn extract_constant_delta_from_constraint(
        post: &ChcExpr,
        pre: &ChcExpr,
        _constraint: &ChcExpr,
    ) -> Option<i128> {
        // Case: post = pre (unchanged)
        if post == pre {
            return Some(0);
        }

        // Case: post = (+ c pre) or post = (+ pre c) where c is constant
        if let ChcExpr::Op(ChcOp::Add, args) = post {
            if args.len() == 2 {
                if let (ChcExpr::Int(c), other) = (args[0].as_ref(), args[1].as_ref()) {
                    if other == pre {
                        return Some(*c);
                    }
                }
                if let (other, ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref()) {
                    if other == pre {
                        return Some(*c);
                    }
                }
            }
        }

        // Case: constraint contains (= post (+ c pre)) or similar
        // This is handled by the pattern above since post IS the head arg expression

        None
    }
}
