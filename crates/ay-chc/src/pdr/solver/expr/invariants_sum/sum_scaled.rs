// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn discover_scaled_sum_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Skip predicates with incoming inter-predicate transitions.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 3 int variables
            let int_vars: Vec<(usize, &ChcVar)> = canonical_vars
                .iter()
                .enumerate()
                .filter(|(_, v)| matches!(v.sort, ChcSort::Int))
                .collect();

            if int_vars.len() < 3
                || int_vars.len() > crate::pdr::solver::invariants::MAX_PAIRWISE_DISCOVERY_VARS
            {
                continue;
            }

            // Get initial values - for predicates entered via transitions, use entry bounds
            let init_values = self.get_init_values(pred.id);

            // For predicates with exact init values, use init-guided discovery
            // For predicates without (e.g., entered via transitions), try common coefficients
            let has_exact_init = int_vars
                .iter()
                .any(|(_, v)| init_values.get(&v.name).is_some_and(|b| b.min == b.max));

            // Try all triples (vi, vj, vk)
            for (idx_i, var_i) in &int_vars {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for (idx_j, var_j) in &int_vars {
                    if idx_i >= idx_j {
                        continue; // Avoid duplicates (vi + vj = vj + vi)
                    }

                    for (idx_k, var_k) in &int_vars {
                        if idx_k == idx_i || idx_k == idx_j {
                            continue;
                        }

                        // Get init values if available
                        let init_i = init_values
                            .get(&var_i.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min);
                        let init_j = init_values
                            .get(&var_j.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min);
                        let init_k = init_values
                            .get(&var_k.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min);

                        // Determine coefficients to try based on init values
                        let coeffs_to_try: Vec<i128> = match (init_i, init_j, init_k) {
                            (Some(i), Some(j), Some(k)) => {
                                let init_sum = i + j;
                                if k == 0 && init_sum == 0 {
                                    // All zeros - try coefficient 2 (most common)
                                    vec![2]
                                } else if k != 0 && init_sum % k == 0 {
                                    let coeff = init_sum / k;
                                    if (2..=4).contains(&coeff) {
                                        vec![coeff]
                                    } else {
                                        vec![]
                                    }
                                } else {
                                    vec![]
                                }
                            }
                            _ if !has_exact_init => {
                                // No exact init values - try coefficient 2
                                // This handles predicates entered via transitions
                                vec![2]
                            }
                            _ => vec![],
                        };

                        for coeff in coeffs_to_try {
                            if self.is_scaled_sum_preserved(pred.id, *idx_i, *idx_j, *idx_k, coeff)
                            {
                                // For predicates without exact init, verify entry condition too
                                if (init_i.is_none() || init_j.is_none() || init_k.is_none())
                                    && !self.verify_scaled_sum_at_entry(
                                        pred.id, *idx_i, *idx_j, *idx_k, coeff,
                                    )
                                {
                                    continue;
                                }
                                self.add_scaled_sum_invariant(pred.id, var_i, var_j, var_k, coeff);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Verify that a scaled sum invariant holds at entry (for predicates without direct facts).
    pub(in crate::pdr::solver) fn verify_scaled_sum_at_entry(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        idx_k: usize,
        coeff: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find entry transitions (transitions from other predicates)
        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue; // Skip fact clauses
            }
            if clause.body.predicates.len() != 1 {
                continue; // Skip hyperedges
            }

            let (body_pred, _) = &clause.body.predicates[0];
            if *body_pred == predicate {
                continue; // Skip self-loops
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get head expressions for the invariant variables
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let head_k = &head_args[idx_k];

            // Build invariant: head_i + head_j = coeff * head_k
            let lhs = ChcExpr::add(head_i.clone(), head_j.clone());
            let rhs = ChcExpr::mul(ChcExpr::Int(coeff), head_k.clone());

            // Get source predicate's frame invariants
            let source_invariants = self.get_frame_invariants_for_predicate(*body_pred);

            // Build query: source_invariants AND constraint AND NOT(invariant_holds)
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Combine source invariants
            let mut combined_source = ChcExpr::Bool(true);
            for inv in &source_invariants {
                combined_source = ChcExpr::and(combined_source, inv.clone());
            }

            let invariant_violated =
                ChcExpr::or(ChcExpr::lt(lhs.clone(), rhs.clone()), ChcExpr::gt(lhs, rhs));

            let query = ChcExpr::and(
                ChcExpr::and(combined_source, clause_constraint),
                invariant_violated,
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false, // Entry violation found
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false, // Conservative
            }
        }

        true
    }

    /// Get current frame invariants for a predicate.
    pub(in crate::pdr::solver) fn get_frame_invariants_for_predicate(
        &self,
        predicate: PredicateId,
    ) -> Vec<ChcExpr> {
        let mut invariants = Vec::new();
        if self.frames.len() > 1 {
            for lemma in &self.frames[1].lemmas {
                if lemma.predicate == predicate {
                    invariants.push(lemma.formula.clone());
                }
            }
        }
        invariants
    }

    /// Add a scaled sum invariant to the frames.
    pub(in crate::pdr::solver) fn add_scaled_sum_invariant(
        &mut self,
        pred_id: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        var_k: &ChcVar,
        coeff: i128,
    ) {
        let lhs = ChcExpr::add(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
        let rhs = ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_k.clone()));
        let scaled_sum_invariant = ChcExpr::eq(lhs, rhs);

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Discovered scaled sum invariant for pred {}: {} + {} = {} * {}",
                pred_id.index(),
                var_i.name,
                var_j.name,
                coeff,
                var_k.name
            );
        }

        self.add_discovered_invariant(pred_id, scaled_sum_invariant, 1);
    }

    /// Check if `vi + vj = coeff * vk` is preserved by all self-loop transitions.
    pub(in crate::pdr::solver) fn is_scaled_sum_preserved(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        idx_k: usize,
        coeff: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Get existing frame invariants for this predicate (e.g., bounds like toggle <= 1)
        let frame_invariants = self.get_frame_invariants_for_predicate(predicate);

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Collect clause data first to avoid borrow conflicts
        struct ClauseData {
            pre_i: ChcExpr,
            pre_j: ChcExpr,
            pre_k: ChcExpr,
            post_i: ChcExpr,
            post_j: ChcExpr,
            post_k: ChcExpr,
            constraint: ChcExpr,
            body_args: Vec<ChcExpr>,
        }
        let mut clause_data_list: Vec<ClauseData> = Vec::new();

        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
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

            // Only check self-loops
            if clause.body.predicates.len() != 1 {
                continue;
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

            clause_data_list.push(ClauseData {
                pre_i: body_args[idx_i].clone(),
                pre_j: body_args[idx_j].clone(),
                pre_k: body_args[idx_k].clone(),
                post_i: head_args[idx_i].clone(),
                post_j: head_args[idx_j].clone(),
                post_k: head_args[idx_k].clone(),
                constraint: clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true)),
                body_args: body_args.clone(),
            });
        }

        // If no self-loops were found, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }

        // Now process collected clause data
        for data in clause_data_list {
            // Substitute canonical variables in frame invariants with body args
            let mut combined_frame_invariants = ChcExpr::Bool(true);
            for inv in &frame_invariants {
                let substituted =
                    Self::substitute_canonical_vars(inv, &canonical_vars, &data.body_args);
                combined_frame_invariants = ChcExpr::and(combined_frame_invariants, substituted);
            }

            // Pre-invariant: pre_i + pre_j = coeff * pre_k
            let pre_sum = ChcExpr::add(data.pre_i.clone(), data.pre_j.clone());
            let pre_rhs = ChcExpr::mul(ChcExpr::Int(coeff), data.pre_k.clone());
            let pre_invariant = ChcExpr::eq(pre_sum, pre_rhs);

            // Post-invariant violation: post_i + post_j != coeff * post_k
            let post_sum = ChcExpr::add(data.post_i.clone(), data.post_j.clone());
            let post_rhs = ChcExpr::mul(ChcExpr::Int(coeff), data.post_k.clone());
            let post_invariant_violated = ChcExpr::or(
                ChcExpr::lt(post_sum.clone(), post_rhs.clone()),
                ChcExpr::gt(post_sum, post_rhs),
            );

            // Query: frame_invariants AND constraint AND pre_invariant AND NOT(post_invariant)
            let query = ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::and(combined_frame_invariants, data.constraint.clone()),
                    pre_invariant.clone(),
                ),
                post_invariant_violated.clone(),
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Scaled sum (idx {} + idx {} = {} * idx {}) NOT preserved",
                            idx_i,
                            idx_j,
                            coeff,
                            idx_k
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => {
                    // ITE expressions can cause Unknown - try case splitting on ITE conditions
                    if let Some(result) = self.is_scaled_sum_preserved_with_ite_split(
                        &data.constraint,
                        &pre_invariant,
                        &post_invariant_violated,
                        &data.post_i,
                        &data.post_j,
                        &data.post_k,
                    ) {
                        if !result {
                            return false;
                        }
                        // else: preserved via case splitting, continue to next clause
                    } else {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Scaled sum (idx {} + idx {} = {} * idx {}) preservation check returned Unknown",
                                idx_i, idx_j, coeff, idx_k
                            );
                        }
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Try ITE case splitting when the main preservation check returns Unknown.
    /// Returns Some(true) if preserved, Some(false) if not preserved, None if can't determine.
    pub(in crate::pdr::solver) fn is_scaled_sum_preserved_with_ite_split(
        &mut self,
        clause_constraint: &ChcExpr,
        pre_invariant: &ChcExpr,
        post_invariant_violated: &ChcExpr,
        post_i: &ChcExpr,
        post_j: &ChcExpr,
        post_k: &ChcExpr,
    ) -> Option<bool> {
        // Extract ITE conditions from post expressions
        let mut ite_conditions = Vec::new();
        Self::extract_ite_conditions(post_i, &mut ite_conditions);
        Self::extract_ite_conditions(post_j, &mut ite_conditions);
        Self::extract_ite_conditions(post_k, &mut ite_conditions);

        if ite_conditions.is_empty() {
            return None;
        }

        // Take first condition and case-split
        let cond = &ite_conditions[0];

        // Case 1: condition is true
        let query_true = ChcExpr::and(
            ChcExpr::and(
                ChcExpr::and(clause_constraint.clone(), pre_invariant.clone()),
                cond.clone(),
            ),
            post_invariant_violated.clone(),
        );

        self.smt.reset();
        let case_true_ok = match self
            .smt
            .check_sat_with_timeout(&query_true, std::time::Duration::from_millis(500))
        {
            SmtResult::Sat(_) => false,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => true,
            SmtResult::Unknown => return None,
        };

        if !case_true_ok {
            return Some(false);
        }

        // Case 2: condition is false
        let query_false = ChcExpr::and(
            ChcExpr::and(
                ChcExpr::and(clause_constraint.clone(), pre_invariant.clone()),
                ChcExpr::not(cond.clone()),
            ),
            post_invariant_violated.clone(),
        );

        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query_false, std::time::Duration::from_millis(500))
        {
            SmtResult::Sat(_) => Some(false),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Some(true)
            }
            SmtResult::Unknown => None,
        }
    }
}
