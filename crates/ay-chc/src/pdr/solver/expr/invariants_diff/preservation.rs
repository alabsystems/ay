// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Difference preservation checks — verify that vi - vj is preserved by transitions.

use super::*;

impl PdrSolver {
    /// Check if a difference (vi - vj) is preserved by all transitions for a predicate.
    pub(in crate::pdr::solver) fn is_difference_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the indices of var_i and var_j in canonical vars
        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let (idx_i, idx_j) = match (idx_i, idx_j) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
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

            // Get the head expressions for var_i and var_j (post-state values)
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];

            // Get the body expressions for var_i and var_j (pre-state values)
            if clause.body.predicates.len() != 1 {
                // Hyperedge - be conservative
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

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            // Check: head_i - head_j = body_i - body_j given the clause constraint
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let pre_diff = ChcExpr::sub(body_i.clone(), body_j.clone());
            let post_diff = ChcExpr::sub(head_i.clone(), head_j.clone());
            let diff_differs = ChcExpr::ne(pre_diff, post_diff);

            // Query: clause_constraint AND (pre_diff != post_diff)
            // If SAT, the difference is NOT preserved
            let query = ChcExpr::and(clause_constraint, diff_differs);

            self.smt.reset();
            // Use timeout to avoid hanging on complex queries with ITE
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    // Difference is NOT preserved by this transition
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Difference ({} - {}) is NOT preserved by transition",
                            var_i.name,
                            var_j.name
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Difference IS preserved by this transition
                    continue;
                }
                SmtResult::Unknown => {
                    // Can't verify - be conservative
                    return false;
                }
            }
        }

        // All self-loop transitions preserve the difference.
        // But if zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Difference ({} - {}) is algebraically preserved by all transitions",
                var_i.name,
                var_j.name
            );
        }
        true
    }

    /// Check if a difference (vi - vj) is preserved by all transitions, with entry domain constraint.
    ///
    /// This variant is for predicates without fact clauses (phase-chain predicates).
    /// The entry domain constraint restricts the pre-state to reachable states from
    /// predecessor predicates, enabling discovery of invariants that are preserved
    /// only on the reachable domain.
    ///
    /// Part of #1545 - entry-domain conditioned invariants.
    ///
    /// # Arguments
    /// * `predicate` - The predicate ID
    /// * `var_i` - First variable in the difference
    /// * `var_j` - Second variable in the difference
    /// * `entry_domain` - Entry domain constraint (in canonical variable names)
    ///
    /// Returns true if (var_i - var_j) is preserved by all self-loop transitions
    /// when starting from states satisfying the entry domain.
    pub(in crate::pdr::solver) fn is_difference_preserved_with_entry_domain(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        entry_domain: &ChcExpr,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the indices of var_i and var_j in canonical vars
        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let (idx_i, idx_j) = match (idx_i, idx_j) {
            (Some(i), Some(j)) => (i, j),
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

            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            let mut clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Add entry domain constraint (converted to body variable names)
            let mut canon_to_body: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for (body_arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
                canon_to_body.insert(canon.name.clone(), body_arg.clone());
            }
            let entry_on_body = entry_domain.substitute_name_map(&canon_to_body);
            clause_constraint = ChcExpr::and(clause_constraint, entry_on_body);

            let pre_diff = ChcExpr::sub(body_i.clone(), body_j.clone());
            let post_diff = ChcExpr::sub(head_i.clone(), head_j.clone());
            let diff_differs = ChcExpr::ne(pre_diff, post_diff);

            let query = ChcExpr::and(clause_constraint, diff_differs);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Difference ({} - {}) NOT preserved (with entry domain)",
                            var_i.name,
                            var_j.name
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue;
                }
                SmtResult::Unknown => {
                    return false;
                }
            }
        }

        if !checked_any_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Difference ({} - {}) preserved (with entry domain)",
                var_i.name,
                var_j.name
            );
        }
        true
    }
}
