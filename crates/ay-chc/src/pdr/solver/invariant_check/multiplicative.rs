// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Verify that a multiplicative invariant (vi = k * vj) holds for a predicate.
    ///
    /// The invariant holds if:
    /// 1. For fact clauses: the init constraint implies vi = k * vj
    /// 2. For transition clauses: if precondition has vi = k * vj, then postcondition has vi' = k * vj'
    pub(in crate::pdr::solver) fn verify_multiplicative_invariant(
        &mut self,
        predicate: PredicateId,
        vi_name: &str,
        vj_name: &str,
        k: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let vi_idx = canonical_vars.iter().position(|v| v.name == vi_name);
        let vj_idx = canonical_vars.iter().position(|v| v.name == vj_name);
        let (vi_idx, vj_idx) = match (vi_idx, vj_idx) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            if self.is_cancelled() {
                return false;
            }
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let vi_expr = &head_args[vi_idx];
            let vj_expr = &head_args[vj_idx];
            let invariant_at_init = ChcExpr::eq(
                vi_expr.clone(),
                ChcExpr::mul(ChcExpr::Int(k), vj_expr.clone()),
            );

            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(constraint, ChcExpr::not(invariant_at_init));

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => return false,
            }
        }

        for clause in self.problem.clauses_defining(predicate) {
            if self.is_cancelled() {
                return false;
            }
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

            for (body_pred, body_args) in &clause.body.predicates {
                let body_canonical = match self.canonical_vars(*body_pred) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                if body_args.len() != body_canonical.len() {
                    continue;
                }

                let body_vi_idx = body_canonical.iter().position(|v| v.name == vi_name);
                let body_vj_idx = body_canonical.iter().position(|v| v.name == vj_name);

                let (body_vi_idx, body_vj_idx) = match (body_vi_idx, body_vj_idx) {
                    (Some(i), Some(j)) => (i, j),
                    // Cross-predicate transition: body predicate doesn't have
                    // matching variable names. Positional fallback is UNSOUND —
                    // position i in body_pred may have different semantics than
                    // position i in the target predicate (e.g., inv4 position 0
                    // is a counter while inv5 position 0 is the final accumulator).
                    // Skip this clause and let add_discovered_invariant's entry-
                    // inductiveness check handle cross-predicate correctness.
                    _ if *body_pred != predicate => {
                        continue;
                    }
                    _ => return false,
                };

                let pre_vi = &body_args[body_vi_idx];
                let pre_vj = &body_args[body_vj_idx];
                let post_vi = &head_args[vi_idx];
                let post_vj = &head_args[vj_idx];

                let pre_invariant = ChcExpr::eq(
                    pre_vi.clone(),
                    ChcExpr::mul(ChcExpr::Int(k), pre_vj.clone()),
                );
                let post_invariant = ChcExpr::eq(
                    post_vi.clone(),
                    ChcExpr::mul(ChcExpr::Int(k), post_vj.clone()),
                );

                let constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));

                // Strict inductiveness: pre AND constraint → post.
                // Do NOT use frame strengthening here. Frame-relative verification
                // creates a circular dependency: false invariants accumulate in the
                // frame, making the pre-condition UNSAT, which makes all subsequent
                // invariant checks vacuously true. This leads to inconsistent frames
                // (e.g., A=3*C AND C=A in gj2007_m_2 pred 0). The entry-inductiveness
                // check in add_discovered_invariant handles cross-predicate soundness.
                let query = ChcExpr::and(
                    ChcExpr::and(pre_invariant, constraint),
                    ChcExpr::not(post_invariant),
                );

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                    _ => return false,
                }
            }
        }

        true
    }
}
