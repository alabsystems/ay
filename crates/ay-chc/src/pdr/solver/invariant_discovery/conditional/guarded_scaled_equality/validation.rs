// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// INIT, absolute: no fact clause may reach a state violating the
    /// implication. No frame assumption is used, so a survivor genuinely holds
    /// on every initial state. Solver `Unknown` rejects.
    pub(super) fn guarded_equality_init_valid(
        &mut self,
        predicate: PredicateId,
        cand: GuardedEquality,
    ) -> bool {
        let Some(canonical_vars) = self.canonical_vars(predicate) else {
            return false;
        };
        let arity = canonical_vars.len();
        let facts: Vec<_> = self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
            .cloned()
            .collect();
        for fact in facts {
            let crate::ClauseHead::Predicate(_, head_args) = &fact.head else {
                continue;
            };
            if head_args.len() != arity {
                return false;
            }
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let lemma = Self::guarded_scaled_equality_on_args(head_args, cand);
            let query = ChcExpr::and(constraint, ChcExpr::not(lemma));
            if !self.guarded_equality_query_is_unsat(&query) {
                return false;
            }
        }
        true
    }

    /// PRESERVATION, relative to `assumption` ONLY — never the frame.
    ///
    /// For every self-loop: `AND(assumption)[body] AND constraint AND
    /// NOT cand[head]` must be UNSAT. Assuming the whole surviving set (itself
    /// included) is what makes a mutually-dependent family provable together;
    /// assuming nothing outside it is what keeps the fixpoint sound.
    pub(super) fn guarded_equality_preserved_given(
        &mut self,
        predicate: PredicateId,
        cand: GuardedEquality,
        assumption: &[GuardedEquality],
    ) -> bool {
        let Some(canonical_vars) = self.canonical_vars(predicate) else {
            return false;
        };
        let arity = canonical_vars.len();
        let clauses: Vec<_> = self
            .problem
            .clauses_defining(predicate)
            .filter(|clause| {
                clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == predicate
            })
            .cloned()
            .collect();

        let mut checked_any_self_loop = false;
        for clause in clauses {
            let (_, body_args) = &clause.body.predicates[0];
            let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
                continue;
            };
            if body_args.len() != arity || head_args.len() != arity {
                return false;
            }
            checked_any_self_loop = true;

            let mut parts: Vec<ChcExpr> = Vec::with_capacity(assumption.len() + 2);
            for a in assumption {
                parts.push(Self::guarded_scaled_equality_on_args(body_args, *a));
            }
            parts.push(
                clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true)),
            );
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let post = Self::guarded_scaled_equality_on_args(head_args, cand);
            let query = ChcExpr::and(base, ChcExpr::not(post));
            if !self.guarded_equality_query_is_unsat(&query) {
                return false;
            }
        }
        checked_any_self_loop
    }

    /// `true` only on a definitive UNSAT; `Sat` and `Unknown` both reject.
    fn guarded_equality_query_is_unsat(&mut self, query: &ChcExpr) -> bool {
        self.smt.reset();
        matches!(
            self.smt
                .check_sat_with_timeout(query, std::time::Duration::from_millis(500)),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }
}
