// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! IUC (Inductive UNSAT Core) shrinking for blocking formula generalization.
//!
//! Extracts minimal subsets of blocking conjuncts using UNSAT cores from
//! inductiveness checks. Port of Z3 Spacer's core-based cube shrinking.

use super::super::*;

impl PdrSolver {
    pub(in crate::pdr) fn try_shrink_blocking_conjuncts_with_iuc(
        &mut self,
        conjuncts: &[ChcExpr],
        predicate: PredicateId,
        level: usize,
    ) -> Option<Vec<ChcExpr>> {
        if level < 1 || conjuncts.len() < 2 {
            return None;
        }

        let mut needed: Vec<bool> = vec![false; conjuncts.len()];
        let mut saw_any_core = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }
            if clause.body.predicates.len() != 1 {
                return None;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let (body_pred, body_args) = &clause.body.predicates[0];

            // At level 1, body frame is at level 0, which comes from fact clauses.
            // If body predicate has exactly one fact clause, use that constraint.
            // If 0 or >1 fact clauses, skip this clause but continue with others.
            let frame_on_body = if level == 1 {
                // Collect fact clauses for body predicate
                let fact_clauses: Vec<(usize, &crate::HornClause)> = self
                    .problem
                    .clauses()
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| {
                        c.body.predicates.is_empty() && c.head.predicate_id() == Some(*body_pred)
                    })
                    .collect();

                if fact_clauses.len() != 1 {
                    // 0 facts = no init states, >1 facts = disjunction - skip this clause
                    continue;
                }

                let (fact_index, fact) = fact_clauses[0];
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != body_args.len() {
                    continue;
                }

                // The fact renamed apart from this step clause (a shared
                // letter would equate an init local with a step variable —
                // `rename_clause_apart`), joined to the body positionally:
                // `fact ∧ body_args = fact_head_args`. This also replaces the
                // old head-variable substitution, which mapped every variable
                // of a compound fact head argument (e.g. `x + 1`) to the body
                // argument itself.
                // A failed rename abandons the shrink (never a weaker frame).
                let names = self.source_names()?;
                let (renamed_fact, renamed_head_args) = self.rename_clause_apart(
                    &names,
                    &format!("__fact{fact_index}_"),
                    &fact_constraint,
                    fact_head_args,
                    [&clause_constraint].into_iter().chain(body_args.iter()),
                )?;
                let init_match = ChcExpr::and_all(
                    body_args
                        .iter()
                        .cloned()
                        .zip(renamed_head_args)
                        .map(|(body_arg, fact_arg)| ChcExpr::eq(body_arg, fact_arg)),
                );
                ChcExpr::and(renamed_fact, init_match)
            } else {
                let frame_constraint = self
                    .cumulative_frame_constraint(level - 1, *body_pred)
                    .unwrap_or(ChcExpr::Bool(true));

                match self.apply_to_args(*body_pred, &frame_constraint, body_args) {
                    Some(expr) => expr,
                    None => continue,
                }
            };

            let mut assumptions_on_head = Vec::with_capacity(conjuncts.len());
            for c in conjuncts {
                let c_on_head = self.apply_to_args(predicate, c, head_args)?;
                assumptions_on_head.push(c_on_head);
            }

            self.smt.reset();
            // Rung 4: the session answers when it can (conjunct-level core
            // over the assumptions; `check_sat_with_assumption_conjuncts_search`).
            match self.smt.check_sat_with_assumption_conjuncts_search(
                &[clause_constraint, frame_on_body],
                &assumptions_on_head,
            ) {
                SmtResult::Sat(_) => return None,
                SmtResult::Unknown => return None,
                SmtResult::Unsat | SmtResult::UnsatWithFarkas(_) => {
                    // No core available; be conservative and skip IUC shrinking.
                    continue;
                }
                SmtResult::UnsatWithCore(core) => {
                    saw_any_core = true;
                    for (i, a) in assumptions_on_head.iter().enumerate() {
                        if core.conjuncts.iter().any(|c| c == a) {
                            needed[i] = true;
                        }
                    }
                }
            }
        }

        if !saw_any_core {
            return None;
        }

        let shrunk: Vec<ChcExpr> = conjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| needed[i])
            .map(|(_, c)| c.clone())
            .collect();

        if shrunk.is_empty() {
            return None;
        }

        Some(shrunk)
    }
}
