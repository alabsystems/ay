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
                let fact_clauses: Vec<_> = self
                    .problem
                    .clauses()
                    .iter()
                    .filter(|c| {
                        c.body.predicates.is_empty() && c.head.predicate_id() == Some(*body_pred)
                    })
                    .collect();

                if fact_clauses.len() != 1 {
                    // 0 facts = no init states, >1 facts = disjunction - skip this clause
                    continue;
                }

                let fact = &fact_clauses[0];
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                // Apply fact constraint to body args via fact head args
                // Substitutes fact_head_args variables with body_args expressions
                // #2492: Also extract constituent vars from expression fact head args
                let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
                for (fact_arg, body_arg) in fact_head_args.iter().zip(body_args.iter()) {
                    match fact_arg {
                        ChcExpr::Var(v) => subst.push((v.clone(), body_arg.clone())),
                        expr => {
                            // For expression fact head args, substitute constituent vars
                            for v in expr.vars() {
                                if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                                    subst.push((v.clone(), body_arg.clone()));
                                }
                            }
                        }
                    }
                }
                if subst.len() < fact_head_args.len() {
                    // Conservative bail: some positions have no variables at all
                    continue;
                }
                fact_constraint.substitute(&subst)
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
            match self.smt.check_sat_with_assumption_conjuncts(
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
