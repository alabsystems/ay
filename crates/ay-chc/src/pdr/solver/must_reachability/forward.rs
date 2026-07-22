// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Propagate must-summaries forward from level k to level k+1.
    /// For each predicate, compute what states are reachable at level k+1
    /// based on must-summaries at level k and transition clauses.
    pub(in crate::pdr::solver) fn propagate_must_summaries_forward(
        &mut self,
        from_level: usize,
        to_level: usize,
    ) {
        if !self.config.use_must_summaries {
            return;
        }

        // Collect predicate count upfront to avoid borrowing self.problem across
        // the mutable self.check_sat_via_executor_backend() call (#7984).
        let num_predicates = self.problem.predicates().len();
        for pred_idx in 0..num_predicates {
            if self.is_cancelled() {
                return;
            }
            let pred_id = PredicateId::new(pred_idx as u32);
            // Collect clauses upfront to avoid borrowing self.problem across
            // the mutable self.check_sat_via_executor_backend() call (#7984).
            let clauses_with_idx: Vec<_> = self
                .problem
                .clauses_defining_with_index(pred_id)
                .map(|(idx, c)| (idx, c.clone()))
                .collect();
            for (clause_index, clause) in &clauses_with_idx {
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                // Skip fact clauses (they define level 0 must-summaries)
                if clause.body.predicates.is_empty() {
                    continue;
                }

                // Check if all body predicates have must-summaries at from_level
                let mut body_must_formulas = Vec::new();
                let mut all_have_must = true;

                for (body_pred, body_args) in &clause.body.predicates {
                    if let Some(must_summary) =
                        self.reachability.must_summaries.get(from_level, *body_pred)
                    {
                        if let Some(applied) =
                            self.apply_to_args(*body_pred, &must_summary, body_args)
                        {
                            body_must_formulas.push(applied);
                        } else {
                            all_have_must = false;
                            break;
                        }
                    } else {
                        all_have_must = false;
                        break;
                    }
                }

                if !all_have_must {
                    continue;
                }

                // Compute what head states are reachable
                let clause_constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));

                let mut query_parts = body_must_formulas;
                query_parts.push(clause_constraint);

                // Extract the reachable value(s) for this predicate
                let canonical_vars_opt = self.canonical_vars(pred_id).map(<[ChcVar]>::to_vec);
                if let Some(canonical_vars) = canonical_vars_opt {
                    // Skip if arity mismatch
                    if head_args.len() != canonical_vars.len() {
                        continue;
                    }

                    // Build query: body_must ∧ clause_constraint
                    // SOUNDNESS NOTE (#2659): Unknown -> skip is conservative. Must-summary
                    // expansion is best-effort; missing an expansion doesn't affect safety
                    // claims, only completeness of Unsafe detection.
                    let query = self.bound_int_vars(ChcExpr::and_all(query_parts.clone()));
                    // #7984: Use persistent executor backend for integer arithmetic.

                    if let SmtResult::Sat(mut model) = self.check_sat_via_executor_backend(&query) {
                        // If model is empty, try to extract values from the query formula
                        // This handles cases like (= x 5) where SMT returns empty model
                        if model.is_empty() {
                            cube::extract_equalities_from_formula(&query, &mut model);
                        }

                        // Build must-summary for the head predicate by evaluating each head arg
                        let mut equalities = Vec::new();
                        let mut all_evaluated = true;

                        for (i, head_arg) in head_args.iter().enumerate() {
                            // SAFETY: arity check above (line 3099) ensures i < canonical_vars.len()
                            if let Some(head_val) = crate::expr::evaluate_expr(head_arg, &model) {
                                let eq = match head_val {
                                    SmtValue::Int(n) => ChcExpr::eq(
                                        ChcExpr::var(canonical_vars[i].clone()),
                                        ChcExpr::int(n),
                                    ),
                                    SmtValue::Bool(b) => ChcExpr::eq(
                                        ChcExpr::var(canonical_vars[i].clone()),
                                        ChcExpr::Bool(b),
                                    ),
                                    _ => {
                                        all_evaluated = false;
                                        break;
                                    }
                                };
                                equalities.push(eq);
                            } else {
                                all_evaluated = false;
                                break;
                            }
                        }

                        if all_evaluated && !equalities.is_empty() {
                            let new_must = if equalities.len() == 1 {
                                equalities.pop().expect("len == 1")
                            } else {
                                equalities
                                    .into_iter()
                                    .reduce(ChcExpr::and)
                                    .unwrap_or(ChcExpr::Bool(true))
                            };

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Forward must propagation: pred {} at level {} -> {}",
                                    pred_id.index(),
                                    to_level,
                                    new_must
                                );
                            }
                            // For hyperedges, collect ALL premises - verification requires complete chains
                            let mut premises = Vec::new();
                            let mut all_premises_found = true;
                            for (body_pred, body_args) in &clause.body.predicates {
                                if let Some(id) = self.pick_reach_fact_premise(
                                    *body_pred, from_level, body_args, &model,
                                ) {
                                    premises.push(id);
                                } else {
                                    all_premises_found = false;
                                }
                            }
                            let mut instances = model;
                            cube::extract_equalities_from_formula(&new_must, &mut instances);

                            // Only create backed must-summary if we have all premises
                            // (required for valid cex verification)
                            if all_premises_found || clause.body.predicates.is_empty() {
                                let Some(id) = Self::insert_reach_fact_bounded(
                                    &mut self.reachability,
                                    self.config.verbose,
                                    ReachFact {
                                        id: ReachFactId(0),
                                        predicate: pred_id,
                                        level: to_level,
                                        state: new_must.clone(),
                                        incoming_clause: Some(*clause_index),
                                        premises,
                                        instances,
                                    },
                                ) else {
                                    continue;
                                };
                                // Add to must-summaries as BACKED (proven reachable)
                                // MustSummaries handles deduplication (#1601)
                                let added = self.reachability.must_summaries.add_backed(
                                    to_level,
                                    pred_id,
                                    new_must.clone(),
                                    id,
                                );
                                if added {
                                    // Add to reach solver as BACKED entry for fast short-circuit
                                    self.reachability
                                        .reach_solvers
                                        .add_backed(pred_id, id, new_must);
                                }
                            } else {
                                // Add as filter-only (no backing ID) for negative filtering
                                let added = self.reachability.must_summaries.add_filter_only(
                                    to_level,
                                    pred_id,
                                    new_must.clone(),
                                );
                                if added {
                                    self.reachability.reach_solvers.add(pred_id, new_must);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
