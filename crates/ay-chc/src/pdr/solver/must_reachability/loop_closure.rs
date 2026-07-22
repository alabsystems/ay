// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Enrich must-summaries with self-loop closure states for inter-predicate propagation.
    ///
    /// For phase-chain benchmarks like gj2007, the init must-summary (A=0, C>0) cannot
    /// satisfy inter-predicate transition guards (A >= C). This function computes the
    /// "closure" of self-loop iterations: what states can be reached after running
    /// the self-loop until the exit guard is satisfied.
    ///
    /// For each predicate P with must-summary at level 0:
    /// 1. Find inter-predicate transitions FROM P to Q (where Q != P)
    /// 2. Extract the exit guard (constraint that must be true to take P -> Q)
    /// 3. Add (must-summary ∧ exit_guard) as an enriched must-summary for P
    ///
    /// This enables forward propagation to predicates that require guard satisfaction.
    ///
    /// Part of #1613: Must-summary self-loop closure for inter-predicate propagation.
    pub(in crate::pdr::solver) fn enrich_must_summaries_with_loop_closure(&mut self) {
        if !self.config.use_must_summaries {
            return;
        }

        // Collect predicates with must-summaries at level 0
        let preds_with_must: Vec<PredicateId> = self
            .problem
            .predicates()
            .iter()
            .enumerate()
            .filter_map(|(idx, _)| {
                let pred = PredicateId::new(idx as u32);
                if self.reachability.must_summaries.get(0, pred).is_some() {
                    Some(pred)
                } else {
                    None
                }
            })
            .collect();

        for pred in preds_with_must {
            if self.is_cancelled() {
                return;
            }
            // Verify predicate still has must-summary (defensive check)
            if self.reachability.must_summaries.get(0, pred).is_none() {
                continue;
            }

            // Find inter-predicate transitions FROM this predicate
            // These are clauses where body has pred and head is a DIFFERENT predicate
            for clause in self.problem.clauses() {
                // Check if body contains this predicate
                let has_pred_in_body = clause.body.predicates.iter().any(|(p, _)| *p == pred);
                if !has_pred_in_body {
                    continue;
                }

                // Check if head is a different predicate
                let head_pred = match &clause.head {
                    crate::ClauseHead::Predicate(p, _) if *p != pred => Some(*p),
                    _ => None,
                };

                let Some(_target_pred) = head_pred else {
                    continue;
                };

                // This is an inter-predicate transition: pred -> target_pred
                // Extract the exit guard (constraint on this transition)
                let exit_guard = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));

                // Skip trivial guards
                if exit_guard == ChcExpr::Bool(true) {
                    continue;
                }

                // Map guard variables to canonical predicate variables
                // Body predicates may have different variable names than canonical
                let body_pred_args = clause
                    .body
                    .predicates
                    .iter()
                    .find(|(p, _)| *p == pred)
                    .map(|(_, args)| args.as_slice());

                let Some(body_args) = body_pred_args else {
                    continue;
                };

                let canonical_vars_opt = self.canonical_vars(pred).map(<[ChcVar]>::to_vec);
                let Some(canonical_vars) = canonical_vars_opt else {
                    continue;
                };

                if body_args.len() != canonical_vars.len() {
                    continue;
                }

                // Build substitution: body_arg_var -> canonical_var
                // #2492: Also extract constituent vars from expression body args
                let mut exit_guard_canonical = exit_guard.clone();
                for (body_arg, canon_var) in body_args.iter().zip(canonical_vars.iter()) {
                    match body_arg {
                        ChcExpr::Var(body_var) => {
                            exit_guard_canonical = exit_guard_canonical
                                .substitute(&[(body_var.clone(), ChcExpr::var(canon_var.clone()))]);
                        }
                        expr => {
                            for v in expr.vars() {
                                exit_guard_canonical = exit_guard_canonical
                                    .substitute(&[(v.clone(), ChcExpr::var(v.clone()))]);
                            }
                        }
                    }
                }

                // Check if the enriched state is satisfiable (init can reach exit guard)
                // For gj2007: init (A=0, C>0) + exit (A >= C) is UNSAT directly,
                // but reachable after loop iterations.
                //
                // We need to check if the exit guard can EVER be satisfied by
                // states reachable from init. This requires looking at the self-loop.
                //
                // Find the self-loop clause to determine preserved variables
                let self_loop_clause = self.problem.clauses().iter().find(|c| {
                    c.head.predicate_id() == Some(pred)
                        && c.body.predicates.iter().any(|(p, _)| *p == pred)
                });

                if let Some(loop_clause) = self_loop_clause {
                    // Get init must-summary to preserve its constraints on unchanged variables
                    let init_must = self.reachability.must_summaries.get(0, pred);

                    // Find preserved variables: body_arg == head_arg (unchanged in loop)
                    let loop_body_args = loop_clause
                        .body
                        .predicates
                        .iter()
                        .find(|(p, _)| *p == pred)
                        .map(|(_, args)| args.as_slice());
                    let loop_head_args = match &loop_clause.head {
                        crate::ClauseHead::Predicate(_, args) => Some(args.as_slice()),
                        _ => None,
                    };

                    // Build enriched must-summary: exit_guard ∧ preserved_constraints
                    let mut enriched_parts = vec![exit_guard_canonical.clone()];

                    if let (Some(body_args), Some(head_args), Some(init_formula)) =
                        (loop_body_args, loop_head_args, init_must)
                    {
                        // Find which canonical variable indices are preserved
                        let mut preserved_indices: Vec<usize> = Vec::new();
                        for (i, (body_arg, head_arg)) in
                            body_args.iter().zip(head_args.iter()).enumerate()
                        {
                            let is_preserved = match (body_arg, head_arg) {
                                (ChcExpr::Var(bv), ChcExpr::Var(hv)) => bv.name == hv.name,
                                _ => false,
                            };
                            if is_preserved && i < canonical_vars.len() {
                                preserved_indices.push(i);
                            }
                        }

                        // Extract constraints on preserved variables from init formula
                        // For gj2007: E (position 2) is preserved
                        // Init has (not (<= E 0)) -> E >= 1 -> keep (>= __p2_a2 1)
                        // Init has (= B E) -> both are "preserved-ish" -> keep equality
                        for &idx in &preserved_indices {
                            // Extract lower bound from init if available
                            // Self-audit fix #2: Include all lower bounds, not just positive ones
                            // Negative bounds like x >= -5 are also valid invariants
                            if let Some(lb) = Self::extract_lower_bound_for_var(
                                &init_formula,
                                idx,
                                &canonical_vars,
                            ) {
                                enriched_parts.push(ChcExpr::ge(
                                    ChcExpr::var(canonical_vars[idx].clone()),
                                    ChcExpr::int(lb),
                                ));
                            }

                            // #1684: Extract upper bound from init if available
                            // For s_mutants_16_m: C has range [1,4] at init, must preserve C <= 4
                            // in loop-closure to prevent Entry-CEGAR from finding spurious C=5 witnesses
                            if let Some(ub) = Self::extract_upper_bound_for_canonical_var(
                                &init_formula,
                                idx,
                                &canonical_vars,
                            ) {
                                enriched_parts.push(ChcExpr::le(
                                    ChcExpr::var(canonical_vars[idx].clone()),
                                    ChcExpr::int(ub),
                                ));
                            }

                            // Extract constant equality (var = N) from init if available
                            // Self-audit fix #3: Handle cases like init has `A = 0`
                            if let Some(c) = Self::extract_constant_equality_for_var(
                                &init_formula,
                                idx,
                                &canonical_vars,
                            ) {
                                enriched_parts.push(ChcExpr::eq(
                                    ChcExpr::var(canonical_vars[idx].clone()),
                                    ChcExpr::int(c),
                                ));
                            }
                        }

                        // Check for equality constraints between variables where at least one is preserved
                        // For gj2007: init has (= __p2_a1 __p2_a2), position 2 is preserved
                        // If both sides are preserved OR one side is constant-equivalent, keep it
                        for i in 0..canonical_vars.len() {
                            for j in (i + 1)..canonical_vars.len() {
                                // Self-audit fix #1: Only add equality if it exists in init formula
                                // AND at least one var is preserved. Previously had redundant check.
                                let has_equality = Self::has_equality_in_formula(
                                    &init_formula,
                                    i,
                                    j,
                                    &canonical_vars,
                                );
                                let at_least_one_preserved = preserved_indices.contains(&i)
                                    || preserved_indices.contains(&j);

                                if has_equality && at_least_one_preserved {
                                    enriched_parts.push(ChcExpr::eq(
                                        ChcExpr::var(canonical_vars[i].clone()),
                                        ChcExpr::var(canonical_vars[j].clone()),
                                    ));
                                }
                            }
                        }
                    }

                    let enriched = ChcExpr::and_all(enriched_parts);
                    // Add as FILTER-ONLY (heuristic seed, no proof of reachability)
                    // Loop-closure enrichment is not backed by a witness chain
                    let added =
                        self.reachability
                            .must_summaries
                            .add_filter_only(0, pred, enriched.clone());
                    if added {
                        // Part of #1398: Also add as filter-only reach-solver entry.
                        // This prevents the negative fast path in check_must_reachability
                        // from skipping clause iteration for POBs that intersect the
                        // enriched closure state. We use add() (filter-only) NOT
                        // add_backed() because the enriched state is a heuristic
                        // over-approximation, not a proven under-approximation.
                        // Using add_backed would cause spurious SAT claims.
                        self.reachability.reach_solvers.add(pred, enriched.clone());

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Enriched must-summary + reach-filter for pred {} with loop closure: {}",
                                pred.index(),
                                enriched
                            );
                        }
                    }
                }
            }
        }
    }
}
