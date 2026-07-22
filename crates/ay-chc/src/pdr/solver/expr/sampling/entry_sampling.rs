// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use super::super::model_key;
use super::with_blocking_clauses;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    /// Sample models from entry edges for predicates without fact clauses (#1970).
    ///
    /// For derived predicates, builds edge formula from incoming inter-predicate
    /// clauses and samples head-variable values mapped to canonical vars.
    pub(in crate::pdr::solver) fn sample_entry_edge_models(
        &mut self,
        predicate: PredicateId,
        level: usize,
        n: usize,
    ) -> Vec<FxHashMap<String, i128>> {
        // Some benchmarks (e.g., s_multipl_10) require sampling through multiple layers of
        // derived predicates: P (facts) -> Q (derived) -> R (derived). To seed R from Q when Q
        // has no must-summaries yet, we recursively sample entry-edge models for Q.
        //
        // Depth is bounded and guarded by a visited set to avoid loops in cyclic CHCs.
        // Depth 3 handles: P (facts) -> Q (derived) -> R (derived) -> S (derived)
        const MAX_DERIVED_BODY_SAMPLE_DEPTH: usize = 3;
        let mut visited: FxHashSet<PredicateId> = FxHashSet::default();
        visited.insert(predicate);
        self.sample_entry_edge_models_impl(
            predicate,
            level,
            n,
            MAX_DERIVED_BODY_SAMPLE_DEPTH,
            &mut visited,
        )
    }

    fn sample_entry_edge_models_impl(
        &mut self,
        predicate: PredicateId,
        level: usize,
        n: usize,
        remaining_depth: usize,
        visited: &mut FxHashSet<PredicateId>,
    ) -> Vec<FxHashMap<String, i128>> {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return Vec::new(),
        };

        let int_vars: Vec<ChcVar> = canonical_vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        if int_vars.is_empty() {
            return Vec::new();
        }

        let incoming_clauses: Vec<_> = self
            .problem
            .clauses_defining(predicate)
            .filter(|clause| {
                !clause.body.predicates.is_empty()
                    && clause.body.predicates.iter().any(|(p, _)| *p != predicate)
            })
            .cloned()
            .collect();
        if incoming_clauses.is_empty() {
            return Vec::new();
        }

        // Global (across incoming clauses) blocking set for diversity in the *head predicate's*
        // canonical integer variables. This prevents collecting many duplicates when different
        // incoming clauses use different clause-local variable names.
        let mut all_models: Vec<FxHashMap<String, i128>> = Vec::with_capacity(n);
        let mut blocking_clauses: Vec<ChcExpr> = Vec::new();

        for clause in &incoming_clauses {
            if all_models.len() >= n {
                break;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.clone(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Helper: build head bindings `canon_i = head_arg_i` for all integer args.
            // This ensures we can extract a complete assignment for canonical vars even when:
            // - head args are constants or expressions (not just variables)
            // - head variables don't appear elsewhere in the edge formula
            let head_bindings: Vec<ChcExpr> = canonical_vars
                .iter()
                .zip(head_args.iter())
                .filter(|(canon, _)| matches!(canon.sort, ChcSort::Int))
                .map(|(canon, arg)| ChcExpr::eq(ChcExpr::var(canon.clone()), arg.clone()))
                .collect();

            // Strategy 1: If this is a simple single-body clause, try to sample *reachable-ish*
            // entry states by pushing concrete body samples through the edge.
            if clause.body.predicates.len() == 1 && all_models.len() < n {
                let (body_pred, body_args) = &clause.body.predicates[0];
                let Some(body_canon) = self.canonical_vars(*body_pred).map(<[ChcVar]>::to_vec)
                else {
                    continue;
                };
                if body_args.len() != body_canon.len() {
                    continue;
                }

                let mut body_models: Vec<FxHashMap<String, i128>> = Vec::new();

                // Prefer sampling from must-summaries (concretely reachable) when available.
                // Also include init+forward simulation when the body predicate has facts to
                // preserve parameter diversity (some must-summaries are weak and allow the SMT
                // layer to pick a single minimal value for unconstrained parameters).
                //
                // Note: We sample across levels <= `level` because must-summaries often live
                // at level 0 (init / loop-closure enrichment) even when called at higher levels.
                let max_sample_level = level.min(5);
                let target_body_samples = (n - all_models.len()).max(3) * 3;

                if self.predicate_has_facts(*body_pred) {
                    let seed_n = (n - all_models.len()).clamp(3, 6);
                    let mut init_models = self.sample_init_models(*body_pred, seed_n);
                    if !init_models.is_empty() {
                        let forward = self.simulate_forward_samples_from_init_samples(
                            *body_pred,
                            &init_models,
                            50,
                        );
                        init_models.extend(forward);
                        body_models.extend(init_models);
                    }
                }

                for lvl in 0..=max_sample_level {
                    body_models.extend(self.sample_reachable_models(*body_pred, lvl, 3));
                    if body_models.len() >= target_body_samples {
                        break;
                    }
                }

                // Even when must-summaries exist, they may describe only shallow reachable
                // states (often the entry region). For entry edges guarded by an exit condition
                // (e.g., A = 0), forward simulation helps reach the boundary states needed
                // to seed the head predicate (s_multipl_15 POST, s_multipl_10 FUN->SAD).
                if !body_models.is_empty() && body_models.len() < target_body_samples {
                    let forward = self.simulate_forward_samples_from_init_samples(
                        *body_pred,
                        &body_models,
                        50,
                    );
                    body_models.extend(forward);
                }

                // If the body predicate is derived (no facts), it may not yet have must
                // summaries. In that case, recursively sample *its* entry edges, then forward-
                // simulate its self-loops to obtain reachable-ish body states for this edge.
                //
                // Also do this as an augmentation path when must-summary sampling is too small.
                if body_models.len() < target_body_samples
                    && !self.predicate_has_facts(*body_pred)
                    && remaining_depth > 0
                {
                    let inserted = visited.insert(*body_pred);
                    if inserted {
                        let mut derived_models: Vec<FxHashMap<String, i128>> = Vec::new();

                        // Limit recursion to a small number of samples to avoid blowups.
                        let inner_n = (n - all_models.len()).clamp(3, 6);
                        for lvl in 1..=max_sample_level.min(3) {
                            derived_models.extend(self.sample_entry_edge_models_impl(
                                *body_pred,
                                lvl,
                                inner_n,
                                remaining_depth - 1,
                                visited,
                            ));
                            if derived_models.len() >= inner_n * 3 {
                                break;
                            }
                        }

                        if !derived_models.is_empty() {
                            let forward = self.simulate_forward_samples_from_init_samples(
                                *body_pred,
                                &derived_models,
                                50,
                            );
                            derived_models.extend(forward);
                        }

                        // Dedup and cap.
                        let mut body_seen: FxHashSet<String> = FxHashSet::default();
                        derived_models.retain(|m| body_seen.insert(model_key(m)));
                        if derived_models.len() > inner_n * 3 {
                            derived_models.truncate(inner_n * 3);
                        }

                        body_models.extend(derived_models);
                        visited.remove(body_pred);
                    }
                }

                // Dedup body samples to avoid repeated identical queries.
                let mut body_seen: FxHashSet<String> = FxHashSet::default();
                body_models.retain(|m| body_seen.insert(model_key(m)));

                for body_model in &body_models {
                    if all_models.len() >= n {
                        break;
                    }

                    let mut conjuncts: Vec<ChcExpr> =
                        Vec::with_capacity(1 + head_bindings.len() + body_args.len());

                    if let Some(ref constraint) = clause.body.constraint {
                        conjuncts.push(constraint.clone());
                    }

                    // Fix the body predicate arguments to a concrete sampled body state:
                    // for each integer arg position i: body_arg_i = body_value_i.
                    let mut body_complete = true;
                    for (i, canon_var) in body_canon.iter().enumerate() {
                        if !matches!(canon_var.sort, ChcSort::Int) {
                            continue;
                        }
                        let Some(&value) = body_model.get(&canon_var.name) else {
                            body_complete = false;
                            break;
                        };
                        conjuncts.push(ChcExpr::eq(body_args[i].clone(), ChcExpr::Int(value)));
                    }
                    if !body_complete {
                        continue;
                    }

                    conjuncts.extend(head_bindings.iter().cloned());

                    let base = if conjuncts.is_empty() {
                        ChcExpr::Bool(true)
                    } else {
                        ChcExpr::and_all(conjuncts)
                    };

                    let query = with_blocking_clauses(base, &blocking_clauses);

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Sat(model) => {
                            let Some(values) = Self::extract_head_int_assignment_from_model(
                                &model,
                                &canonical_vars,
                                &head_args,
                            ) else {
                                continue;
                            };

                            // Block this exact head assignment from future samples.
                            let diseqs: Vec<ChcExpr> = int_vars
                                .iter()
                                .filter_map(|v| {
                                    values.get(&v.name).map(|val| {
                                        ChcExpr::ne(ChcExpr::var(v.clone()), ChcExpr::Int(*val))
                                    })
                                })
                                .collect();
                            if !diseqs.is_empty() {
                                blocking_clauses.push(
                                    diseqs
                                        .into_iter()
                                        .reduce(ChcExpr::or)
                                        .unwrap_or(ChcExpr::Bool(true)),
                                );
                            }

                            all_models.push(values);
                        }
                        _ => {
                            // Concrete body sample incompatible with this edge; try next.
                            continue;
                        }
                    }
                }
            }

            if all_models.len() >= n {
                break;
            }

            // Strategy 2 (fallback): SMT sampling over the edge formula using current solver
            // knowledge (frame constraints + must-summaries when available).
            let mut conjuncts: Vec<ChcExpr> = Vec::new();
            if let Some(ref constraint) = clause.body.constraint {
                conjuncts.push(constraint.clone());
            }

            for (body_pred, body_args) in &clause.body.predicates {
                // Prefer must-summaries (under-approx reachable domain) as a sampling guide.
                if let Some(must) = self.reachability.must_summaries.get_all_levels(*body_pred) {
                    if let Some(applied) = self.apply_to_args(*body_pred, &must, body_args) {
                        conjuncts.push(applied);
                    }
                }

                if let Some(frame_lemmas) = self.cumulative_frame_constraint(level, *body_pred) {
                    if let Some(applied) = self.apply_to_args(*body_pred, &frame_lemmas, body_args)
                    {
                        conjuncts.push(applied);
                    }
                }
            }

            conjuncts.extend(head_bindings.iter().cloned());

            let base_formula = if conjuncts.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::and_all(conjuncts)
            };

            for _ in 0..(n - all_models.len()) {
                let query = with_blocking_clauses(base_formula.clone(), &blocking_clauses);

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                {
                    SmtResult::Sat(model) => {
                        let Some(values) = Self::extract_head_int_assignment_from_model(
                            &model,
                            &canonical_vars,
                            &head_args,
                        ) else {
                            break;
                        };

                        // Block this exact head assignment from future samples.
                        let diseqs: Vec<ChcExpr> = int_vars
                            .iter()
                            .filter_map(|v| {
                                values.get(&v.name).map(|val| {
                                    ChcExpr::ne(ChcExpr::var(v.clone()), ChcExpr::Int(*val))
                                })
                            })
                            .collect();
                        if !diseqs.is_empty() {
                            blocking_clauses.push(
                                diseqs
                                    .into_iter()
                                    .reduce(ChcExpr::or)
                                    .unwrap_or(ChcExpr::Bool(true)),
                            );
                        }

                        all_models.push(values);
                    }
                    _ => break,
                }
            }
        }

        if self.config.verbose && !all_models.is_empty() {
            safe_eprintln!(
                "PDR: sampled {} entry-edge models for derived pred {} at level {}",
                all_models.len(),
                predicate.index(),
                level
            );
        }

        all_models
    }
}
