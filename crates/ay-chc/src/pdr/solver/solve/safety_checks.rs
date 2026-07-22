// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Mid-loop direct safety proof used after `StrengthenResult::Safe` when frame
    /// convergence is delayed by non-pushable lemmas.
    ///
    /// This keeps the `solve()` loop readable and gives us a focused test seam for
    /// the #2059 fallback path.
    pub(super) fn try_main_loop_direct_safety_proof(&mut self) -> Option<InvariantModel> {
        // Keep the original guard: don't run this early when the frame stack is shallow.
        if self.frames.len() <= 3 {
            return None;
        }

        // Skip if no new lemmas since last failed attempt (#5480).
        // The cascade + verify_model costs ~3.5s per call. For benchmarks where
        // the model fails transition verification repeatedly (e.g., s_multipl_24),
        // this avoids burning the entire solve budget on futile re-verification.
        let current_lemma_count: usize = self.frames[1].lemmas.len();
        if current_lemma_count > 0
            && current_lemma_count <= self.verification.last_direct_safety_lemma_count
        {
            return None;
        }

        let model = self.check_invariants_prove_safety()?;

        // #5877: When every lemma was verified as strictly self-inductive (no
        // frame strengthening), skip the whole-model verify_model_with_budget.
        //
        // Strict self-inductiveness of each lemma φᵢ means:
        //   ∀i: φᵢ ∧ Trans → φᵢ'  (per-clause, per-lemma SMT check with ITE case-split)
        // This implies the conjunction is inductive:
        //   (∧ᵢ φᵢ) ∧ Trans → (∧ᵢ φᵢ')
        //
        // The whole-model check is redundant but can fail due to SMT solver
        // limitations on complex disjunctive transitions (e.g., BV 9-case
        // transitions, BvToInt-relaxed integer counterexamples). The per-lemma
        // checks use ITE case-splitting which handles these better.
        //
        // Frame-strengthened inductiveness is weaker (inductive relative to
        // other frame lemmas), so models with frame-strengthened lemmas must
        // still go through verify_model_with_budget.
        //
        // EXCEPTION: Hyperedge clauses (multiple body predicates in one clause,
        // e.g., P(x) ∧ Q(y) ⇒ R(x,y)). Per-lemma self-inductiveness only
        // verifies self-loop transitions. Entry-inductiveness checks cross-
        // predicate transitions but uses must-summaries/frame constraints for
        // body predicates, which may be weaker than the actual reachable set.
        // For hyperedge clauses, the body predicate conjunction constrains the
        // head, and weak body invariants can cause the head invariant to be
        // unsound. Full verify_model_with_budget is required. (#7467)
        let has_hyperedge = self
            .problem
            .clauses()
            .iter()
            .any(|c| c.body.predicates.len() > 1);
        if model.individually_inductive && !has_hyperedge {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: accepting strictly self-inductive model, skipping whole-model check (#5877)"
                );
            }
            return Some(model);
        } else if model.individually_inductive && has_hyperedge {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: individually_inductive model but problem has hyperedge clauses; \
                     requiring full verification (#7467)"
                );
            }
        }

        // (#5745) All other models go through budget-based verification — no
        // skip_transition_validation fast-accept. The budget version handles
        // mod/div-heavy transition clauses that return Unknown (#3121).
        // Query clauses are always checked (soundness-critical).
        let verify_budget = std::time::Duration::from_millis(1500);
        if self.verify_model_with_budget(&model, verify_budget) {
            return Some(model);
        }

        // NOTE: A query-only fallback was here (#1362) but was UNSOUND.
        // Query-only verification checks that the invariant blocks the error
        // state, but does NOT verify that the invariant holds on all reachable
        // states. Frame-strengthened lemmas can block the query syntactically
        // while being non-inductive (e.g., reachable_abort_unsafe: v1=0 blocks
        // query v1=1 but fails on transition v0>10 → v1'=1). If full
        // verification fails, the model is invalid — period.

        // #5941: Track direct safety proof verification failures.
        self.verification.total_model_failures += 1;
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety produced invalid model in main loop; \
                 total_model_failures={}, continuing",
                self.verification.total_model_failures,
            );
        }
        self.verification.last_direct_safety_lemma_count = current_lemma_count;
        None
    }

    /// Check if initial states satisfy safety (no query reachable at level 0)
    pub(in crate::pdr::solver) fn init_safe(&mut self) -> InitResult {
        let mut any_unknown = false;
        // Collect queries upfront to avoid borrowing self.problem across
        // the mutable self.check_sat_via_executor_backend() call (#7984).
        let queries: Vec<_> = self.problem.queries().cloned().collect();
        for query in &queries {
            if query.body.predicates.len() != 1 {
                // Multi-predicate queries can't be checked against individual
                // facts. Skip rather than bail — PDR will discover unsafety
                // through normal POB processing if needed (#6047).
                any_unknown = true;
                continue;
            }

            let (pred, args) = &query.body.predicates[0];
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let bad_state = match self.constraint_to_canonical_state(*pred, args, &constraint) {
                Some(s) => s,
                None => {
                    any_unknown = true;
                    continue;
                }
            };

            let facts: Vec<_> = self
                .problem
                .facts()
                .filter(|f| f.head.predicate_id() == Some(*pred))
                .cloned()
                .collect();
            for fact in &facts {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                let bad_on_fact = match self.apply_to_args(*pred, &bad_state, head_args) {
                    Some(e) => e,
                    None => {
                        any_unknown = true;
                        continue;
                    }
                };
                let init_and_bad = self.bound_int_vars(ChcExpr::and(fact_constraint, bad_on_fact));
                // #7984: Use persistent executor backend for integer arithmetic.
                match self.check_sat_via_executor_backend(&init_and_bad) {
                    SmtResult::Sat(_) => return InitResult::Unsafe,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                    SmtResult::Unknown => {
                        // SMT couldn't decide init AND bad. Continue checking
                        // remaining queries — other queries may still determine
                        // safety. PDR discovers unsafety via POB processing (#6047).
                        any_unknown = true;
                    }
                }
            }
        }

        if any_unknown {
            // Some queries were indeterminate, but none found Unsafe. Treat as
            // Safe to allow PDR to proceed — if the initial state is actually
            // unsafe, PDR will find it through normal POB processing.
            // This is sound: init_safe is an optimization, not a correctness gate.
            // Z3 Spacer takes the same approach: init_safe failure doesn't block PDR.
            if self.config.verbose {
                safe_eprintln!("PDR: init_safe had indeterminate queries; proceeding as Safe");
            }
        }

        InitResult::Safe
    }

    /// #6047: Try to prove safety for acyclic problems (no transition clauses).
    ///
    /// For problems where all clauses are facts or queries (no transitions),
    /// the invariant `true` is trivially inductive. Safety reduces to checking
    /// whether each query constraint is satisfiable. If all query constraints
    /// are Unsat, the system is safe.
    ///
    /// This handles model-checker-consumer-generated CHC problems that, after inlining, have a
    /// single predicate with many error-path queries but no self-loop transitions.
    /// Standard PDR fails on these because it can't learn lemmas (strengthen
    /// finds no bad states) and check_fixed_point rejects empty frames.
    pub(super) fn try_acyclic_safety_proof(&mut self) -> Option<InvariantModel> {
        let queries: Vec<_> = self
            .problem
            .clauses()
            .iter()
            .filter(|c| c.is_query())
            .cloned()
            .collect();

        let facts: Vec<_> = self.problem.facts().cloned().collect();

        if queries.is_empty() {
            return None;
        }

        // Collect facts per predicate in canonical vars for model building.
        let mut pred_fact_constraints: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();
        for fact in &facts {
            if let crate::ClauseHead::Predicate(pred_id, head_args) = &fact.head {
                let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                if let Some(canonical) =
                    self.constraint_to_canonical_state(*pred_id, head_args, &constraint)
                {
                    pred_fact_constraints
                        .entry(*pred_id)
                        .or_default()
                        .push(canonical);
                }
            }
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: acyclic_safety: {} queries, {} facts",
                queries.len(),
                facts.len()
            );
        }

        // For each query, check safety by directly unifying fact and query
        // constraints at the clause-variable level through arg equalities.
        // This avoids canonical-var scoping issues from scalarized arrays.
        //
        // For query `P(q_args) AND q_constraint => false`:
        //   Safe iff ∀ fact_i defining P: `fact_i_constraint AND (fact_head_args = q_args) AND q_constraint` is Unsat
        //
        // Since (∨_i fact_i) AND query is Unsat iff ∀i . fact_i AND query is Unsat.
        for (i, query) in queries.iter().enumerate() {
            if self.is_cancelled() {
                return None;
            }

            if query.body.predicates.is_empty() {
                // Pure constraint query (expanded from nullary fail predicate).
                let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let bounded = self.bound_int_vars(constraint);
                // #7984: Use persistent executor backend for integer arithmetic.
                match self.check_sat_via_executor_backend(&bounded) {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: acyclic_safety: query {} (pure constraint) proven unreachable",
                                i
                            );
                        }
                        continue;
                    }
                    SmtResult::Sat(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: acyclic_safety: query {} (pure constraint) is Sat, bailing",
                                i
                            );
                        }
                        return None;
                    }
                    SmtResult::Unknown => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: acyclic_safety: query {} (pure constraint) Unknown, bailing",
                                i
                            );
                        }
                        return None;
                    }
                }
            } else if query.body.predicates.len() == 1 {
                let (pred_id, query_args) = &query.body.predicates[0];
                let query_constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

                // Gather relevant fact clauses for this predicate.
                let relevant_facts: Vec<_> = facts
                    .iter()
                    .filter(|f| f.head.predicate_id() == Some(*pred_id))
                    .collect();

                if relevant_facts.is_empty() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: acyclic_safety: query {} pred {} has no facts, vacuously safe",
                            i,
                            pred_id.index()
                        );
                    }
                    continue;
                }

                // Check each fact separately. Safety holds iff ALL facts give Unsat.
                let mut all_unsat = true;
                for (fi, fact) in relevant_facts.iter().enumerate() {
                    if self.is_cancelled() {
                        return None;
                    }
                    let crate::ClauseHead::Predicate(_, fact_head_args) = &fact.head else {
                        continue;
                    };
                    let fact_constraint =
                        fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

                    if fact_head_args.len() != query_args.len() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: acyclic_safety: query {} fact {} arity mismatch, bailing",
                                i,
                                fi
                            );
                        }
                        return None;
                    }

                    // Build: fact_constraint AND query_constraint AND (fact_args = query_args)
                    let mut conjuncts = vec![fact_constraint, query_constraint.clone()];
                    for (fa, qa) in fact_head_args.iter().zip(query_args.iter()) {
                        conjuncts.push(ChcExpr::eq(fa.clone(), qa.clone()));
                    }

                    let check = ChcExpr::and_all(conjuncts);
                    let bounded = self.bound_int_vars(check);
                    // #7984: Use persistent executor backend for integer arithmetic.
                    match self.check_sat_via_executor_backend(&bounded) {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {}
                        SmtResult::Sat(_) => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: acyclic_safety: query {} fact {} is Sat, cannot prove safety",
                                    i, fi
                                );
                            }
                            all_unsat = false;
                            break;
                        }
                        SmtResult::Unknown => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: acyclic_safety: query {} fact {} Unknown, bailing",
                                    i,
                                    fi
                                );
                            }
                            return None;
                        }
                    }
                }

                if !all_unsat {
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: acyclic_safety: query {} proven unreachable ({} facts checked)",
                        i,
                        relevant_facts.len()
                    );
                }
            } else {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: acyclic_safety: query {} has {} body predicates, bailing",
                        i,
                        query.body.predicates.len()
                    );
                }
                return None;
            }
        }

        // All queries are unreachable from facts.
        if self.config.verbose {
            safe_eprintln!(
                "PDR: acyclic_safety: all {} queries proven safe",
                queries.len()
            );
        }

        // Build model: each predicate maps to its fact-based invariant.
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();
            let formula = match pred_fact_constraints.get(&pred.id) {
                Some(disjuncts) if !disjuncts.is_empty() => {
                    if disjuncts.len() == 1 {
                        disjuncts[0].clone()
                    } else {
                        ChcExpr::or_all(disjuncts.clone())
                    }
                }
                _ => ChcExpr::Bool(false),
            };
            model.set(pred.id, PredicateInterpretation::new(vars, formula));
        }

        // Verify the model through normal verification pipeline.
        if self.verify_model(&model) {
            Some(model)
        } else {
            if self.config.verbose {
                safe_eprintln!("PDR: acyclic_safety: model fails verification, bailing");
            }
            None
        }
    }

    /// Build a trivial counterexample (initial state violates safety)
    pub(in crate::pdr::solver) fn build_trivial_cex(&self) -> Counterexample {
        Counterexample {
            steps: Vec::new(),
            witness: None,
            ground_derivation: None,
        }
    }
}
