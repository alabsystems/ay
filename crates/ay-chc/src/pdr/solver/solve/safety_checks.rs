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
        let queries: Vec<(usize, crate::HornClause)> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_query())
            .map(|(i, c)| (i, c.clone()))
            .collect();
        for (query_index, query) in &queries {
            if query.body.predicates.is_empty() {
                // No relation needs a producing fact: this query is already
                // a depth-zero violation exactly when its theory guard is
                // satisfiable. Nullary expansion can expose this shape after
                // constant projection. It must not wait for a predicate POB
                // that this clause can never generate.
                let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                match self.check_sat_via_executor_backend(&constraint) {
                    SmtResult::Sat(mut env) => {
                        // Carry the exact depth-zero clause instance. An empty
                        // trace loses this query's satisfying local assignment
                        // and cannot be replayed by a fresh verifier.
                        let owner = self.input_restatement_owner();
                        let _memory = owner.install_memory();
                        if !owner.open() {
                            return InitResult::Interrupted;
                        }
                        let complete = crate::ground_derivation::complete::complete_env_for_clause(
                            query, &mut env,
                        );
                        if !owner.open() {
                            return InitResult::Interrupted;
                        }
                        if !complete {
                            any_unknown = true;
                            continue;
                        }
                        let derivation = crate::ground_derivation::GroundDerivation {
                            steps: vec![crate::ground_derivation::GroundDerivationStep {
                                clause_index: *query_index,
                                env,
                                premises: Vec::new(),
                            }],
                            query_step: 0,
                        };
                        match crate::ground_derivation::validate_ground_derivation_with_progress(
                            &self.problem,
                            &derivation,
                            &mut || owner.open(),
                        ) {
                            Ok(()) => {
                                if !owner.open() {
                                    return InitResult::Interrupted;
                                }
                                return InitResult::UnsafeWithEvidence(
                                    Counterexample::new(Vec::new())
                                        .with_ground_derivation(derivation),
                                );
                            }
                            Err(crate::ground_derivation::GroundDerivationError::Interrupted) => {
                                return InitResult::Interrupted;
                            }
                            Err(_) => any_unknown = true,
                        }
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                    SmtResult::Unknown => any_unknown = true,
                }
                continue;
            }
            if query.body.predicates.len() != 1 {
                // Multi-predicate queries can't be checked against individual
                // facts. Skip rather than bail — PDR will discover unsafety
                // through normal POB processing if needed (#6047).
                any_unknown = true;
                continue;
            }

            let (pred, args) = &query.body.predicates[0];
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            // `bad_state` meets the fact clauses below: the query clause is
            // renamed apart first, so its locals keep fresh names in the
            // canonical state (`rename_clause_apart`).
            let Some(names) = self.source_names() else {
                any_unknown = true;
                continue;
            };
            let Some((constraint, args)) = self.rename_clause_apart(
                &names,
                &format!("__query{query_index}_"),
                &constraint,
                args,
                std::iter::empty(),
            ) else {
                any_unknown = true;
                continue;
            };
            let bad_state = match self.constraint_to_canonical_state(*pred, &args, &constraint) {
                Some(s) => s,
                None => {
                    any_unknown = true;
                    continue;
                }
            };

            let facts: Vec<(usize, crate::HornClause)> = self
                .problem
                .clauses()
                .iter()
                .enumerate()
                .filter(|(_, c)| c.is_fact() && c.head.predicate_id() == Some(*pred))
                .map(|(i, c)| (i, c.clone()))
                .collect();
            for (fact_index, fact) in &facts {
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                // The fact renamed apart as well (`rename_clause_apart`).
                let Some((fact_constraint, head_args)) = self.rename_clause_apart(
                    &names,
                    &format!("__fact{fact_index}_"),
                    &fact_constraint,
                    head_args,
                    [&bad_state],
                ) else {
                    any_unknown = true;
                    continue;
                };
                let head_args = head_args.as_slice();
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

        let facts: Vec<(usize, crate::HornClause)> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_fact() && !c.is_query())
            .map(|(i, c)| (i, c.clone()))
            .collect();

        if queries.is_empty() {
            return None;
        }

        // Collect facts per predicate in canonical vars for model building.
        let mut pred_fact_constraints: FxHashMap<PredicateId, Vec<(usize, ChcExpr)>> =
            FxHashMap::default();
        // Facts a query check below proved unsatisfiable on their own.
        let mut facts_unsat_alone = ay_core::kani_compat::DetHashSet::default();
        for (fact_index, fact) in &facts {
            if let crate::ClauseHead::Predicate(pred_id, head_args) = &fact.head {
                let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                // Renamed apart, the fact's local variables can never be
                // captured by a clause variable of the same name; the model
                // builder (`acyclic_model`) closes them before verification.
                let names = self.source_names()?;
                let (constraint, head_args) = self.rename_clause_apart(
                    &names,
                    &format!("__fact{fact_index}_"),
                    &constraint,
                    head_args,
                    std::iter::empty(),
                )?;
                if let Some(canonical) =
                    self.constraint_to_canonical_state(*pred_id, &head_args, &constraint)
                {
                    pred_fact_constraints
                        .entry(*pred_id)
                        .or_default()
                        .push((*fact_index, canonical));
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
                    .filter(|(_, f)| f.head.predicate_id() == Some(*pred_id))
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
                for (fi, (fact_index, fact)) in relevant_facts.iter().enumerate() {
                    if self.is_cancelled() {
                        return None;
                    }
                    let crate::ClauseHead::Predicate(_, fact_head_args) = &fact.head else {
                        continue;
                    };
                    let fact_constraint =
                        fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                    // Fact and query are separate clauses: rename the fact
                    // apart (`rename_clause_apart`); they meet only through the
                    // positional argument equalities below.
                    let names = self.source_names()?;
                    let (fact_constraint, fact_head_args) = self.rename_clause_apart(
                        &names,
                        &format!("__fact{fact_index}_"),
                        &fact_constraint,
                        fact_head_args,
                        [&query_constraint].into_iter().chain(query_args.iter()),
                    )?;
                    let fact_head_args = fact_head_args.as_slice();

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
                        | SmtResult::UnsatWithFarkas(_) => {
                            // No arguments and a `true` query: the check was the fact alone.
                            if query_args.is_empty()
                                && matches!(query_constraint, ChcExpr::Bool(true))
                            {
                                facts_unsat_alone.insert(*fact_index);
                            }
                        }
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

        // Build model: each predicate maps to its fact-based invariant, with
        // every disjunct closed over fact-local variables (`acyclic_model`).
        let model = self.build_acyclic_safety_model(&pred_fact_constraints, &facts_unsat_alone)?;

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
            compact_derivation: None,
            ground_derivation: None,
        }
    }
}
