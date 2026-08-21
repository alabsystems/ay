// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Safety-proof checks based on discovered invariants.

use super::*;

impl PdrSolver {
    pub(super) fn must_reverify_bv_single_predicate_inductive_subset_candidate(
        &self,
        model: &InvariantModel,
    ) -> bool {
        // #7964: Only force cascade reverification for NATIVE BV
        // single-predicate problems, not BvToBool-expanded ones.
        // BvToBool expansion removes BV sorts (has_bv_sorts() = false)
        // but sets bv_bit_groups. BvToBool transitions are fully
        // expanded to Boolean logic, so frame-relative self-inductive
        // models are reliable. Native BV problems retain BV sorts
        // and can produce models that pass frame-relative checks but
        // fail whole-model verification on the real BV transition
        // surface.
        let is_native_bv = self.problem.has_bv_sorts();
        is_native_bv && self.problem.predicates().len() == 1 && !model.individually_inductive
    }

    /// Check if discovered invariants in frame 1 prove that all error states are unreachable.
    ///
    /// This is a direct safety check that bypasses the iterative PDR loop when we've
    /// already discovered enough invariants during the discovery phase.
    ///
    /// For each error clause (predicate(vars) ∧ error_constraint → false), we check if:
    /// - The invariants in frame 1 for that predicate, combined with the error_constraint,
    ///   form an unsatisfiable formula.
    ///
    /// This is particularly effective for benchmarks like gj2007 where:
    /// - Equality invariants (A = B) and counting invariants (A = 5*C) are discovered
    /// - Combined with error constraint (A >= 5*C ∧ B ≠ 5*C), the formula becomes UNSAT
    pub(in crate::pdr::solver) fn check_invariants_prove_safety(
        &mut self,
    ) -> Option<InvariantModel> {
        self.check_invariants_prove_safety_impl(false)
    }

    /// Check if discovered invariants prove safety.
    ///
    /// `algebraic_fast`: when true, only try the algebraic-only model and
    /// skip the expensive inductive-subset computation. Used during early
    /// safety checks in multi-predicate startup to avoid wasting 6-10s on
    /// SMT calls for the inductive subset when the algebraic model is
    /// unlikely to be sufficient. (#5425)
    pub(in crate::pdr::solver) fn check_invariants_prove_safety_impl(
        &mut self,
        algebraic_fast: bool,
    ) -> Option<InvariantModel> {
        if self.frames.len() < 2 {
            return None;
        }

        // Collect all query (error) clauses
        let queries: Vec<_> = self
            .problem
            .clauses()
            .iter()
            .filter(|c| c.is_query())
            .cloned()
            .collect();

        if queries.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: no query clauses found ({} total clauses)",
                    self.problem.clauses().len()
                );
            }
            return None;
        }

        // For each query, check if discovered invariants prove it unreachable
        for query in &queries {
            // #2887: Check cancellation between SMT queries.
            if self.is_cancelled() {
                return None;
            }
            // Handle queries with 0 body predicates from multi-def inlining.
            // The query is just constraint->false; safety requires UNSAT.
            if query.body.predicates.is_empty() {
                let constraint = match &query.body.constraint {
                    Some(c) => c.clone(),
                    None => return None,
                };
                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&constraint, std::time::Duration::from_millis(500))
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety: 0-pred query UNSAT (trivially safe)"
                            );
                        }
                        continue;
                    }
                    _ => return None,
                }
            }
            // Get the predicate from the error clause body.
            // Multi-body queries (multiple predicates in error clause) are not
            // supported — conservatively bail rather than silently skipping.
            if query.body.predicates.len() != 1 {
                return None;
            }
            let (pred_id, body_args) = &query.body.predicates[0];
            let pred = *pred_id;

            // Get canonical variables for this predicate
            let canonical_vars = match self.canonical_vars(pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Build variable mapping from body args to canonical vars
            // #2492: Also extract constituent vars from expression body args
            let mut var_map: FxHashMap<String, ChcVar> = FxHashMap::default();
            for (arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        var_map.insert(v.name.clone(), canon.clone());
                    }
                    expr => {
                        for v in expr.vars() {
                            var_map
                                .entry(v.name.clone())
                                .or_insert_with(|| canon.clone());
                        }
                    }
                }
            }

            // Convert error constraint to canonical form
            let error_constraint = match &query.body.constraint {
                Some(c) => match Self::to_canonical(c, &var_map) {
                    Some(ec) => ec,
                    None => continue,
                },
                None => continue,
            };

            // Collect all invariants from frame 1 for this predicate
            let mut invariants: Vec<ChcExpr> = Vec::new();
            for lemma in &self.frames[1].lemmas {
                if lemma.predicate == pred {
                    invariants.push(lemma.formula.clone());
                }
            }

            if invariants.is_empty() {
                // No invariants for the query predicate directly.
                // #1306: Try backward-chain check: for each clause that defines this
                // predicate, substitute the source predicate's invariants through the
                // transition constraint. If ALL defining clauses make the error
                // unreachable, safety is proven.
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: check_invariants_prove_safety: pred {} has no invariants; trying backward-chain check",
                        pred.index()
                    );
                }
                let backward_ok =
                    self.check_backward_chain_safety(pred, &error_constraint, &canonical_vars);
                if backward_ok {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} backward-chain UNSAT (good!)",
                            pred.index()
                        );
                    }
                    // #1306: Derive an invariant for this predicate from the
                    // backward-chain proof. The backward-chain proved that the
                    // error constraint is unreachable, so ¬error is a valid
                    // invariant. Push it to frame 1 so the model builder picks
                    // it up. Without this, the model has `true` for this predicate,
                    // and query-only verification fails because `true ∧ error` is SAT.
                    let not_error = ChcExpr::not(error_constraint.clone());
                    let lemma = Lemma::new(pred, not_error, 1);
                    if self.frames.len() > 1 {
                        self.frames[1].add_lemma(lemma);
                    }
                    continue;
                }
                return None;
            }

            // #5930: If the predicate has Real-sorted variables but no invariant
            // mentions any Real variable, the invariants are a Boolean/Int-only
            // overapproximation that cannot prove safety for Real-sorted problems.
            // PDR's invariant discovery (sums, bounds, etc.) operates on Int/Bool;
            // Real variables are invisible to it. A Boolean-only invariant that
            // proves error unreachable in the Bool projection may miss feasible
            // paths through Real-valued state space.
            let pred_has_real = canonical_vars.iter().any(|v| v.sort == ChcSort::Real);
            // Also check problem-level for Real in nested sorts (e.g., Array(_, Real))
            let problem_has_real = self.problem.has_real_sorts();
            if pred_has_real || problem_has_real {
                let any_invariant_mentions_real = invariants
                    .iter()
                    .any(|inv| inv.vars().iter().any(|v| v.sort == ChcSort::Real));
                if !any_invariant_mentions_real {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} has Real-sorted vars \
                             but invariants are Bool/Int-only; cannot prove safety (#5930)",
                            pred.index()
                        );
                    }
                    return None;
                }
            }

            // Build conjunction: invariants ∧ error_constraint
            let inv_conjunction = invariants
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));

            let combined = ChcExpr::and(inv_conjunction.clone(), error_constraint.clone());

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: checking pred {} with combined formula",
                    pred.index()
                );
            }

            // Fast path: syntactic contradiction check.
            // If any invariant is the direct negation of the error constraint (or a
            // conjunct of it), the combined formula is trivially UNSAT. This handles
            // cases like const_mod_2 where invariant `(= (mod var k) 0)` directly
            // contradicts error `(not (= (mod var k) 0))`, avoiding expensive SMT
            // calls that can fail due to mod elimination budget limits on large moduli.
            let syntactic_unsat =
                Self::error_contradicts_invariants(&error_constraint, &self.frames[1].lemmas, pred);

            if syntactic_unsat {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: check_invariants_prove_safety: pred {} error UNSAT (syntactic contradiction)",
                        pred.index()
                    );
                }
                // Continue checking other queries
                continue;
            }

            // Mod-substitution: if we have invariant (= (mod X k) Y), substitute
            // (mod X k) → Y in the error constraint. This handles cases like const_mod_3
            // where the SMT solver can't reason about multiple `mod` expressions in
            // conjunction with the invariant. (#3211)
            let simplified_error =
                Self::apply_mod_substitution(&error_constraint, &self.frames[1].lemmas, pred);
            let (check_error, check_combined) = if let Some(ref simp) = simplified_error {
                let simp_combined = ChcExpr::and(inv_conjunction.clone(), simp.clone());
                // Re-check syntactic contradiction on simplified formula
                let simp_syntactic =
                    Self::error_contradicts_invariants(simp, &self.frames[1].lemmas, pred);
                if simp_syntactic {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} error UNSAT (syntactic after mod-subst)",
                            pred.index()
                        );
                    }
                    continue;
                }
                (simp.clone(), simp_combined)
            } else {
                (error_constraint.clone(), combined)
            };

            // Check if combined formula is UNSAT
            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&check_combined, std::time::Duration::from_secs(2))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} error UNSAT (good!)",
                            pred.index()
                        );
                    }
                    // Do NOT add NOT(error_constraint) as a blocking lemma. While
                    // invariants AND error being UNSAT means NOT(error) follows from the
                    // current frame[1] invariants, frame[1] may contain non-inductive
                    // lemmas (e.g., pc<=0 on reachable_abort_unsafe_000). The combined
                    // check uses ALL frame[1] lemmas including non-inductive ones, so
                    // NOT(error) derived this way may not hold in all reachable states.
                    // Adding it as an algebraic lemma contaminates the algebraic-only
                    // model, and portfolio verification would reject it. (#5652)
                }
                SmtResult::Sat(model) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} error SAT: {:?}",
                            pred.index(),
                            model
                        );
                    }

                    // #5652: The frozen-var SAT fallback is DISABLED. The combined
                    // invariants-and-error check says error IS reachable given current
                    // invariants. The frozen-var check used frame-1 invariants to
                    // establish "frozen-ness", but frame-1 invariants may not be
                    // transition-inductive. On reachable_abort_unsafe_000, this
                    // incorrectly concluded pc was frozen (using non-inductive pc=0
                    // bound) and overrode the SAT result, producing false SAT.

                    // Error is reachable according to invariants - can't prove safety this way
                    return None;
                }
                SmtResult::Unknown => {
                    // Try splitting disequalities: (not (= a b)) -> (< a b) OR (> a b)
                    // Check if BOTH branches are UNSAT (which means original is UNSAT)
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: pred {} unknown, trying disequality split",
                            pred.index()
                        );
                    }

                    // Extract disequalities and replace with strict inequalities
                    let diseqs = Self::extract_disequalities(&check_error);
                    if diseqs.is_empty() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety: pred {} unknown (no disequalities)",
                                pred.index()
                            );
                        }
                        return None;
                    }

                    // For each disequality (a != b), check:
                    // 1. invariants ∧ error_constraint[a != b -> a < b] is UNSAT
                    // 2. invariants ∧ error_constraint[a != b -> a > b] is UNSAT
                    // If BOTH are UNSAT, then original is UNSAT.
                    let mut all_unsat = true;
                    for (lhs, rhs) in diseqs {
                        // Try lhs < rhs
                        let lt_constraint = check_error.replace_diseq(
                            &lhs,
                            &rhs,
                            ChcExpr::lt(lhs.clone(), rhs.clone()),
                        );
                        let combined_lt = ChcExpr::and(inv_conjunction.clone(), lt_constraint);

                        self.smt.reset();
                        let lt_result = self.smt.check_sat_with_timeout(
                            &combined_lt,
                            std::time::Duration::from_secs(2),
                        );

                        // Try lhs > rhs
                        let gt_constraint = check_error.replace_diseq(
                            &lhs,
                            &rhs,
                            ChcExpr::gt(lhs.clone(), rhs.clone()),
                        );
                        let combined_gt = ChcExpr::and(inv_conjunction.clone(), gt_constraint);

                        self.smt.reset();
                        let gt_result = self.smt.check_sat_with_timeout(
                            &combined_gt,
                            std::time::Duration::from_secs(2),
                        );

                        match (lt_result, gt_result) {
                            (
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_),
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_),
                            ) => {
                                // Both branches UNSAT - this disequality is handled
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: check_invariants_prove_safety: diseq split UNSAT for {} != {}",
                                        lhs, rhs
                                    );
                                }
                            }
                            _ => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: check_invariants_prove_safety: diseq split failed for {} != {}",
                                        lhs, rhs
                                    );
                                }
                                all_unsat = false;
                                break;
                            }
                        }
                    }

                    if !all_unsat {
                        return None;
                    }
                    // All disequality splits proven UNSAT - continue to check other queries
                }
            }
        }

        // All queries proven unreachable! Build model from frame 1 invariants.
        if self.config.verbose {
            safe_eprintln!("PDR: check_invariants_prove_safety: all queries proven unreachable!");
        }

        // (#5970): When the startup fixpoint converged (frame[0] = frame[1]),
        // the full frame conjunction is inductive by definition. Build the model
        // from the full frame with convergence_proven tracking. If no conjuncts
        // were filtered by filter_non_canonical_conjuncts, convergence_proven is
        // set and the caller can skip the expensive inductiveness verification
        // cascade (verify_model_fast, filtered models, etc.).
        //
        // #8578 SOUNDNESS FIX: Startup convergence on acyclic multi-predicate
        // problems does NOT guarantee correctness. The startup fixpoint loop
        // discovers invariants via heuristic passes (bound discovery, equality
        // discovery), not through the standard PDR blocking loop. On acyclic
        // problems (no self-loops), wrong invariants are never refuted by self-
        // loop inductiveness checks, so the fixpoint converges with wrong
        // lemmas. Skip the convergence_proven fast-path when any predicate
        // with non-trivial frame lemmas has no self-loop clauses.
        // #4751: the convergence claim ("frame conjunction inductive because
        // the fixpoint converged") is stale once any later discovery pass
        // (affine kernel, entry-value bounds, parity) has added frame[1]
        // lemmas after the convergence snapshot. In that case skip the
        // fast-path so the inductive-subset/cascade filtering below can
        // extract a genuinely inductive model instead of shipping the raw
        // frame to strict validation (which would demote it).
        let frame1_unchanged_since_convergence = self
            .startup_converged_frame1_len
            .is_some_and(|n| self.frames.get(1).is_some_and(|f| f.lemmas.len() == n));
        if self.startup_converged
            && frame1_unchanged_since_convergence
            && self.problem.predicates().len() > 1
        {
            let has_acyclic_predicate_with_lemmas = self.problem.predicates().iter().any(|pred| {
                let has_lemmas = self.frames[1].lemmas.iter().any(|l| l.predicate == pred.id);
                if !has_lemmas {
                    return false;
                }
                // Check if this predicate has any self-loop clause
                // (a clause where head=pred and body contains pred).
                let has_self_loop = self
                    .problem
                    .clauses_defining(pred.id)
                    .any(|clause| clause.body.predicates.iter().any(|(bp, _)| *bp == pred.id));
                !has_self_loop
            });

            if has_acyclic_predicate_with_lemmas {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: check_invariants_prove_safety: startup converged but problem has acyclic predicates with lemmas; skipping convergence_proven fast-path (#8578)"
                    );
                }
            } else {
                let convergence_model = self.build_model_from_frame_for_convergence(1);
                if convergence_model.convergence_proven {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: startup converged + no filtering => convergence_proven model"
                        );
                    }
                    return Some(convergence_model);
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: check_invariants_prove_safety: startup converged but conjuncts were filtered; continuing cascade"
                    );
                }
            }
        }

        let model = self.build_model_from_frame(1);

        // SOUNDNESS FIX #5723/#5745: The frame-1 model includes ALL lemmas
        // (not just algebraically-verified ones), and non-algebraic lemmas
        // may not be transition-inductive. The model is returned for portfolio
        // validation which always checks transitions. The algebraic-only fast
        // path below returns a model containing only algebraically-verified lemmas.
        let has_algebraic_mod = self.frames[1].lemmas.iter().any(|lemma| {
            lemma.algebraically_verified
                && matches!(&lemma.formula, ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2
                    && (matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, _))
                        || matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mod, _))))
        });

        if has_algebraic_mod && self.problem.predicates().len() == 1 {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: algebraic mod detected (single-predicate), portfolio will validate transitions"
                );
            }
            // Portfolio always validates transitions (#5745).
        }

        // #5652: The frozen-var fast path is REMOVED.
        // Frozen-var proofs used frame-1 invariants which may not be transition-
        // inductive. On reachable_abort_unsafe_000, this produced false SAT.
        // All models must now pass portfolio transition validation.

        // #5540: The multi-predicate algebraic mod+bound fast path is REMOVED.
        // It previously returned Some(model) without verify_model, claiming
        // "invariants are correct by construction." This claim is FALSE:
        // accumulator_unsafe_000 produced a false SAT because the algebraic
        // analysis does not cover cross-predicate transition correctness
        // for multi-predicate problems. The portfolio's transition validation catches
        // these bad models. Let the normal verification pipeline handle all multi-
        // predicate models.

        // Fast path: build model from ONLY algebraically-verified lemmas and check
        // if it blocks all errors. This avoids the expensive verify_model cascade
        // when sum/affine invariants alone prove safety (#5401).
        {
            let has_algebraic_lemmas = self.frames[1]
                .lemmas
                .iter()
                .any(|lemma| lemma.algebraically_verified);

            if has_algebraic_lemmas {
                let alg_model = self.build_model_from_algebraic_lemmas(1);
                let alg_blocks_errors =
                    self.algebraic_model_blocks_all_errors(&alg_model, &queries);

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: check_invariants_prove_safety: algebraic-only model blocks errors: {}",
                        alg_blocks_errors
                    );
                }

                if alg_blocks_errors {
                    // Quick verify_model check: the algebraic-only model may block
                    // all error clauses but fail transition clause checks when
                    // propagated cross-predicate invariants (not algebraically
                    // verified) are needed. For example, s_multipl_17 requires
                    // (mod __p1_a0 6) = 0 propagated from pred 0 to pred 1, but
                    // propagated lemmas don't have algebraically_verified set.
                    // If verify_model fails, fall through to inductive-subset
                    // which includes propagated lemmas that pass self-inductiveness.
                    if self.verify_model(&alg_model) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety: accepting algebraic-only model ({} predicates)",
                                self.problem.predicates().len()
                            );
                        }
                        return Some(alg_model);
                    } else {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety: algebraic-only model blocks errors but fails verify_model; trying inductive-subset"
                            );
                        }
                        // When algebraic_fast, bail immediately. The model
                        // lacks invariants (e.g., parity) that haven't been
                        // discovered yet. Running the cascade wastes budget.
                        if algebraic_fast {
                            return None;
                        }
                    }
                }
            }
        }

        // #5877: For BvToInt-relaxed encoding (single-predicate), accept the model
        // directly when all queries are proven unreachable. In this encoding,
        // individual inductiveness checks and whole-model verify_model_with_budget
        // both fail due to integer counterexamples that are infeasible in the
        // original BV domain. The portfolio's back-translation verification re-checks
        // the model against the original BV-sorted problem.
        //
        // Only for single-predicate: multi-predicate problems need cross-predicate
        // transition verification that self-inductiveness doesn't cover.
        if self.config.bv_to_int_relaxed && self.problem.predicates().len() == 1 {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: BvToInt-relaxed single-pred: accepting model (all queries unreachable) (#5877)"
                );
            }
            let mut model = model;
            model.individually_inductive = true;
            return Some(model);
        }

        // Inductive-subset fast-accept (delegated to safety_proof_inductive.rs)
        if !algebraic_fast {
            use super::safety_proof_inductive::InductiveSubsetOutcome;

            match self.try_inductive_subset_model(&queries, model) {
                InductiveSubsetOutcome::Proven(m) => {
                    // #7964: On native-BV single-predicate problems, the
                    // inductive-subset "blocks all errors" check can still
                    // produce a candidate that later fails whole-model
                    // verification on the real query/transition surface
                    // (simple.c_000 / simple sendmail canary). Only trust
                    // strictly self-inductive models directly; all other BV
                    // single-predicate candidates must go through the normal
                    // verification cascade before they are exposed as a
                    // direct safety proof.
                    if self.must_reverify_bv_single_predicate_inductive_subset_candidate(&m) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety: re-verifying BV single-predicate inductive-subset candidate via cascade (#7964)"
                            );
                        }
                        return self.try_model_verification_cascade(m);
                    }
                    return Some(m);
                }
                InductiveSubsetOutcome::Cascade(m) => {
                    return self.try_model_verification_cascade(m);
                }
            }
        }

        // Model verification cascade (delegated to safety_proof_cascade.rs)
        self.try_model_verification_cascade(model)
    }
}
