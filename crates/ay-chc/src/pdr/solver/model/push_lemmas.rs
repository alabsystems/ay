// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma propagation and consecution checking for PDR frames.

use super::super::{
    build_frame_predicate_lemma_counts, compute_push_cache_signature, ChcExpr, ChcOp, Lemma,
    PdrSolver, SmtResult,
};

impl PdrSolver {
    /// Push lemmas from frame k to frame k+1 if they are inductive
    ///
    /// A lemma NOT(s) at level k can be pushed to level k+1 if:
    /// - Frame[k] /\ T => NOT(s)'  (lemma holds after one transition from frame k)
    pub(in crate::pdr::solver) fn push_lemmas(&mut self) {
        // Precondition: at least 2 frames (frame 0 is init, frame 1+ are PDR frames) (#4757).
        debug_assert!(
            self.frames.len() >= 2,
            "BUG: push_lemmas requires at least 2 frames, got {}",
            self.frames.len()
        );

        // Process frames from low to high
        for k in 1..self.frames.len().saturating_sub(1) {
            // #2956 Finding 1: avoid cloning the entire Vec<Lemma> upfront.
            // Instead, snapshot the count and clone individual lemmas on-demand.
            // Most lemmas hit the cache or duplicate check and are skipped without
            // any clone. Only lemmas reaching can_push_lemma or push need cloning.
            let num_lemmas = self.frames[k].lemmas.len();
            let frame_sig_counts = build_frame_predicate_lemma_counts(&self.frames[k]);

            if self.config.verbose {
                safe_eprintln!("PDR: push_lemmas: level {}, {} lemmas", k, num_lemmas);
            }

            for idx in 0..num_lemmas {
                // Check cancellation in inner push loop to respond to cooperative timeouts
                if self.is_cancelled() {
                    return;
                }

                // Extract Copy fields by indexing — no clone needed.
                let predicate = self.frames[k].lemmas[idx].predicate;
                let formula_hash = self.frames[k].lemmas[idx].formula_hash;

                // O(1) duplicate check using precomputed hash (#1036, #perf).
                // Uses contains_lemma_with_hash to avoid redundant O(|formula|)
                // structural_hash() tree walk — formula_hash is already cached in Lemma.
                if self.frames[k + 1].contains_lemma_with_hash(
                    predicate,
                    &self.frames[k].lemmas[idx].formula,
                    formula_hash,
                ) {
                    continue;
                }

                let lemma_key = (k, predicate.index(), formula_hash);
                let dep_preds = self
                    .caches
                    .push_cache_deps
                    .get(&predicate)
                    .map_or(&[] as &[_], Vec::as_slice);
                let frame_sig = compute_push_cache_signature(&frame_sig_counts, dep_preds);

                // Check push cache — compare formula by ref through index.
                if let Some((cached_expr, cached_frame_sig, cached_can_push)) =
                    self.caches.push_cache.get(&lemma_key)
                {
                    // Collision safety (#2860): verify expression matches before using cache.
                    if *cached_expr == self.frames[k].lemmas[idx].formula {
                        if *cached_can_push {
                            // Mark source lemma as used — it survived push (#8601)
                            self.frames[k].lemmas[idx].mark_used();
                            // Clone only the single lemma that will be pushed.
                            let mut pushed = self.frames[k].lemmas[idx].clone();
                            pushed.level = k + 1;
                            let pushed_pred = pushed.predicate;
                            let pushed_formula = pushed.formula.clone();
                            self.emit_lemma_lifecycle_event(
                                "push",
                                "push_cache_hit",
                                pushed.predicate,
                                k + 1,
                                &pushed.formula,
                            );
                            self.add_lemma_to_frame(pushed, k + 1);
                            self.try_cross_predicate_propagation(pushed_pred, &pushed_formula, k);
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Pushed lemma {} to level {}",
                                    self.frames[k].lemmas[idx].formula,
                                    k + 1
                                );
                            }
                            continue;
                        }
                        if *cached_frame_sig == frame_sig {
                            continue;
                        }
                    }
                    // Expression mismatch (collision) - fall through to recompute
                }

                // Try to push this lemma to frame k+1.
                // Clone the individual lemma for can_push_lemma (needs &Lemma while &mut self).
                let lemma = self.frames[k].lemmas[idx].clone();
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Trying to push lemma {}/{}: {}",
                        idx + 1,
                        num_lemmas,
                        lemma.formula
                    );
                }
                let can_push = self.can_push_lemma(&lemma, k);
                // Store with expression for collision detection (#2860)
                self.insert_push_cache_entry(
                    lemma_key,
                    (lemma.formula.clone(), frame_sig, can_push),
                );
                if can_push {
                    // INVARIANT: Lemma passed inductiveness check, safe to push.
                    assert!(
                        k + 1 < self.frames.len(),
                        "BUG: Pushing lemma to level {} but only {} frames exist",
                        k + 1,
                        self.frames.len()
                    );
                    // Mark source lemma as used — it survived push (#8601)
                    self.frames[k].lemmas[idx].mark_used();
                    let mut pushed = lemma;
                    pushed.level = k + 1;
                    self.emit_lemma_lifecycle_event(
                        "push",
                        "push_smt_verified",
                        pushed.predicate,
                        k + 1,
                        &pushed.formula,
                    );
                    // #2459: Route through add_lemma_to_frame for cross-predicate
                    // propagation without restart accounting (push is not blocking).
                    let pushed_pred = pushed.predicate;
                    let pushed_formula = pushed.formula.clone();
                    self.add_lemma_to_frame(pushed, k + 1);
                    self.try_cross_predicate_propagation(pushed_pred, &pushed_formula, k);
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Pushed lemma {} to level {}",
                            self.frames[k].lemmas[idx].formula,
                            k + 1
                        );
                    }
                } else {
                    let lemma_ref = &self.frames[k].lemmas[idx];
                    // #2804/#5347: Log when a discovery-shaped lemma fails inductiveness.
                    // This was previously an unconditional BUG message, but IC3 interpolation
                    // also produces `Var >= Const` lemmas that match `is_discovered_invariant()`.
                    // Non-inductive lemmas at level 1 are normal PDR behavior for IC3-learned
                    // lemmas. Guard behind verbose to avoid false-positive diagnostic noise.
                    if self.config.verbose
                        && lemma_ref.level == 1
                        && Self::is_discovered_invariant(&lemma_ref.formula)
                    {
                        safe_eprintln!(
                            "PDR: discovery-shaped lemma failed inductiveness check at level {} \
                             (may be IC3-learned, not necessarily a discovery bug): {}",
                            k,
                            lemma_ref.formula
                        );
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Cannot push lemma {} (not inductive at level {})",
                            lemma_ref.formula,
                            k
                        );
                    }
                }
            }
        }
    }

    /// Check if a lemma can be pushed from level k to level k+1
    ///
    /// A lemma NOT(blocked_state) can be pushed if:
    /// - For all transitions T: Frame[k] /\ T /\ blocked_state' is UNSAT
    ///
    /// A positive invariant L can be pushed if:
    /// - For all transitions T: Frame[k] /\ T => L' (in the post-state)
    /// - Equivalently: Frame[k] /\ T /\ NOT(L') is UNSAT
    pub(in crate::pdr::solver) fn can_push_lemma(&mut self, lemma: &Lemma, level: usize) -> bool {
        // #5653 Phase 1A: ALL lemmas get full SMT inductiveness check during push.
        // Previously, 75% of discovered invariants at level 1 skipped this check
        // in release builds (spot-check mask 0x03). This made frame convergence
        // detection unsound — can_push_lemma returning true without proof meant
        // the Knaster-Tarski fixed-point argument did not hold.
        // Removing the skip ensures frame convergence is a complete proof.
        // Extract what we need to check is UNSAT in the post-state
        // For NOT(blocked_state): check blocked_state' is UNSAT
        // For positive invariant L: check NOT(L') is UNSAT
        let blocked_state = match &lemma.formula {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => (*args[0]).clone(),
            // Positive invariant: we need to check NOT(L') is UNSAT
            positive => ChcExpr::not(positive.clone()),
        };
        // Now blocked_state is what we check for reachability (should be UNSAT)
        // For blocking lemma NOT(s): blocked_state = s, check s' is UNSAT
        // For positive invariant L: blocked_state = NOT(L), check NOT(L') is UNSAT
        macro_rules! record_push_countermodel {
            ($model:expr, $head_args:expr) => {{
                let canonical_vars = self
                    .canonical_vars(lemma.predicate)
                    .map(|vars| vars.to_vec());
                let frame_epoch = self.frames_lemma_epoch();
                super::super::core::record_validated_blocking_countermodel_from_head_args(
                    &mut self.caches.implication_cache,
                    frame_epoch,
                    canonical_vars.as_deref(),
                    lemma.predicate,
                    level,
                    $head_args,
                    $model,
                    &blocked_state,
                );
            }};
        }

        // Drop countermodels recorded against older (weaker) frame states
        // before consulting the fast path (#pdr-chain).
        let push_frame_epoch = self.frames_lemma_epoch();
        self.caches
            .implication_cache
            .note_frame_epoch(push_frame_epoch);
        // LAWI-style fast path: check if cached countermodel shows blocked_state is reachable
        if self.caches.implication_cache.blocking_rejected_by_cache(
            lemma.predicate.index(),
            level,
            &blocked_state,
        ) {
            return false;
        }

        // #5877: Non-pure-LIA push queries go through `check_sat_with_ite_case_split`,
        // which otherwise falls back to a 2s default timeout. BV/mod-heavy
        // inductiveness queries routinely exceed that budget, so install a
        // larger default here while preserving any outer caller timeout.
        let _non_lia_push_timeout = if self.problem_is_pure_lia {
            None
        } else {
            let push_timeout = self
                .smt
                .current_timeout()
                .or(Some(std::time::Duration::from_secs(10)));
            Some(self.smt.scoped_check_timeout(push_timeout))
        };

        // For each clause that can produce states for this predicate
        for (clause_index, clause) in self.problem.clauses_defining_with_index(lemma.predicate) {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Apply blocked_state to head args (post-state)
            let blocked_on_head =
                match self.apply_to_args(lemma.predicate, &blocked_state, head_args) {
                    Some(e) => e,
                    None => return false,
                };
            // #2515: Match Spacer's is_invariant rule-tag semantics by including
            // clause-guarded propagated lemmas only for this active clause.
            // #2536: Level-aware — only include lemmas valid at this push level.
            let guarded =
                self.clause_guarded_constraint(lemma.predicate, clause_index, head_args, level);

            // Negated equality splitting: ¬(a = b) → (a < b) ∨ (a > b)
            // Controlled by config. Helps dillig-style benchmarks but doubles queries (#470).
            // Portfolio runs both configs (#491).
            let negated_equality_splits = if self.config.use_negated_equality_splits {
                match &blocked_on_head {
                    ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                        if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                            if eq_args.len() == 2 {
                                let a = eq_args[0].as_ref().clone();
                                let b = eq_args[1].as_ref().clone();
                                Some([ChcExpr::lt(a.clone(), b.clone()), ChcExpr::gt(a, b)])
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            } else {
                None
            };

            // Fact clause (no predicates in body): check if fact can produce blocked state
            if clause.body.predicates.is_empty() {
                if let Some(ref splits) = negated_equality_splits {
                    let mut all_unsat = true;
                    for split in splits {
                        // #8660 Phase 2b: ROW-expand before dispatch so push-lemma
                        // queries with symbolic store indices reduce to LIA+ITE.
                        let query = ChcExpr::and_all([
                            clause_constraint.clone(),
                            guarded.clone(),
                            split.clone(),
                        ])
                        .expand_select_store_symbolic();
                        let (result, _sat_query) = Self::check_sat_with_ite_case_split(
                            &mut self.smt,
                            self.config.verbose,
                            &query,
                        );
                        match result {
                            SmtResult::Sat(ref model) => {
                                record_push_countermodel!(model, head_args);
                                return false;
                            }
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {}
                            SmtResult::Unknown => {
                                all_unsat = false;
                            }
                        }
                    }
                    if all_unsat {
                        continue;
                    }
                }
                // #8660 Phase 2b: ROW-expand before dispatch.
                let query = ChcExpr::and_all([
                    clause_constraint.clone(),
                    guarded.clone(),
                    blocked_on_head.clone(),
                ])
                .expand_select_store_symbolic();
                let (result, _sat_query) =
                    Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
                match result {
                    SmtResult::Sat(ref model) => {
                        record_push_countermodel!(model, head_args);
                        return false;
                    } // Fact can produce blocked state
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            }

            // Hyperedge clause (multiple body predicates)
            if clause.body.predicates.len() > 1 {
                let mut body_constraints = Vec::with_capacity(clause.body.predicates.len());
                for (body_pred, body_args) in &clause.body.predicates {
                    let frame_constraint = self.frames[level]
                        .get_predicate_constraint(*body_pred)
                        .unwrap_or(ChcExpr::Bool(true));
                    match self.apply_to_args(*body_pred, &frame_constraint, body_args) {
                        Some(e) => body_constraints.push(e),
                        None => return false,
                    }
                }
                let all_body_constraints = ChcExpr::and_all(body_constraints);
                if let Some(ref splits) = negated_equality_splits {
                    let mut all_unsat = true;
                    for split in splits {
                        // #8660 Phase 2b: ROW-expand before dispatch.
                        let query = ChcExpr::and_all([
                            all_body_constraints.clone(),
                            clause_constraint.clone(),
                            guarded.clone(),
                            split.clone(),
                        ])
                        .expand_select_store_symbolic();
                        let (result, _sat_query) = Self::check_sat_with_ite_case_split(
                            &mut self.smt,
                            self.config.verbose,
                            &query,
                        );
                        match result {
                            SmtResult::Sat(ref model) => {
                                record_push_countermodel!(model, head_args);
                                return false;
                            }
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {}
                            SmtResult::Unknown => {
                                all_unsat = false;
                            }
                        }
                    }
                    if all_unsat {
                        continue;
                    }
                }
                // #8660 Phase 2b: ROW-expand before dispatch.
                let query = ChcExpr::and_all([
                    all_body_constraints,
                    clause_constraint.clone(),
                    guarded.clone(),
                    blocked_on_head.clone(),
                ])
                .expand_select_store_symbolic();
                let (result, _sat_query) =
                    Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
                match result {
                    SmtResult::Sat(ref model) => {
                        record_push_countermodel!(model, head_args);
                        return false;
                    } // Can reach blocked state via hyperedge
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            }

            // Linear clause (one predicate in body)
            let (body_pred, body_args) = &clause.body.predicates[0];

            // Get frame constraint at level k for the body predicate
            let frame_constraint = self.frames[level]
                .get_predicate_constraint(*body_pred)
                .unwrap_or(ChcExpr::Bool(true));

            let frame_on_body = match self.apply_to_args(*body_pred, &frame_constraint, body_args) {
                Some(e) => e,
                None => return false,
            };

            // Check: Frame[k] /\ T /\ blocked_state' is SAT?
            // If SAT, then lemma is not inductive (can reach blocked state from frame k)
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: can_push_lemma query for {}: frame_on_body={}",
                    lemma.formula,
                    frame_on_body
                );
            }

            // #6358: Per-predicate prop_solver for can_push_lemma inductiveness.
            // Pure-LIA: one solve via prop_solver, no double-solve fallback.
            if self.incremental_pdr_enabled() && negated_equality_splits.is_none() {
                let seg_key = super::super::prop_solver::SegmentKey::Inductiveness { clause_index };
                let prop = super::super::core::ensure_prop_solver_split(
                    &mut self.prop_solvers,
                    &self.frames,
                    lemma.predicate,
                );
                prop.register_segment(seg_key, &clause_constraint);
                let check_timeout = self
                    .smt
                    .current_timeout()
                    .or(Some(std::time::Duration::from_secs(2)));
                let assumptions = [
                    frame_on_body.clone(),
                    blocked_on_head.clone(),
                    guarded.clone(),
                ];
                let incr_result = prop.check_inductiveness(
                    self.frames.len(),
                    clause_index,
                    &assumptions,
                    check_timeout,
                    None,
                );
                match incr_result {
                    crate::smt::IncrementalCheckResult::Unsat => {
                        continue;
                    }
                    crate::smt::IncrementalCheckResult::Sat(ref model) => {
                        // Pure-LIA: SAT is trusted (no ITE/mod/div).
                        record_push_countermodel!(model, head_args);
                        return false;
                    }
                    crate::smt::IncrementalCheckResult::Unknown => {
                        // Unknown: fall through to non-incremental.
                    }
                }
            }

            if let Some(ref splits) = negated_equality_splits {
                let mut all_unsat = true;
                for split in splits {
                    // #8660 Phase 2b: ROW-expand before dispatch.
                    let query = ChcExpr::and_all([
                        frame_on_body.clone(),
                        clause_constraint.clone(),
                        guarded.clone(),
                        split.clone(),
                    ])
                    .expand_select_store_symbolic();
                    let (result, _sat_query) = Self::check_sat_with_ite_case_split(
                        &mut self.smt,
                        self.config.verbose,
                        &query,
                    );
                    match result {
                        SmtResult::Sat(ref model) => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: can_push_lemma: SAT (not inductive) on split, model={:?}",
                                    model
                                );
                            }
                            record_push_countermodel!(model, head_args);
                            return false;
                        }
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {}
                        SmtResult::Unknown => {
                            all_unsat = false;
                        }
                    }
                }
                if all_unsat {
                    continue;
                }
            }
            // #8660 Phase 2b: ROW-expand before dispatch.
            let query = ChcExpr::and_all([
                frame_on_body.clone(),
                clause_constraint.clone(),
                guarded,
                blocked_on_head.clone(),
            ])
            .expand_select_store_symbolic();
            let (result, _sat_query) =
                Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
            match result {
                SmtResult::Sat(ref model) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: can_push_lemma: SAT (not inductive), model={:?}",
                            model
                        );
                    }
                    record_push_countermodel!(model, head_args);
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                } // This clause doesn't violate inductiveness
                SmtResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: can_push_lemma: Unknown (treating as not inductive)");
                    }
                    return false;
                }
            }
        }

        true // Lemma is inductive at this level
    }
}
