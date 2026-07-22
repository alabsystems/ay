// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Select a premise reach_fact at `level` that is consistent with the SMT `model`.
    ///
    /// When must-summaries are disjunctions, there may be multiple reach_facts per (pred, level).
    /// For counterexample reconstruction we prefer a reach_fact whose instantiated state holds
    /// under the transition model that produced the head fact.
    ///
    /// Returns None if no reach_fact can be shown consistent with `model`. This avoids
    /// constructing invalid witness chains that later fail counterexample verification
    /// with positional mismatches (#1685).
    pub(in crate::pdr::solver) fn pick_reach_fact_premise(
        &self,
        predicate: PredicateId,
        level: usize,
        args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ReachFactId> {
        for rf_id in self
            .reachability
            .reach_facts
            .ids_for_predicate_level(predicate, level)
            .iter()
            .copied()
        {
            let Some(rf) = self.reachability.reach_facts.get(rf_id) else {
                continue;
            };
            let Some(applied) = self.apply_to_args(predicate, &rf.state, args) else {
                continue;
            };

            match crate::expr::evaluate_expr(&applied, model) {
                Some(SmtValue::Bool(true)) => return Some(rf_id),
                Some(SmtValue::Bool(false)) => continue,
                Some(_) | None => {}
            }

            // Try again after best-effort augmentation from equalities in the applied formula.
            let mut augmented = model.clone();
            cube::augment_model_from_equalities(&applied, &mut augmented);
            match crate::expr::evaluate_expr(&applied, &augmented) {
                Some(SmtValue::Bool(true)) => return Some(rf_id),
                Some(SmtValue::Bool(false)) => continue,
                Some(_) | None => continue,
            }
        }

        None
    }

    /// Check if a POB state is must-reachable via transition from level-1 (Spacer technique)
    ///
    /// Following Golem/Spacer semantics: check if there's a transition from must-reachable
    /// states at level-1 to the POB state at this level. If yes, the POB state becomes
    /// must-reachable at this level.
    ///
    /// Key insight: must summaries at level K represent states reachable in exactly K steps.
    /// To determine if POB at level K is must-reachable, we check if:
    /// ∃ clause C with body_preds, ∃ must_summaries at level K-1 such that:
    ///   body_must_summaries ∧ clause_constraint ∧ pob_state is SAT
    ///
    /// Returns the state formula and SMT model (for counterexample construction).
    pub(in crate::pdr::solver) fn check_must_reachability(
        &mut self,
        pob: &ProofObligation,
    ) -> Option<ReachFactId> {
        if !self.config.use_must_summaries {
            return None;
        }

        // At level 0, there's no level -1 to check
        // Level 0 must-reachability is established directly from fact clauses
        if pob.level == 0 {
            return None;
        }

        // POSITIVE short-circuit (Option B+): check if POB state intersects a BACKED reach fact.
        // If so, we can return that ReachFactId directly without clause iteration, enabling
        // immediate witness construction. See the development design notes
        if let Some((rf_id, _model)) =
            self.reachability
                .reach_solvers
                .find_match(&mut self.smt, pob.predicate, &pob.state)
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Fast path HIT: POB at level {} for pred {} matched backed reach fact {:?}",
                    pob.level,
                    pob.predicate.index(),
                    rf_id
                );
            }
            return Some(rf_id);
        }

        // NEGATIVE fast path: check if POB state intersects any cached reach fact.
        // If no intersection with any *known* reach fact, skip expensive clause iteration.
        // Note: reach facts are an under-approximation, so this is a best-effort filter.
        // CRITICAL: Only apply this filter when we have cached reach facts for this predicate.
        // When empty, we must proceed with full clause iteration to bootstrap the cache.
        // See the development design notes
        if self.reachability.reach_solvers.has_facts(pob.predicate)
            && !self.reachability.reach_solvers.is_reachable(
                &mut self.smt,
                pob.predicate,
                &pob.state,
            )
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Fast path skip: POB at level {} for pred {} doesn't intersect known reach facts",
                    pob.level,
                    pob.predicate.index()
                );
            }
            return None;
        }

        let prev_level = pob.level - 1;

        // Collect clauses upfront to avoid borrowing self.problem across
        // the mutable self.check_sat_via_executor_backend() call (#7984).
        let clauses_with_idx: Vec<_> = self
            .problem
            .clauses_defining_with_index(pob.predicate)
            .map(|(idx, c)| (idx, c.clone()))
            .collect();
        for (clause_index, clause) in &clauses_with_idx {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            // Get clause constraint
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Apply POB state to head arguments
            let state_on_head = match self.apply_to_args(pob.predicate, &pob.state, head_args) {
                Some(e) => e,
                None => continue,
            };

            // Fact clause: check if POB state satisfies initial constraint directly
            // SOUNDNESS NOTE (#2659): Unknown -> continue (skip clause) is conservative.
            // Must-reachability is a positive assertion; if the SMT check is inconclusive
            // we simply don't establish must-reachability for this clause. The POB will
            // still be processed through normal inductiveness checks.
            if clause.body.predicates.is_empty() {
                let query = self
                    .bound_int_vars(ChcExpr::and_all([clause_constraint.clone(), state_on_head]));
                // #7984: Use persistent executor backend for integer arithmetic.
                if let SmtResult::Sat(model) = self.check_sat_via_executor_backend(&query) {
                    // POB state is directly reachable from init
                    // SOUNDNESS FIX: Return concrete cube, not full POB state
                    // The POB state may be more general than actually reachable states.
                    // For example, POB might have B >= A but init requires B > A.
                    // Use cube_from_model_or_constraints to recover partial models
                    // by augmenting from constraint equalities before falling back
                    // to cube_from_equalities (#3004, #3018).
                    let Some(concrete_state) = self.cube_from_model_or_constraints(
                        pob.predicate,
                        head_args,
                        &query,
                        &model,
                    ) else {
                        continue;
                    };
                    let mut instances = model;
                    cube::extract_equalities_from_formula(&concrete_state, &mut instances);
                    let id = Self::insert_reach_fact_bounded(
                        &mut self.reachability,
                        self.config.verbose,
                        ReachFact {
                            id: ReachFactId(0),
                            predicate: pob.predicate,
                            level: 0,
                            state: concrete_state.clone(),
                            incoming_clause: Some(*clause_index),
                            premises: Vec::new(),
                            instances,
                        },
                    )?;
                    // Add to reach solver as BACKED entry (fact clause has no premises)
                    // for fast short-circuit in future queries
                    self.reachability
                        .reach_solvers
                        .add_backed(pob.predicate, id, concrete_state);
                    return Some(id);
                }
                continue;
            }

            // Collect must summaries for all body predicates at prev_level
            let mut body_must_summaries = Vec::new();
            let mut all_have_must = true;

            for (body_pred, body_args) in &clause.body.predicates {
                if let Some(must_summary) =
                    self.reachability.must_summaries.get(prev_level, *body_pred)
                {
                    // Apply must summary to body arguments
                    if let Some(applied) = self.apply_to_args(*body_pred, &must_summary, body_args)
                    {
                        body_must_summaries.push(applied);
                    } else {
                        all_have_must = false;
                        break;
                    }
                } else {
                    all_have_must = false;
                    break;
                }
            }

            // If all body predicates have must summaries at prev_level, check transition
            // SOUNDNESS NOTE (#2659): Unknown -> continue (try next clause) is conservative.
            // Same as above: must-reachability is best-effort, not required for soundness.
            if all_have_must {
                let mut components = body_must_summaries;
                components.push(clause_constraint.clone());
                components.push(state_on_head);

                let query = self.bound_int_vars(ChcExpr::and_all(components));
                // #7984: Use persistent executor backend for integer arithmetic.
                if let SmtResult::Sat(model) = self.check_sat_via_executor_backend(&query) {
                    // Transition from must-reachable predecessors reaches POB state
                    // SOUNDNESS FIX: Return concrete cube, not full POB state
                    // The POB state may include unreachable points.
                    // Use cube_from_model_or_constraints to recover partial models
                    // by augmenting from constraint equalities before falling back
                    // to cube_from_equalities (#3004, #3018).
                    let Some(concrete_state) = self.cube_from_model_or_constraints(
                        pob.predicate,
                        head_args,
                        &query,
                        &model,
                    ) else {
                        continue;
                    };
                    // For hyperedges, collect ALL premises - verification requires complete chains
                    let mut premises = Vec::new();
                    let mut all_premises_found = true;
                    for (body_pred, body_args) in &clause.body.predicates {
                        if let Some(id) =
                            self.pick_reach_fact_premise(*body_pred, prev_level, body_args, &model)
                        {
                            premises.push(id);
                        } else {
                            all_premises_found = false;
                        }
                    }
                    // Only add reach_fact if we have all premises (required for valid cex verification)
                    if !all_premises_found && !clause.body.predicates.is_empty() {
                        // Skip this reach_fact - incomplete premise chain would cause spurious cex
                        continue;
                    }
                    let mut instances = model;
                    cube::extract_equalities_from_formula(&concrete_state, &mut instances);
                    let id = Self::insert_reach_fact_bounded(
                        &mut self.reachability,
                        self.config.verbose,
                        ReachFact {
                            id: ReachFactId(0),
                            predicate: pob.predicate,
                            level: pob.level,
                            state: concrete_state.clone(),
                            incoming_clause: Some(*clause_index),
                            premises,
                            instances,
                        },
                    )?;
                    // Add to reach solver as BACKED entry (all premises found)
                    // for fast short-circuit in future queries
                    self.reachability
                        .reach_solvers
                        .add_backed(pob.predicate, id, concrete_state);
                    return Some(id);
                }
            }
        }

        None
    }

    /// Try to progress a derivation when a premise reaches concrete reachability.
    ///
    /// When a POB with an attached derivation becomes concretely reachable (via reach fact),
    /// this function:
    /// 1. Records the reach fact as satisfying the active premise
    /// 2. Advances to the next premise (if any)
    /// 3. If derivation is complete, creates the head reach fact with all premises
    ///
    /// Returns the head reach fact ID if derivation is complete, None otherwise.
    ///
    /// #1275 Phase 3: Hook reach fact creation to progress derivations.
    /// Reference: Z3 Spacer `spacer_context.cpp:3363` (derivation progression on concrete reachability).
    pub(in crate::pdr::solver) fn try_progress_derivation(
        &mut self,
        derivation_id: crate::pdr::derivation::DerivationId,
        premise_rf_id: ReachFactId,
    ) -> Option<ReachFactId> {
        if !self.config.use_derivations {
            return None;
        }

        // Get mutable access to the derivation
        let derivation = self.reachability.derivations.get_mut(derivation_id)?;

        // Record this reach fact as satisfying the active premise
        derivation.satisfy_active(premise_rf_id);

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Derivation {:?} progressed: {}/{} premises satisfied",
                derivation_id,
                derivation.premise_rfs.len(),
                derivation.premises.len()
            );
        }

        // Check if all premises are now satisfied
        if !derivation.is_complete() {
            return None;
        }

        // Derivation is complete - create the head reach fact
        // This reach fact has multiple premises (AND-node) for the hyperedge
        let head_predicate = derivation.head_predicate;
        let head_level = derivation.head_level;
        let head_state = derivation.head_state.clone();
        let clause_index = derivation.clause_index;
        let premise_rfs = derivation.premise_rfs.clone();

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Derivation {:?} complete - creating head reach fact for pred {} at level {}",
                derivation_id,
                head_predicate.index(),
                head_level
            );
        }

        // Build instances from head state
        let mut instances = FxHashMap::default();
        cube::extract_equalities_from_formula(&head_state, &mut instances);

        // Create the head reach fact with all premise facts as children (AND-node)
        let head_rf_id = Self::insert_reach_fact_bounded(
            &mut self.reachability,
            self.config.verbose,
            ReachFact {
                id: ReachFactId(0),
                predicate: head_predicate,
                level: head_level,
                state: head_state.clone(),
                incoming_clause: Some(clause_index),
                premises: premise_rfs,
                instances,
            },
        )?;

        // Add to reach solver as BACKED entry for fast short-circuit
        self.reachability
            .reach_solvers
            .add_backed(head_predicate, head_rf_id, head_state);

        // Free the derivation slot for reuse
        self.reachability.derivations.free(derivation_id);

        Some(head_rf_id)
    }

    /// Add a backed must summary with proven reachability.
    ///
    /// Called when we have a ReachFact proving the state is reachable.
    pub(in crate::pdr::solver) fn add_must_summary_backed(
        &mut self,
        pred: PredicateId,
        level: usize,
        formula: ChcExpr,
        reach_fact_id: ReachFactId,
    ) {
        if !self.config.use_must_summaries {
            return;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Adding backed must summary for pred {} at level {}: {}",
                pred.index(),
                level,
                formula
            );
        }
        let _ = self
            .reachability
            .must_summaries
            .add_backed(level, pred, formula, reach_fact_id);
    }
}
