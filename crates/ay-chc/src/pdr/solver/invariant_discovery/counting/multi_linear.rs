// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Try adding the conjunction of init inequalities (non-strict only) as a single lemma.
    ///
    /// Some benchmarks have init constraints where each bound is not self-inductive in isolation,
    /// but the conjunction becomes inductive once combined (potentially along with other learned
    /// invariants like `A <= B`).
    ///
    /// We intentionally drop strict inequalities (`>`/`<`) here, since they are rarely inductive
    /// and tend to block otherwise-useful non-strict bounds from being learned.
    pub(in crate::pdr::solver) fn discover_conjunctive_init_inequality_invariants(&mut self) {
        const MAX_CONJUNCTS: usize = 8;

        let predicates: Vec<_> = self.problem.predicates().to_vec();
        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Avoid adding init-derived conjunctions for predicates that can be populated by
            // unrelated incoming transitions. Self-inductiveness alone isn't sufficient there.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let init_inequalities = self.extract_init_inequalities(pred.id);
            let mut conjuncts: Vec<ChcExpr> = Vec::new();
            for ineq in init_inequalities {
                if !matches!(ineq, ChcExpr::Op(ChcOp::Ge | ChcOp::Le, _)) {
                    continue;
                }
                if conjuncts.contains(&ineq) {
                    continue;
                }
                conjuncts.push(ineq);
            }

            if conjuncts.len() < 2 || conjuncts.len() > MAX_CONJUNCTS {
                continue;
            }

            let conj = ChcExpr::and_all(conjuncts);

            // Avoid exact duplicates.
            if self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == pred.id && l.formula == conj)
            {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Trying conjunctive init inequality invariant for pred {}",
                    pred.id.index()
                );
            }

            self.add_discovered_invariant(pred.id, conj, 1);
        }
    }

    /// Discover multi-linear invariants via CEX-guided iterative refinement.
    ///
    /// This handles benchmarks like `three_dots_moving_2` that require conjunctive
    /// multi-linear invariants (e.g., `2x0 - x1 - x2 + x3 >= 0`) where each clause
    /// needs the others for inductiveness.
    ///
    /// Algorithm:
    /// 1. Extract linear inequality candidates from init constraints
    /// 2. For each candidate, check if it's self-inductive
    /// 3. If not, get a counterexample pre-state model
    /// 4. Find an init constraint that blocks the CEX pre-state
    /// 5. Conjoin it with the candidate and iterate
    /// 6. Stop when inductive or max iterations reached
    ///
    /// Based on design doc: the development design notes
    /// Issue: #1525
    pub(in crate::pdr::solver) fn discover_multi_linear_invariants(&mut self) {
        const MAX_REFINEMENTS: usize = 10;

        let predicates: Vec<_> = self.problem.predicates().to_vec();
        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip predicates with unrestricted inter-predicate transitions
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            // Get all linear inequality candidates from init
            let init_inequalities = self.extract_init_inequalities(pred.id);
            if init_inequalities.len() < 2 {
                continue; // Need at least 2 candidates for refinement
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_multi_linear_invariants for pred {} with {} candidates",
                    pred.id.index(),
                    init_inequalities.len()
                );
            }

            // Try each candidate as a starting point
            for (idx, base_candidate) in init_inequalities.iter().enumerate() {
                if self.is_cancelled() {
                    return;
                }
                // Skip if this candidate is already known inductive
                // Note: is_self_inductive_blocking checks if NOT(arg) is inductive,
                // so to check if candidate is inductive, pass NOT(candidate)
                if self.is_self_inductive_blocking(&ChcExpr::not(base_candidate.clone()), pred.id) {
                    continue;
                }

                // Try iterative refinement
                if let Some(refined) = self.refine_candidate_iteratively(
                    pred.id,
                    base_candidate.clone(),
                    &init_inequalities,
                    idx,
                    MAX_REFINEMENTS,
                ) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Multi-linear refinement succeeded for pred {}: {}",
                            pred.id.index(),
                            refined
                        );
                    }
                    // Add the refined invariant
                    self.add_discovered_invariant(pred.id, refined, 1);
                    // Don't break - other base candidates might yield different useful invariants
                }
            }
        }
    }

    /// Iteratively refine a candidate invariant by conjoining init constraints that
    /// block counterexample pre-states.
    ///
    /// Returns Some(refined_invariant) if we find an inductive conjunction,
    /// None if we exhaust refinement options.
    pub(in crate::pdr::solver) fn refine_candidate_iteratively(
        &mut self,
        pred: PredicateId,
        base_candidate: ChcExpr,
        all_candidates: &[ChcExpr],
        base_idx: usize,
        max_refinements: usize,
    ) -> Option<ChcExpr> {
        let mut current = base_candidate;
        let mut used_indices: Vec<usize> = vec![base_idx];

        for iteration in 0..max_refinements {
            // Check inductiveness and get model if not inductive
            match self.check_inductiveness_with_model(&current, pred) {
                InductiveCheckResult::Inductive => {
                    // Found inductive invariant
                    return Some(current);
                }
                InductiveCheckResult::NotInductive(cex_model) => {
                    // Find an unused init constraint that blocks this CEX pre-state
                    let mut found_blocker = false;

                    for (cand_idx, candidate) in all_candidates.iter().enumerate() {
                        if used_indices.contains(&cand_idx) {
                            continue;
                        }

                        // Check if candidate is violated by the CEX pre-state
                        // If so, adding it will rule out this counterexample
                        if self.mbp.eval_bool(candidate, &cex_model) == Some(false) {
                            // This constraint rules out cex_pre - conjoin it
                            current = ChcExpr::and_all(vec![current, candidate.clone()]);
                            used_indices.push(cand_idx);
                            found_blocker = true;

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Multi-linear refinement iter {}: added {} (total {} conjuncts)",
                                    iteration,
                                    candidate,
                                    used_indices.len()
                                );
                            }
                            break;
                        }
                    }

                    if !found_blocker {
                        // No unused init constraint blocks cex_pre - can't refine further
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Multi-linear refinement stopped at iter {}: no blocker found",
                                iteration
                            );
                        }
                        return None;
                    }
                }
                InductiveCheckResult::Unknown => {
                    // SMT solver couldn't decide - give up on this candidate
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Multi-linear refinement stopped at iter {}: SMT returned Unknown",
                            iteration
                        );
                    }
                    return None;
                }
            }
        }

        // Max iterations reached - check final result
        // Note: is_self_inductive_blocking checks if NOT(arg) is inductive,
        // so pass NOT(current) to check if current is inductive
        if self.is_self_inductive_blocking(&ChcExpr::not(current.clone()), pred) {
            Some(current)
        } else {
            None
        }
    }

    /// Check if a candidate is self-inductive and return a counterexample model if not.
    ///
    /// Unlike `is_self_inductive_blocking` which takes a blocking formula and checks if
    /// `not(blocking)` is inductive, this function takes a candidate invariant and checks
    /// if the candidate itself is self-inductive: candidate(pre) /\ T => candidate(post).
    pub(in crate::pdr::solver) fn check_inductiveness_with_model(
        &mut self,
        candidate: &ChcExpr,
        predicate: PredicateId,
    ) -> InductiveCheckResult {
        let violated = ChcExpr::not(candidate.clone());

        // Collect self-loop clauses
        let clauses: Vec<_> = self.problem.clauses_defining(predicate).cloned().collect();

        for clause in &clauses {
            if clause.body.predicates.is_empty() {
                continue; // Fact clause
            }

            // #1852 Phase 0: Use UNSAT-sufficient check for hyperedge self-loops
            if clause.body.predicates.len() > 1 {
                let has_self_loop = clause
                    .body
                    .predicates
                    .iter()
                    .any(|(bp, _)| *bp == predicate);
                if has_self_loop {
                    // Try Phase 0 UNSAT-sufficient check
                    if let Some(hyperedge_query) =
                        self.build_hyperedge_inductive_query(clause, predicate, candidate)
                    {
                        match self.smt.check_sat(&hyperedge_query.query) {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                // UNSAT means inductive even with weak assumptions - continue
                                continue;
                            }
                            SmtResult::Sat(model) => {
                                if hyperedge_query.missing_product_state {
                                    // SAT but we dropped constraints - inconclusive
                                    return InductiveCheckResult::Unknown;
                                }
                                // SAT with no missing constraints - truly not inductive
                                return InductiveCheckResult::NotInductive(model);
                            }
                            SmtResult::Unknown => {
                                return InductiveCheckResult::Unknown;
                            }
                        }
                    }
                    return InductiveCheckResult::Unknown; // Couldn't build query
                }
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue; // Not a self-loop
            }

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // candidate_on_body = candidate applied to body (pre-state satisfies invariant)
            let Some(candidate_on_body) = self.apply_to_args(predicate, candidate, body_args)
            else {
                return InductiveCheckResult::Unknown;
            };

            // violated_on_head = not(candidate) applied to head (post-state violates invariant)
            let Some(violated_on_head) = self.apply_to_args(predicate, &violated, head_args) else {
                return InductiveCheckResult::Unknown;
            };

            // Query: candidate_on_body /\ clause_constraint /\ violated_on_head
            // SAT => not inductive (pre-state satisfies candidate but post-state violates it)
            let query = self.bound_int_vars(ChcExpr::and_all(vec![
                candidate_on_body.clone(),
                clause_constraint.clone(),
                violated_on_head.clone(),
            ]));

            match self.smt.check_sat(&query) {
                SmtResult::Sat(model) => {
                    // Not inductive without frame[1] - try strengthening with frame[1] lemmas.
                    // This enables multi-linear invariants to use already-discovered equalities
                    // as prerequisites. See #2245 for the root cause analysis.
                    if self.frames.len() > 1 {
                        let mut strengthened_parts =
                            vec![candidate_on_body, clause_constraint.clone()];
                        let mut frame1_lemma_count = 0;
                        for frame_lemma in &self.frames[1].lemmas {
                            if frame_lemma.predicate == predicate {
                                if let Some(applied) =
                                    self.apply_to_args(predicate, &frame_lemma.formula, body_args)
                                {
                                    strengthened_parts.push(applied);
                                    frame1_lemma_count += 1;
                                }
                            }
                        }
                        strengthened_parts.push(violated_on_head);

                        // Only retry if we actually added frame[1] lemmas
                        if frame1_lemma_count > 0 {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: check_inductiveness_with_model retrying with {} frame[1] lemmas for pred {}",
                                    frame1_lemma_count,
                                    predicate.index()
                                );
                            }

                            let strengthened_query =
                                self.bound_int_vars(ChcExpr::and_all(strengthened_parts));
                            match self.smt.check_sat(&strengthened_query) {
                                SmtResult::Sat(strengthened_model) => {
                                    // Still not inductive even with frame[1] lemmas
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: check_inductiveness_with_model still SAT after frame[1] strengthening for pred {}",
                                            predicate.index()
                                        );
                                    }
                                    return InductiveCheckResult::NotInductive(strengthened_model);
                                }
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {
                                    // Inductive with frame[1] prerequisites - continue checking
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: check_inductiveness_with_model UNSAT after frame[1] strengthening for pred {}",
                                            predicate.index()
                                        );
                                    }
                                }
                                SmtResult::Unknown => {
                                    // Fall back to original model if strengthened check is unknown
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: check_inductiveness_with_model UNKNOWN after frame[1] strengthening for pred {}",
                                            predicate.index()
                                        );
                                    }
                                    return InductiveCheckResult::NotInductive(model);
                                }
                            }
                        } else {
                            // No frame[1] lemmas for this predicate - return original result
                            return InductiveCheckResult::NotInductive(model);
                        }
                    } else {
                        // No frame[1] available - return original result
                        return InductiveCheckResult::NotInductive(model);
                    }
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This clause preserves the lemma - continue checking others
                }
                SmtResult::Unknown => {
                    return InductiveCheckResult::Unknown;
                }
            }
        }

        // All self-loop clauses preserve the lemma
        InductiveCheckResult::Inductive
    }
}
