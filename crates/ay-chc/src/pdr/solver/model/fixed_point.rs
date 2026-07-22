// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fixed-point detection and frame equivalence checking for PDR.

use super::super::{ChcExpr, ChcSort, Frame, InvariantModel, PdrSolver, SmtResult};

impl PdrSolver {
    /// Check if we've reached a fixed point (F_i = F_{i+1} for some i)
    ///
    /// After strengthening, try to push lemmas to higher frames and detect
    /// if any consecutive frames become equivalent. If F_i = F_{i+1}, then
    /// F_i is an inductive invariant.
    ///
    /// When a fixed point candidate fails verification, we extract the counterexample
    /// and add proof obligations to block the failing states, forcing PDR to discover
    /// a stronger invariant.
    pub(in crate::pdr::solver) fn check_fixed_point(&mut self) -> Option<InvariantModel> {
        if self.config.verbose {
            safe_eprintln!("PDR: check_fixed_point: {} frames", self.frames.len());
        }
        // Subsume redundant bound lemmas before propagation.
        // Matches Z3 Spacer's simplify_formulas_pre: clean frames before push_lemmas
        // to reduce SMT query size during propagation checks.
        let total_subsumed: usize = self
            .frames
            .iter_mut()
            .map(Frame::subsume_redundant_bounds)
            .sum();
        if total_subsumed > 0 {
            self.caches.push_cache.clear();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Subsumed {} redundant bound lemmas pre-propagation",
                    total_subsumed
                );
            }
        }

        // Semantic subsumption (Z3 Spacer's unit_subsumption_tactic port).
        // Enabled for single-predicate only; multi-predicate adds too much SMT
        // overhead (count_by_2 regresses from 40→39/55 with full subsumption).
        if self.problem.predicates().len() <= 1 {
            let mut total_semantic: usize = 0;
            for i in 0..self.frames.len() {
                let removed = self.frames[i].subsume_semantic(&mut self.smt, 64);
                total_semantic += removed;
            }
            if total_semantic > 0 {
                self.caches.push_cache.clear();
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Subsumed {} lemmas via semantic implication pre-propagation",
                        total_semantic
                    );
                }
            }
        }

        // Cancellation check before expensive lemma propagation
        if self.is_cancelled() {
            return None;
        }

        // Try to push lemmas from each frame to the next
        self.push_lemmas();
        self.tracing.active_pob = None;
        self.pdr_trace_step("Running", Some("PropagateLemmas"), None);
        tracing::info!(
            action = "PropagateLemmas",
            frames = self.frames.len(),
            "PDR propagated lemmas"
        );

        if self.config.verbose {
            safe_eprintln!("PDR: check_fixed_point: push_lemmas done");
            for (i, frame) in self.frames.iter().enumerate() {
                safe_eprintln!("  Frame {}: {} lemmas", i, frame.lemmas.len());
            }
        }

        // Postcondition after push_lemmas: frame monotonicity.
        // Each frame F_k should have lemma count >= frame F_{k+1} for k >= 1
        // because push_lemmas only adds lemmas to higher frames, never removes from lower.
        // (This is a weak invariant — subsumption in higher frames can violate strict
        // monotonicity, so we only assert the direction is correct after push_lemmas.)
        // Note: empty frames are valid for multi-predicate array problems where SMT queries
        // may return Unknown, preventing lemma generation. The solver will eventually return
        // Unknown if no progress is made. (#6047)
        if self.config.verbose {
            for k in 1..self.frames.len().saturating_sub(1) {
                if self.frames[k].lemmas.is_empty() && k != self.frames.len() - 1 {
                    safe_eprintln!(
                        "PDR: Warning: Frame {} is empty after push_lemmas (frames.len()={})",
                        k,
                        self.frames.len()
                    );
                }
            }
        }

        // Check for fixed point: F_i = F_{i+1} for some i >= 1
        for i in 1..self.frames.len().saturating_sub(1) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_fixed_point: checking frames {} and {}",
                    i,
                    i + 1
                );
            }
            if self.frames_equivalent(i, i + 1) {
                if self.config.verbose {
                    safe_eprintln!("PDR: Fixed point detected at level {}", i);
                }

                // SOUNDNESS (#5877): Check frame consistency before building model.
                //
                // An inconsistent frame (conjunction of lemmas for some predicate
                // is UNSAT) makes all can_push_lemma checks vacuously true and
                // frame convergence vacuously true. Models from inconsistent frames
                // are garbage and will fail transition validation.
                //
                // Previously this was only a diagnostic comment. Now we actually
                // check: if any predicate's frame constraint is UNSAT, skip this
                // convergence point. This prevents the PDR from entering an
                // infinite loop of converge → verify_model fail → converge.
                // Collect predicate IDs with init facts to avoid borrow conflict.
                let preds_with_facts: Vec<_> = self
                    .problem
                    .predicates()
                    .iter()
                    .filter(|pred| self.predicate_has_facts(pred.id))
                    .map(|pred| pred.id)
                    .collect();
                let frame_inconsistent = preds_with_facts.iter().any(|&pred_id| {
                    // #1398: Only check consistency for predicates with direct
                    // init facts. Intermediate predicates (no init facts) can
                    // have inconsistent frames due to blocking lemmas from
                    // different incoming transitions — this is expected and not
                    // a convergence-blocking issue.
                    if let Some(constraint) = self.frames[i].get_predicate_constraint(pred_id) {
                        self.smt.reset();
                        matches!(
                            self.smt.check_sat_with_timeout(
                                &constraint,
                                std::time::Duration::from_millis(500),
                            ),
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        )
                    } else {
                        false
                    }
                });
                if frame_inconsistent {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_fixed_point: rejecting frame convergence at level {} — \
                             frame has inconsistent predicate constraint (#5877)",
                            i
                        );
                    }
                    continue;
                }

                // We do NOT set skip_transition_validation here. Empirical evidence
                // (#5723, accumulator_unsafe) shows that even consistent frames can
                // produce non-inductive models that pass query-only validation but
                // fail transition checks. Full validation is always required.
                //
                // Multi-predicate entry-inductive model building:
                // For multi-predicate problems, blocking lemmas for derived predicates
                // (those without direct init clauses) can be self-inductive but violate
                // entry constraints from upstream predicates. For example, if pred P
                // feeds into pred Q via clause (P(x) -> Q(x)), and Q has blocking
                // lemma "x >= 0" that's preserved by Q's self-transition but Q's
                // entry states from P include negative values, the model will fail
                // verify_model at the connecting clause.
                //
                // Use build_model_from_entry_inductive_lemmas for multi-predicate
                // problems, which filters out entry-invalid lemmas. Fall back to
                // build_model_from_frame if the entry-inductive model is trivial
                // (all predicates map to true).
                let model = if self.problem.predicates().len() > 1 {
                    let entry_model = self.build_model_from_entry_inductive_lemmas(i);
                    let is_trivial = self.problem.predicates().iter().all(|pred| {
                        entry_model
                            .get(&pred.id)
                            .is_none_or(|interp| matches!(interp.formula, ChcExpr::Bool(true)))
                    });
                    if is_trivial {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_fixed_point: entry-inductive model is trivial, \
                                 falling back to full frame model at level {}",
                                i
                            );
                        }
                        // Full frame — convergence_proven set by builder
                        // when no non-canonical conjuncts were filtered.
                        self.build_model_from_frame_for_convergence(i)
                    } else {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_fixed_point: using entry-inductive model for \
                                 multi-predicate problem at level {}",
                                i
                            );
                        }
                        // SOUNDNESS: Entry-inductive model is a FILTERED
                        // subset of the converged frame. Frame convergence
                        // proves the FULL frame; filtering weakens the
                        // model. convergence_proven stays false. (#5970)
                        entry_model
                    }
                } else {
                    // Single-predicate: use full frame with convergence
                    // tracking. convergence_proven will be set when no
                    // non-canonical conjuncts were filtered. (#5970, #7410)
                    self.build_model_from_frame_for_convergence(i)
                };

                // #5930: Reject fixpoint candidates where predicates have Real-sorted
                // args but the model's invariant formula only mentions Bool/Int variables.
                // PDR cannot discover Real-involving lemmas, so such models are potentially
                // unsound — the Boolean invariant may be vacuously inductive while missing
                // Real-feasible error paths. The SMT verification of transitions may pass
                // because the SAT solver handles the Boolean structure but the LRA solver
                // may mark individual atoms as unsupported on complex Real constraints (#6167).
                let has_real_coverage_gap = self.problem.predicates().iter().any(|pred| {
                    let has_real_args = pred.arg_sorts.iter().any(|s| matches!(s, ChcSort::Real));
                    if !has_real_args {
                        return false;
                    }
                    model.get(&pred.id).is_some_and(|interp| {
                        !interp
                            .formula
                            .vars()
                            .iter()
                            .any(|v| v.sort == ChcSort::Real)
                    })
                });
                if has_real_coverage_gap {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_fixed_point: rejecting frame convergence at level {} — \
                             predicate has Real-sorted args but model is Bool/Int-only (#5930)",
                            i
                        );
                    }
                    // Don't return this model — continue PDR to search for
                    // stronger invariants. In practice PDR can't discover Real
                    // lemmas so this falls through to Unknown.
                    continue;
                }

                // Frame convergence model goes through full verify_model and
                // portfolio validation (#5723, #5745).
                tracing::info!(
                    action = "FrameConvergence",
                    level = i,
                    "PDR: Frame convergence detected at level {} — full validation required",
                    i
                );
                return Some(model);
            }
        }

        None
    }

    /// Check if two frames are equivalent (have same constraints for all predicates)
    ///
    /// Uses SMT-based logical equivalence checking: F_i(P) <=> F_j(P) for all predicates.
    /// Two frames are equivalent if their cumulative constraints are logically equivalent,
    /// which means F_i => F_j and F_j => F_i.
    pub(in crate::pdr::solver) fn frames_equivalent(&mut self, i: usize, j: usize) -> bool {
        // Quick syntactic check first
        if self.frames[i].lemmas.len() != self.frames[j].lemmas.len() {
            if self.config.verbose {
                safe_eprintln!("PDR: frames_equivalent: frames {} and {} have different lemma counts ({} vs {})",
                    i, j, self.frames[i].lemmas.len(), self.frames[j].lemmas.len());
            }
            return false;
        }

        // Two empty frames cannot form a valid fixpoint — an empty frame set
        // means PDR hasn't discovered any lemmas, not that safety is proven.
        // This can happen when SMT queries return Unknown for array-heavy
        // problems. (#6047)
        if self.frames[i].lemmas.is_empty() && self.frames[j].lemmas.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: frames_equivalent: both frames {} and {} are empty, not a valid fixpoint",
                    i,
                    j
                );
            }
            return false;
        }

        // Check logical equivalence for each predicate
        let pred_ids: Vec<_> = self.problem.predicates().iter().map(|p| p.id).collect();
        for pred_id in pred_ids {
            if self.config.verbose {
                safe_eprintln!("PDR: frames_equivalent: checking pred {}", pred_id.index());
            }
            let constraint_i = self.cumulative_frame_constraint(i, pred_id);
            let constraint_j = self.cumulative_frame_constraint(j, pred_id);

            match (constraint_i, constraint_j) {
                (None, None) => {
                    // Both are true, equivalent
                    continue;
                }
                (Some(_), None) | (None, Some(_)) => {
                    // One has constraints, the other doesn't - not equivalent
                    return false;
                }
                (Some(ci), Some(cj)) => {
                    // Fast path: structural equality check
                    if ci == cj {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: frames_equivalent: pred {} syntactically equal",
                                pred_id.index()
                            );
                        }
                        continue;
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: frames_equivalent: pred {} checking logical equivalence",
                            pred_id.index()
                        );
                    }

                    // Check logical equivalence via SMT: ci <=> cj
                    // This means: (ci => cj) AND (cj => ci)
                    //
                    // #4751 L4: decompose each implication PER CONJUNCT and
                    // bound each query. The previous monolithic
                    // `check_implies(ci, cj)` negates the whole 20+-lemma
                    // conjunction cj into a 20+-way disjunction; on redundant
                    // bound-flooded frames (s_multipl_12) that single
                    // UNBOUNDED LIA query ran for minutes and starved the
                    // whole solve. `ci => (c1 /\ ... /\ cn)` holds iff
                    // `ci => ck` for every k, so the decomposition is exact
                    // (not an approximation); each small query is easy. A
                    // timeout/Unknown fails CLOSED (frames treated as not
                    // equivalent — PDR just keeps searching; any convergence
                    // model still passes full validation downstream).

                    // First check ci => cj: (ci AND NOT ck) UNSAT for each ck.
                    if !self.frame_constraint_implies(&ci, &cj) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: frames_equivalent: pred {} ci => cj FAILED",
                                pred_id.index()
                            );
                        }
                        return false;
                    }

                    // Then check cj => ci: (cj AND NOT ck) UNSAT for each ck.
                    if !self.frame_constraint_implies(&cj, &ci) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: frames_equivalent: pred {} cj => ci FAILED",
                                pred_id.index()
                            );
                        }
                        return false;
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: frames_equivalent: pred {} logically equivalent",
                            pred_id.index()
                        );
                    }
                }
            }
        }

        true
    }

    /// Bounded per-conjunct implication check for frame equivalence
    /// (#4751 L4). Returns true iff `lhs => rhs` was PROVEN: for every
    /// conjunct `ck` of `rhs`, the query `lhs /\ NOT ck` is UNSAT within the
    /// per-conjunct timeout. Timeout/Unknown/SAT all return false (fail
    /// closed: the frames are treated as not equivalent and PDR continues).
    ///
    /// The decomposition is exact — `lhs => (c1 /\ ... /\ cn)` iff
    /// `lhs => ck` for all k — while avoiding the negated-conjunction
    /// disjunctive blowup of a monolithic `check_implies` call.
    fn frame_constraint_implies(&mut self, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
        const PER_CONJUNCT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(1);
        for conjunct in rhs.collect_conjuncts() {
            // Cap at the remaining solve deadline (mirrors verification's
            // cap_timeout, which is not visible from this module).
            let timeout = match self.solve_deadline {
                Some(deadline) => PER_CONJUNCT_TIMEOUT
                    .min(deadline.saturating_duration_since(ay_core::time::Instant::now())),
                None => PER_CONJUNCT_TIMEOUT,
            };
            if timeout.is_zero() || self.is_cancelled() {
                return false;
            }
            let query = ChcExpr::and(lhs.clone(), ChcExpr::not(conjunct));
            self.smt.reset();
            match self.smt.check_sat_with_timeout(&query, timeout) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => return false,
            }
        }
        true
    }
}
