// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition clause (inductiveness) verification.
//!
//! Extracted from `model.rs` — handles the `ClauseHead::Predicate` match arm in
//! `verify_model_impl`. This is the largest verification phase, containing the
//! full fallback chain: SMT check, blocking-lemma filtering, case-splitting,
//! algebraic verification, mod elimination, and executor fallback.

use super::*;

impl PdrSolver {
    /// `body ∧ ¬head` with every variable a top-level equality defines
    /// substituted away ([`ChcExpr::eliminate_top_level_definitions`]).
    ///
    /// All of them, not a fixed few: a clause-local array pinned by
    /// `a = store(...)` that survives keeps the query in the array theory,
    /// where each check goes to the executor and, in the default
    /// proof-carrying posture, costs about a second and can come back
    /// `unknown` (the BV/LIA tautology check refuses a query with an array
    /// term), so a valid back-translated model of a straight-line program
    /// failed validation. Stopping after eight substitutions left such
    /// definitions in place whenever more than eight preceded them. The
    /// substituted definitions are returned too, so a SAT model of the
    /// simplified query names the eliminated variables again
    /// ([`ChcExpr::extend_model_by_definitions`]).
    fn simplify_transition_query(query: ChcExpr) -> (ChcExpr, Vec<(ChcVar, ChcExpr)>) {
        query.eliminate_top_level_definitions_with_trail()
    }

    /// Verify a single transition clause (`ClauseHead::Predicate`).
    ///
    /// Returns `Some(failure_tuple)` on verification failure. Returns `None`
    /// if the clause passes (caller continues the loop). Sets
    /// `*used_filtered_invariant = true` when filtered invariant strategies fire.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn verify_transition_clause(
        &mut self,
        clause: &crate::HornClause,
        clause_idx: usize,
        body: &ChcExpr,
        head_pred: &PredicateId,
        head_args: &[ChcExpr],
        model: &InvariantModel,
        verify_timeout: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
        used_filtered_invariant: &mut bool,
        concrete: &mut concrete::ConcreteBudget,
        concrete_unsat_count: &mut u64,
        exact_owner: &mut crate::ground_derivation::compact::Owner<'static>,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        let head = match self.clause_head_under_model(&clause.head, model) {
            Some(h) => h,
            None => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} head computation failed",
                        clause_idx
                    );
                }
                return Some((
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                ));
            }
        };
        let head = self.bound_int_vars(head);
        if self.config.verbose {
            let kind = match &head {
                ChcExpr::Bool(false) => "false",
                ChcExpr::Bool(true) => "true",
                ChcExpr::Op(ChcOp::And, _) => "conjunction",
                _ => "other",
            };
            safe_eprintln!("PDR: verify_model: clause {clause_idx} head shape={kind}");
        }

        // Preserve the original conjunction before variable substitution or
        // blocking-lemma filtering can erase its direct proof. Ordinary
        // single-literal/trivial queries retain the existing fast SMT path.
        if matches!(&head, ChcExpr::Op(ChcOp::And, _)) {
            let local_deadline = match (budget_start, budget) {
                (Some(start), Some(limit)) => match start.checked_add(limit) {
                    Some(deadline) => Some(deadline),
                    None => return Some(Self::unconfirmed_model()),
                },
                _ => None,
            };
            let mut allowed =
                || local_deadline.is_none_or(|deadline| ay_core::time::Instant::now() < deadline);
            let mut continuation = exact_owner.with_progress(&mut allowed);
            match exact_conjunct::entails(body, &head, &mut continuation) {
                Ok(true) => return None,
                Ok(false) => {}
                Err(error) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {clause_idx} structural proof refused: {error:?}"
                        );
                    }
                    return Some(Self::unconfirmed_model());
                }
            }
        }

        // Validate: body => head  (i.e., body /\ !head is UNSAT)
        // Keep the pre-simplification query: `simplify_transition_query`
        // substitutes top-level variable equalities away, so a SAT model over
        // the simplified query omits the substituted variables. State
        // extraction (and #4751 L4 candidate repair) re-derives them by
        // propagating the ORIGINAL query's equalities through the model.
        let raw_query = self.bound_int_vars(ChcExpr::and(body.clone(), ChcExpr::not(head.clone())));
        let (query, eliminated) = Self::simplify_transition_query(raw_query.clone());

        // Fast-path: a syntactic contradiction implies UNSAT (safe to skip SMT).
        if cube::is_trivial_contradiction(&query) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} trivially valid (contradiction)",
                    clause_idx
                );
            }
            return None;
        }

        // BUG FIX #690: DISABLE mod/div early bypass for transition clauses
        // The parity invariants may not actually be inductive, so we must verify.

        self.smt.reset();
        // Cap SMT timeouts to remaining budget to prevent a single clause
        // from consuming the entire verify budget (#3121). Under portfolio
        // CPU contention, unbounded timeouts inflate 2-5x in wall time.
        let remaining_budget =
            budget_start.and_then(|start| budget.map(|b| b.saturating_sub(start.elapsed())));
        let capped_timeout = remaining_budget.map_or(verify_timeout, |r| verify_timeout.min(r));
        if capped_timeout.is_zero() {
            // SOUNDNESS FIX #5508: Non-zero budget exhausted during body
            // computation. The early budget check correctly rejects when budget
            // is expired at clause start, but body computation can push us past
            // the budget. Previously this silently skipped the transition clause
            // with `continue`, allowing non-inductive models through as false
            // Safe results.
            //
            // BV soft degradation (#5595): For BV problems, budget exhaustion
            // on transition clauses is expected — BV SMT queries are much more
            // expensive than LIA. Skip the unverifiable clause instead of
            // rejecting.
            //
            // Mod/div soft degradation (#5653): For mod/div clauses, SMT is
            // incomplete and routinely returns Unknown within budget.
            // However, accepting an unverified transition clause is unsound,
            // so budget exhaustion must reject the model.
            //
            // SOUNDNESS NOTE (#5643): This skip weakens defense-in-depth for
            // BV and mod/div problems. PDR engines produce inductive invariants
            // by construction, so this gap is theoretical. The
            // bv_soft_degradation_skips counter tracks occurrences.
            let has_bv = self
                .problem
                .predicates()
                .iter()
                .any(|p| p.arg_sorts.iter().any(|s| matches!(s, ChcSort::BitVec(_))));
            if has_bv {
                // SOUNDNESS (#C1, sound-by-default): the verification budget was
                // exhausted before we could SMT-check this BV transition clause, so
                // we cannot certify the candidate invariant is inductive over it.
                // Reject the model UNCONDITIONALLY (prefer `unknown` over an
                // unverified Safe), matching the mod/div and generic branches below.
                // Previously this fell open to `None` (trusting the unverified
                // clause) unless `strict_proofs` — a latent false-SAFE source the
                // public discharge gate cannot catch, because that gate only checks
                // query/safety clauses and skips every transition clause.
                self.telemetry.bv_soft_degradation_skips += 1;
                tracing::warn!(
                    clause_idx,
                    total_skips = self.telemetry.bv_soft_degradation_skips,
                    "BV transition clause verification budget exhausted before SMT \
                     check — rejecting model (sound: prefer unknown)"
                );
                return Some((*head_pred, body.clone(), *head_pred, head));
            }
            if Self::contains_mod_or_div(&query) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: rejecting model — mod/div transition clause {} exhausted verification budget before SMT check",
                        clause_idx,
                    );
                }
                return Some((*head_pred, body.clone(), *head_pred, head));
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: rejecting model — budget exhausted before transition clause {} SMT check",
                    clause_idx
                );
            }
            return Some((*head_pred, body.clone(), *head_pred, head));
        }
        let split_surface = Self::has_verification_case_split_surface(&query);
        let head_conjunct_count = head.collect_conjuncts().len();
        if split_surface && (2..=16).contains(&head_conjunct_count) {
            if let Some(result) = self.try_head_conjunct_splitting(
                clause_idx,
                body,
                &query,
                &head,
                head_pred,
                verify_timeout,
                budget_start,
                budget,
                used_filtered_invariant,
            ) {
                return result;
            }
        }

        let mut tried_case_split = false;
        let mut result = SmtResult::Unknown;
        if split_surface && !Self::contains_mod_or_div(&query) && !query.contains_array_ops() {
            tried_case_split = true;
            let split_timeout =
                self.current_verify_step_timeout(VERIFY_CASE_SPLIT_TIMEOUT, budget_start, budget);
            result = Self::try_verification_case_split(
                &mut self.smt,
                self.config.verbose,
                &query,
                split_timeout,
            );
            if self.config.verbose && !matches!(result, SmtResult::Unknown) {
                safe_eprintln!(
                    "PDR: verify_model: clause {} resolved via early bounded case-split ({:?})",
                    clause_idx,
                    if matches!(
                        result,
                        SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_)
                    ) {
                        "UNSAT"
                    } else {
                        "SAT"
                    }
                );
            }
        }
        if matches!(result, SmtResult::Unknown) {
            self.smt.reset();
            result = self.smt.check_sat_with_timeout(&query, capped_timeout);
        }
        if matches!(result, SmtResult::Unknown) && !query.contains_array_ops() && !tried_case_split
        {
            let remaining_budget = self.remaining_verification_budget(budget_start, budget);
            if !Self::contains_mod_or_div(&query) {
                // Pure QF_LIA: retry with remaining budget (decidable).
                let retry_timeout = self.current_verify_retry_timeout(budget_start, budget);
                if !retry_timeout.is_zero() {
                    self.smt.reset();
                    result = self.smt.check_sat_with_timeout(&query, retry_timeout);
                }
            } else {
                // Mod/div present: pre-eliminate to pure QF_LIA, then retry
                // with timeout capped to remaining budget (#3121).
                let mod_retry_timeout = std::time::Duration::from_secs(5);
                let capped_mod =
                    remaining_budget.map_or(mod_retry_timeout, |r| mod_retry_timeout.min(r));
                if !capped_mod.is_zero() {
                    let mod_free = query.eliminate_mod();
                    self.smt.reset();
                    result = self.smt.check_sat_with_timeout(&mod_free, capped_mod);
                    if self.config.verbose && !matches!(result, SmtResult::Unknown) {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} resolved via mod-elimination retry ({:?})",
                            clause_idx,
                            if matches!(result, SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)) { "UNSAT" } else { "SAT" }
                        );
                    }
                }
            }
        }
        // #1362: Equality propagation + ITE case-split fallback for Unknown.
        // The per-lemma is_self_inductive_blocking check succeeds on ITE-heavy
        // transitions because it uses propagate_equalities() + check_sat_with_ite_case_split.
        // Apply the same technique to whole-model transition verification so that
        // verify_model_fresh can confirm models that pass per-lemma checks.
        if matches!(result, SmtResult::Unknown) && !query.contains_array_ops() {
            let simplified = query.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                result = SmtResult::Unsat;
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} resolved via equality propagation (UNSAT)",
                        clause_idx
                    );
                }
            } else if !tried_case_split
                && !matches!(&head, ChcExpr::Op(ChcOp::And, args) if args.len() > 1)
            {
                let split_timeout = self.current_verify_step_timeout(
                    VERIFY_CASE_SPLIT_TIMEOUT,
                    budget_start,
                    budget,
                );
                let ite_result = Self::try_verification_case_split(
                    &mut self.smt,
                    self.config.verbose,
                    &simplified,
                    split_timeout,
                );
                if !matches!(ite_result, SmtResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} resolved via ITE case-split ({:?})",
                            clause_idx,
                            if matches!(
                                ite_result,
                                SmtResult::Unsat
                                    | SmtResult::UnsatWithCore(_)
                                    | SmtResult::UnsatWithFarkas(_)
                            ) {
                                "UNSAT"
                            } else {
                                "SAT"
                            }
                        );
                    }
                    result = ite_result;
                }
            }
        }
        if let SmtResult::Sat(candidate) = result {
            result = self.confirm_original_validation_sat(
                &raw_query,
                &eliminated,
                candidate,
                verify_timeout,
                budget_start,
                budget,
            );
            if matches!(result, SmtResult::Unknown) {
                return Some(Self::unconfirmed_model());
            }
        }
        match result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // #6787: Cross-check via Executor — budgeted (#5970 regression).
                // Skip for small queries (<100 AST nodes).
                {
                    let query_size = query.node_count(200);
                    if query_size >= 100 && self.cross_check_budget > std::time::Duration::ZERO {
                        let cross_timeout = self
                            .cross_check_budget
                            .min(std::time::Duration::from_millis(500));
                        let propagated = FxHashMap::default();
                        let cross_start = ay_core::time::Instant::now();
                        // A rejection-only guard: a rule's spent executor
                        // allowance must not turn it into a vacuous Unknown.
                        let _unmetered = crate::smt::executor_work::ScopedExecutorWork::lift();
                        let cross_result =
                            self.smt
                                .check_sat_via_executor(&query, &propagated, cross_timeout);
                        self.cross_check_budget = self
                            .cross_check_budget
                            .saturating_sub(cross_start.elapsed());
                        if let SmtResult::Sat(candidate) = cross_result {
                            let original = self.confirm_original_validation_sat(
                                &raw_query,
                                &eliminated,
                                candidate,
                                verify_timeout,
                                budget_start,
                                budget,
                            );
                            if matches!(original, SmtResult::Unknown) {
                                return Some(Self::unconfirmed_model());
                            }
                            if matches!(original, SmtResult::Sat(_)) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model: clause {} CROSS-CHECK FAILED — \
                                         original query confirmed SAT (#6787)",
                                        clause_idx
                                    );
                                }
                                tracing::warn!(
                                    clause_idx,
                                    "verify_model: original query confirms cross-check SAT (#6787)"
                                );
                                return Some((*head_pred, body.clone(), *head_pred, head));
                            }
                        }
                    }
                }
                // SOUNDNESS FIX #5381: Concrete evaluation sanity check.
                // #5653: Budget-limited to avoid cumulative overhead.
                // #7410: Rate-limit: first 10, then 1-in-100.
                *concrete_unsat_count += 1;
                if concrete.has_room()
                    && (*concrete_unsat_count <= 10 || (*concrete_unsat_count).is_multiple_of(100))
                {
                    match concrete.check(body, &query) {
                        concrete::ConcreteAnswer::Witness(cex_model) => {
                            tracing::warn!(
                                clause_idx,
                                ?cex_model,
                                "verify_model: SMT said UNSAT but concrete check found SAT"
                            );
                            return Some((*head_pred, body.clone(), *head_pred, head.clone()));
                        }
                        // The solve is over: no acceptance on an unfinished check.
                        concrete::ConcreteAnswer::Interrupted => {
                            return Some(Self::unconfirmed_model())
                        }
                        concrete::ConcreteAnswer::NoWitness => {}
                    }
                }
            }
            SmtResult::Sat(m) => {
                let mut m = m;
                ChcExpr::extend_model_by_definitions(&eliminated, &mut m);
                if m.is_empty() {
                    Self::extract_equalities_from_formula(&raw_query, &mut m);
                }
                // Augment from the PRE-simplification query (#4751 L4):
                // simplify_transition_query substituted variable equalities
                // away, so only the raw query still carries the equalities
                // needed to reconstruct the substituted variables' values.
                cube::augment_model_from_equalities(&raw_query, &mut m);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} implication failed",
                        clause_idx
                    );
                    safe_eprintln!("  body={}", body);
                    safe_eprintln!("  head={}", head);
                    safe_eprintln!("  model={:?}", m);
                }

                // SAT refutes this exact submitted interpretation. Proving a
                // weaker head, even followed by query-only rechecks, cannot
                // validate the original model. Preserve the concrete teacher
                // below: candidate repair may weaken a separate model, then
                // must recheck that changed model against every clause.
                // Extract pre-state (body predicate) and post-state (head predicate)
                if let Some((body_pred, body_args)) = clause.body.predicates.first() {
                    let pre_state = self.extract_state_from_args(*body_pred, body_args, &m);
                    let post_state = self.extract_state_from_args(*head_pred, head_args, &m);
                    if let Some(pre) = pre_state {
                        return Some((
                            *body_pred,
                            pre,
                            *head_pred,
                            post_state.unwrap_or(ChcExpr::Bool(false)),
                        ));
                    }
                }
                return Some((
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                ));
            }
            SmtResult::Unknown => {
                // A disjunctive body interpretation (IMC's reached set) is
                // re-checked one disjunct at a time before the fallback chain.
                if Self::body_interpretation_is_disjunctive(clause, model)
                    && self.prove_by_disjunctive_body_split(clause_idx, &query)
                {
                    return None;
                }
                // Full fallback chain in model_inductive_unknown.rs.
                return self.handle_unknown_transition_clause(
                    clause,
                    clause_idx,
                    body,
                    &query,
                    &head,
                    head_pred,
                    verify_timeout,
                    budget_start,
                    budget,
                    used_filtered_invariant,
                );
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "model_inductive/definition_tests.rs"]
mod definition_tests;
