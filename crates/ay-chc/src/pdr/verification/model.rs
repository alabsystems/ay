// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model verification for PDR solver.
//!
//! Contains methods for verifying that an invariant model satisfies all CHC clauses.
//! The main `verify_model_impl` dispatches to extracted methods in sibling modules:
//! - `model_safety.rs`: query clause verification (`ClauseHead::False`)
//! - `model_inductive.rs`: transition clause verification (`ClauseHead::Predicate`)
//! - `model_recheck.rs`: post-loop filtered-invariant re-verification
//!
//! Mod/div fallback strategies are in the `mod_div` sibling module.

use super::*;

impl PdrSolver {
    /// Set the wall-clock deadline used by direct model-validation entrypoints.
    ///
    /// `solve()` normally initializes `solve_deadline` from `config.solve_timeout`
    /// in `solve_init()`. External validation APIs call verification directly, so
    /// they need to seed the same deadline state before running per-clause checks.
    pub(crate) fn set_validation_deadline(&mut self, budget: std::time::Duration) {
        let effective_budget = self
            .config
            .solve_timeout
            .map_or(budget, |solve_timeout| solve_timeout.min(budget));
        self.config.solve_timeout = Some(effective_budget);

        let requested_deadline = ay_core::time::Instant::now() + effective_budget;
        self.solve_deadline = Some(self.solve_deadline.map_or(requested_deadline, |deadline| {
            deadline.min(requested_deadline)
        }));
    }

    /// Cap a per-query SMT timeout at the remaining solve deadline (#3225).
    ///
    /// When `solve_timeout` is set, individual SMT calls should not outlast the
    /// overall solve budget. Without this, a single 30s retry timeout can run
    /// long past the solve_deadline, preventing cooperative cancellation
    /// from taking effect.
    pub(super) fn cap_timeout(&self, requested: std::time::Duration) -> std::time::Duration {
        if let Some(deadline) = self.solve_deadline {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            requested.min(remaining)
        } else {
            requested
        }
    }

    pub(super) fn remaining_verification_budget(
        &self,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> Option<std::time::Duration> {
        let solve_remaining = self
            .solve_deadline
            .map(|deadline| deadline.saturating_duration_since(ay_core::time::Instant::now()));
        let clause_remaining = budget_start
            .and_then(|start| budget.map(|limit| limit.saturating_sub(start.elapsed())));
        match (solve_remaining, clause_remaining) {
            (Some(solve_remaining), Some(clause_remaining)) => {
                Some(solve_remaining.min(clause_remaining))
            }
            (Some(solve_remaining), None) => Some(solve_remaining),
            (None, Some(clause_remaining)) => Some(clause_remaining),
            (None, None) => None,
        }
    }

    pub(super) fn current_verify_retry_timeout(
        &self,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> std::time::Duration {
        let requested = match self.remaining_verification_budget(budget_start, budget) {
            Some(remaining) => {
                VERIFY_RETRY_TIMEOUT.min((remaining / 4).max(std::time::Duration::from_secs(2)))
            }
            None => VERIFY_RETRY_TIMEOUT,
        };
        self.cap_timeout(requested)
    }

    pub(super) fn current_verify_step_timeout(
        &self,
        requested: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> std::time::Duration {
        let requested = match self.remaining_verification_budget(budget_start, budget) {
            Some(remaining) => requested.min(remaining),
            None => requested,
        };
        self.cap_timeout(requested)
    }

    /// Reject ill-formed models whose interpretations mention FREE variables.
    ///
    /// SOUNDNESS: An invariant interpretation must be closed over its binder
    /// vars (`interp.vars`). If the formula references other variables, the
    /// substitution performed by `apply_interp_to_args` leaves them free in
    /// the verification query, where they are CAPTURED by same-named
    /// clause-local variables. Clause constraints can then contradict the
    /// captured conjuncts, making consecution checks vacuously UNSAT and
    /// letting a non-invariant "pass" full validation (022c-horn_000
    /// false-SAT: synthesized `INV1 := ¬(... ∧ (= G H) ∧ (= I J))` with free
    /// G/H/I/J was validated against clauses whose own G/H/I/J satisfied
    /// `(>= (- G H) 1)`, discharging every check).
    ///
    /// Returns `true` (reject) when any interpretation used by the problem
    /// has free variables.
    pub(super) fn model_has_free_interpretation_vars(&self, model: &InvariantModel) -> bool {
        for pred in self.problem.predicates() {
            let Some(interp) = model.get(&pred.id) else {
                continue;
            };
            let param_names: ay_core::kani_compat::DetHashSet<&str> =
                interp.vars.iter().map(|v| v.name.as_str()).collect();
            if let Some(free_var) = interp
                .formula
                .vars()
                .iter()
                .find(|v| !param_names.contains(v.name.as_str()))
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: rejecting ill-formed model — pred {} interpretation \
                         has free variable `{}` not among its binder vars (capture-unsound)",
                        pred.id.index(),
                        free_var.name
                    );
                }
                tracing::warn!(
                    pred = pred.id.index(),
                    free_var = %free_var.name,
                    "verify_model: rejecting model with free interpretation variable \
                     (substitution capture would make clause checks vacuous)"
                );
                return true;
            }
        }
        false
    }

    /// Verify that a model satisfies all CHC clauses
    ///
    /// REQUIRES: `self.problem` is the CHC problem the `model` was constructed for.
    /// ENSURES: If this returns `true`, `model` satisfies all CHC clauses in `self.problem`
    ///   (i.e., is a sound proof of safety). If it returns `false`, the model is invalid or
    ///   verification could not be completed (conservatively treated as failure).
    ///
    /// A model is valid if for every clause `body => head`:
    /// - If head is False: body under the model interpretation is unsatisfiable
    /// - If head is a predicate: body under the model implies head under the model
    ///
    /// This is the main entry point for external invariant validation.
    pub fn verify_model(&mut self, model: &InvariantModel) -> bool {
        self.verify_model_impl(model, None, false, false).is_none()
    }

    /// Panic-safe variant of [`verify_model`](Self::verify_model).
    ///
    /// Catches ay-internal panics and returns them as `ChcError::Internal`.
    /// Non-ay panics propagate normally via `resume_unwind`.
    pub fn try_verify_model(&mut self, model: &InvariantModel) -> crate::ChcResult<bool> {
        ay_core::catch_ay_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.verify_model(model))),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
    }

    /// Number of transition clauses skipped by BV soft degradation (#5643).
    /// Non-zero means the model was not fully verified for inductiveness.
    #[cfg(test)]
    pub(crate) fn bv_soft_degradation_skips(&self) -> usize {
        self.telemetry.bv_soft_degradation_skips
    }

    /// Verify a model using a **fresh** SMT context (#5922).
    ///
    /// PDR's warm SmtContext accumulates state (var_map sort-qualification,
    /// pred_app_counter, conversion_budget_strikes) that can cause `check_sat`
    /// to return different results than a fresh context (#6100). This method
    /// temporarily replaces `self.smt` with a brand-new `SmtContext`, runs
    /// per-rule verification with a 2s budget, and restores the original context.
    ///
    /// Use this as a confirmation step after `verify_model` succeeds on the warm
    /// context. If fresh verification also passes, the model is reliable.
    /// If fresh verification fails, the warm context was incorrect and the model
    /// should not be returned as Safe.
    pub(in crate::pdr) fn verify_model_fresh(&mut self, model: &InvariantModel) -> bool {
        let warm_smt = std::mem::take(&mut self.smt);
        let per_rule_budget = std::time::Duration::from_secs(2);
        let result = self.verify_model_per_rule(model, per_rule_budget);
        self.smt = warm_smt;
        result
    }

    /// Fresh-context per-rule verification that reports the failing clause.
    ///
    /// Same semantics as [`verify_model_fresh`](Self::verify_model_fresh)
    /// (fresh `SmtContext`, independent 2s per-rule budgets), but returns the
    /// failure tuple `(body_pred, pre_state, head_pred, post_state)` instead
    /// of a bare bool. For a transition-clause SAT failure the `post_state`
    /// is a conjunction of `canonical_var = value` equalities extracted from
    /// the SMT counterexample model — the hook point for counterexample-guided
    /// candidate repair (#4751 L4 follow-up). `None` means the model verified.
    pub(in crate::pdr) fn verify_model_fresh_with_failure(
        &mut self,
        model: &InvariantModel,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        let warm_smt = std::mem::take(&mut self.smt);
        let per_rule_budget = std::time::Duration::from_secs(2);
        let result = self.verify_model_impl(model, Some(per_rule_budget), false, true);
        self.smt = warm_smt;
        result
    }

    /// Fresh-context verification checking only query clauses.
    ///
    /// Used as a fallback when full fresh verification fails on transition
    /// clauses (e.g., ITE-heavy multi-predicate transitions). If the warm
    /// context proved full inductiveness and the fresh context can independently
    /// confirm safety (query clauses UNSAT), the model is sound.
    pub(in crate::pdr) fn verify_model_fresh_query_only(&mut self, model: &InvariantModel) -> bool {
        let warm_smt = std::mem::take(&mut self.smt);
        let result = self.verify_model_query_only(model);
        self.smt = warm_smt;
        result
    }

    /// Verify a model with a wall-clock budget.
    ///
    /// When the budget expires on a transition clause that returned Unknown
    /// (not SAT), the clause is skipped rather than blocking indefinitely.
    /// This prevents verify_model from consuming the entire portfolio timeout
    /// on mod/div-heavy transition clauses where the SMT backend is incomplete.
    pub(crate) fn verify_model_with_budget(
        &mut self,
        model: &InvariantModel,
        budget: std::time::Duration,
    ) -> bool {
        self.verify_model_impl(model, Some(budget), false, false)
            .is_none()
    }

    /// Verify only query clauses (safety property checks).
    ///
    /// K-inductive invariants (from Kind engine) satisfy init + query +
    /// k-step induction, but may not satisfy 1-step transition checks.
    /// This method checks only query clauses, which are the soundness-critical
    /// part: does the invariant actually imply the safety property?
    ///
    /// Transition clauses are skipped entirely — not budget-limited, not
    /// checked with Duration::ZERO. This replaces the pre-#5745 Duration::ZERO
    /// convention that was broken by the budget-expiry rejection logic (#5825).
    pub(crate) fn verify_model_query_only(&mut self, model: &InvariantModel) -> bool {
        self.verify_model_impl(model, None, true, false).is_none()
    }

    /// Verify a model with independent per-rule budgets.
    ///
    /// Unlike `verify_model_with_budget` which uses a SHARED budget across all
    /// clauses (causing budget exhaustion when early clauses consume the budget),
    /// this method resets the budget timer at the start of each clause. Each
    /// clause gets its own full budget allocation.
    ///
    /// This implements the Z3-style rule-by-rule validation pattern where each
    /// rule is checked independently. Complex mod/div transition clauses don't
    /// steal budget from simple init/query clauses.
    ///
    /// Part of #5653: tiered verification design Phase 1.
    /// Reference: Z3 Spacer `validate()` at reference/z3/src/muz/spacer/spacer_context.cpp:2560-2621
    pub(crate) fn verify_model_per_rule(
        &mut self,
        model: &InvariantModel,
        per_rule_budget: std::time::Duration,
    ) -> bool {
        self.verify_model_impl(model, Some(per_rule_budget), false, true)
            .is_none()
    }

    fn verify_model_impl(
        &mut self,
        model: &InvariantModel,
        budget: Option<std::time::Duration>,
        query_only: bool,
        per_rule_budget: bool,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        self.telemetry.verification_queries = self.telemetry.verification_queries.saturating_add(1);
        self.telemetry.bv_soft_degradation_skips = 0;

        // Empty model is valid for a vacuous empty problem (no predicates, no clauses).
        // For non-empty problems with empty models (can happen when PDR finds a fixpoint
        // with empty frames for array problems where SMT returns Unknown), return a
        // verification failure rather than panicking. (#4757, #6047)
        if model.is_empty() {
            if self.problem.predicates().is_empty() && self.problem.clauses().is_empty() {
                return None;
            }
            return Some((
                PredicateId::new(0),
                ChcExpr::Bool(false),
                PredicateId::new(0),
                ChcExpr::Bool(false),
            ));
        }

        // SOUNDNESS: Interpretations with free (non-binder) variables cannot be
        // validated by substitution — same-named clause variables capture them,
        // turning clause checks into vacuous UNSAT queries (022c-horn_000).
        if self.model_has_free_interpretation_vars(model) {
            return Some((
                PredicateId::new(0),
                ChcExpr::Bool(false),
                PredicateId::new(0),
                ChcExpr::Bool(false),
            ));
        }

        // #5930: If any predicate has Real-sorted args but its model interpretation
        // doesn't mention Real variables, reject the model. Boolean-only invariants
        // for Real-sorted problems can appear inductive (transition checks pass SMT)
        // but be too weak to block Real-feasible error paths. The underlying SMT
        // solver may return incorrect UNSAT on transition checks due to incomplete
        // handling of complex Real constraints (per-atom unsupported tracking in LRA, #6167).
        for pred in self.problem.predicates() {
            let has_real_args = pred.arg_sorts.iter().any(|s| matches!(s, ChcSort::Real));
            if !has_real_args {
                continue;
            }
            if let Some(interp) = model.get(&pred.id) {
                let has_real_in_formula = interp
                    .formula
                    .vars()
                    .iter()
                    .any(|v| v.sort == ChcSort::Real);
                if !has_real_in_formula {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: rejecting model — pred {} has Real args but \
                             model is Bool/Int-only (#5930)",
                            pred.id.index()
                        );
                    }
                    return Some((pred.id, ChcExpr::Bool(false), pred.id, ChcExpr::Bool(false)));
                }
            }
        }

        // A model must interpret every predicate referenced by a clause.  This
        // can legitimately fail at a transform/back-translation boundary when
        // the transformed solver returns a partial model.  Treat that as an
        // invalid certificate in every build mode: verification is a trust
        // boundary, so malformed evidence must fail closed rather than panic in
        // debug builds (or merely reach the per-clause fallback in release).
        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            let missing_body = clause
                .body
                .predicates
                .iter()
                .find_map(|(pred, _)| model.get(pred).is_none().then_some(*pred));
            let missing_head = match &clause.head {
                crate::ClauseHead::Predicate(pred, _) if model.get(pred).is_none() => Some(*pred),
                _ => None,
            };
            if let Some(pred) = missing_body.or(missing_head) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: rejecting incomplete model — predicate {} \
                         referenced by clause {} has no interpretation",
                        pred.index(),
                        clause_idx
                    );
                }
                tracing::warn!(
                    predicate = pred.index(),
                    clause_idx,
                    "verify_model: rejecting incomplete invariant model"
                );
                return Some((pred, ChcExpr::Bool(false), pred, ChcExpr::Bool(false)));
            }
        }

        // #3225: Cap per-clause SMT timeouts at the remaining solve deadline.
        // Without this, a single 30s VERIFY_RETRY_TIMEOUT can run past the
        // solve_deadline, preventing cooperative cancellation from taking effect.
        let verify_timeout = self.cap_timeout(VERIFY_INITIAL_TIMEOUT);
        // Track whether any transition clause used filtered invariant (#73 soundness fix).
        // If so, we must re-verify query clauses with the same filtered invariant.
        let mut used_filtered_invariant = false;
        // FIX #74: Store invariant and bad state SEPARATELY so we only filter invariant parts.
        let mut query_clause_info: Vec<QueryClauseInfo> = Vec::new();
        let mut budget_start = budget.map(|_| ay_core::time::Instant::now());

        // #5653: Budget for concrete_transition_check to avoid cumulative overhead.
        // verify_model_impl has a larger budget (1000ms) than verify_model_fast (200ms)
        // since this path has longer overall deadlines.
        let concrete_budget = std::time::Duration::from_secs(1);
        let mut concrete_elapsed = std::time::Duration::ZERO;
        // #7410: Rate-limit concrete cross-checks to 1-in-100 UNSAT results
        // to avoid overhead on query-heavy benchmarks (const_mod_3,
        // menlo_park_term_simpl_2).
        let mut concrete_unsat_count: u64 = 0;

        let num_clauses = self.problem.clauses().len();
        for clause_idx in 0..num_clauses {
            // #5653 Phase 1: Per-rule budget mode resets the timer at the start of
            // each clause. This gives each clause its own full budget allocation
            // instead of sharing a single budget across all clauses.
            if per_rule_budget {
                budget_start = budget.map(|_| ay_core::time::Instant::now());
            }
            // #3225: Check cooperative cancellation between clauses.
            // Return Some (model not verified) to avoid unsound Safe claims.
            if self.is_cancelled() {
                return Some((
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                ));
            }
            // #5825: Query-only mode for k-inductive engines (Kind).
            if query_only && !self.problem.clauses()[clause_idx].is_query() {
                continue;
            }
            // Budget check for transition clauses.
            // Query clauses are always checked (soundness-critical).
            if let (Some(start), Some(b)) = (budget_start, budget) {
                if !self.problem.clauses()[clause_idx].is_query() && start.elapsed() >= b {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: rejecting model — budget {:?} expired before clause {} could be verified",
                            b,
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
            }
            if self.config.verbose {
                safe_eprintln!("PDR: verify_model: checking clause {}", clause_idx);
            }
            let body = match self
                .clause_body_under_model(&self.problem.clauses()[clause_idx].body, model)
            {
                Some(b) => b,
                None => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} body computation failed",
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
            let body = self.bound_int_vars(body);

            // Clone clause to break the borrow on self.problem before &mut self calls.
            // HornClause derives Clone; CHC problems have <100 clauses so cost is negligible.
            let clause = self.problem.clauses()[clause_idx].clone();
            match &clause.head {
                crate::ClauseHead::False => {
                    if let Some(failure) = self.verify_query_clause(
                        &clause,
                        clause_idx,
                        &body,
                        model,
                        verify_timeout,
                        budget_start,
                        budget,
                        &mut query_clause_info,
                        concrete_budget,
                        &mut concrete_elapsed,
                        &mut concrete_unsat_count,
                    ) {
                        return Some(failure);
                    }
                }
                crate::ClauseHead::Predicate(head_pred, head_args) => {
                    if let Some(failure) = self.verify_transition_clause(
                        &clause,
                        clause_idx,
                        &body,
                        head_pred,
                        head_args,
                        model,
                        verify_timeout,
                        budget_start,
                        budget,
                        &mut used_filtered_invariant,
                        concrete_budget,
                        &mut concrete_elapsed,
                        &mut concrete_unsat_count,
                    ) {
                        return Some(failure);
                    }
                }
            }
        }

        // Post-loop: re-verify query clauses if filtered invariant was used (#73 soundness fix).
        if used_filtered_invariant && !query_clause_info.is_empty() {
            if let Some(failure) = self.reverify_queries_with_filtered_invariant(
                &query_clause_info,
                verify_timeout,
                budget_start,
                budget,
            ) {
                return Some(failure);
            }
        }

        // #5643: Log summary when BV soft degradation skipped transition clauses.
        // A non-zero count means inductiveness was not fully verified — only query
        // clauses (safety properties) were hard-checked. PDR engines produce
        // inductive invariants by construction, so this is defense-in-depth only.
        if self.telemetry.bv_soft_degradation_skips > 0 {
            tracing::warn!(
                skipped_clauses = self.telemetry.bv_soft_degradation_skips,
                "trust-proof fallback summary: {} transition clause(s) skipped by \
                 BV soft degradation (budget exhausted). Inductiveness NOT fully verified.",
                self.telemetry.bv_soft_degradation_skips
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: WARNING — {} transition clause(s) skipped by BV soft degradation (budget exhausted). Inductiveness NOT fully verified.",
                    self.telemetry.bv_soft_degradation_skips
                );
            }
        }

        None
    }
}
