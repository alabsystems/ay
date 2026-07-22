// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query clause (safety property) verification.
//!
//! Extracted from `model.rs` — handles the `ClauseHead::False` match arm in
//! `verify_model_impl`.

use super::*;

impl PdrSolver {
    /// Verify a single safety/query clause (`ClauseHead::False`).
    ///
    /// Returns `Some(failure_tuple)` if verification fails (propagates as early
    /// return from `verify_model_impl`). Returns `None` if the clause passes
    /// (caller continues the loop). Populates `query_clause_info` for the
    /// post-loop filtered-invariant re-check.
    pub(super) fn verify_query_clause(
        &mut self,
        clause: &crate::HornClause,
        clause_idx: usize,
        body: &ChcExpr,
        model: &InvariantModel,
        verify_timeout: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
        query_clause_info: &mut Vec<QueryClauseInfo>,
        concrete_budget: std::time::Duration,
        concrete_elapsed: &mut std::time::Duration,
        concrete_unsat_count: &mut u64,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        if self.config.verbose {
            safe_eprintln!("PDR: verify_model: clause {} is query", clause_idx);
            safe_eprintln!("PDR: verify_model: body={}", body);
        }
        // FIX #74: Store invariant and bad state SEPARATELY.
        // Extract only invariant parts (predicate interpretations), keep constraint separate.
        let invariant_body = self
            .extract_invariant_only_from_body(&clause.body, model)
            .unwrap_or(ChcExpr::Bool(true));
        let bad_state = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let pred_info = clause
            .body
            .predicates
            .first()
            .map(|(pred, args)| (*pred, args.clone()));
        query_clause_info.push((pred_info, invariant_body, bad_state));

        // Fast-path: a syntactic contradiction implies UNSAT (safe to skip SMT).
        if cube::is_trivial_contradiction(body) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} is trivially UNSAT (contradiction)",
                    clause_idx
                );
            }
            return None;
        }

        // Disjunction-splitting for back-translated multi-def interpretations.
        // Placed after syntactic contradiction (O(1)) but before full SMT check.
        if let Some(proven) =
            Self::try_disjunction_split_verification(&mut self.smt, body, verify_timeout)
        {
            if proven {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} proven via disjunction-split",
                        clause_idx
                    );
                }
                return None;
            }
        }
        if self.config.verbose {
            safe_eprintln!("PDR: verify_model: no trivial contradiction, calling SMT");
        }
        self.smt.reset();
        let verify_step_timeout =
            self.current_verify_step_timeout(verify_timeout, budget_start, budget);
        // Use a short timeout by default to avoid getting stuck on mod-heavy queries.
        // If we get `Unknown` on a mod-free query, retry once with a longer timeout;
        // this avoids spurious verification failures on hard-but-linear queries.
        let mut result = self.smt.check_sat_with_timeout(body, verify_step_timeout);
        if matches!(result, SmtResult::Unknown)
            && !Self::contains_mod_or_div(body)
            && !body.contains_array_ops()
        {
            self.smt.reset();
            result = self.smt.check_sat_with_timeout(
                body,
                self.current_verify_retry_timeout(budget_start, budget),
            );
        }
        match result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // #5803: Concrete cross-check on query clauses.
                // A false-UNSAT here produces a false Safe — the most dangerous
                // soundness failure. Cross-check with concrete evaluation as a
                // defense-in-depth layer independent of SMT.
                //
                // Query clauses are ALWAYS cross-checked while the concrete
                // budget lasts. The #7410 1-in-100 sampling applies only to
                // transition clauses: on 022c-horn_000 the rate limiter
                // (shared counter already >10 from transition clauses) skipped
                // the query-clause check, letting an SMT false-UNSAT through
                // as a false Safe. Query clauses are one per model
                // verification and the check is bounded by `concrete_budget`.
                *concrete_unsat_count += 1;
                if *concrete_elapsed < concrete_budget {
                    let check_start = ay_core::time::Instant::now();
                    if let Some(cex_model) =
                        concrete::transition_check(body, &ChcExpr::Bool(true), body)
                    {
                        tracing::warn!(
                            clause_idx,
                            ?cex_model,
                            "verify_model: query clause SMT said UNSAT but concrete check found SAT (#5803)"
                        );
                        return Some((
                            PredicateId::new(0),
                            ChcExpr::Bool(false),
                            PredicateId::new(0),
                            ChcExpr::Bool(false),
                        ));
                    }
                    *concrete_elapsed += check_start.elapsed();
                }
            }
            SmtResult::Sat(m) => {
                let mut m = m;
                if m.is_empty() {
                    Self::extract_equalities_from_formula(body, &mut m);
                }
                cube::augment_model_from_equalities(body, &mut m);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} (query) failed - body is SAT: {:?}",
                        clause_idx,
                        m
                    );
                }
                // For query clauses, return the state that reaches false
                if let Some((pred, args)) = clause.body.predicates.first() {
                    if let Some(s) = self.extract_state_from_args(*pred, args, &m) {
                        return Some((*pred, s, *pred, ChcExpr::Bool(false)));
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
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} (query) body is Unknown",
                        clause_idx
                    );
                }
                // #6047: Removed array fallback. Executor adapter
                // handles array queries natively.

                // Mod-substitution fallback: if the body contains equalities
                // like (= (mod X k) Y), substitute (mod X k) → Y to create a
                // mod-free formula that preserves semantics. Also adds range
                // constraint Y >= 0 ∧ Y < k since (mod X k) ∈ [0, k-1]. (#3211)
                if Self::contains_mod_or_div(body) {
                    if let Some(subst_body) = mod_div::substitute_mod_equalities_in_body(body) {
                        if matches!(subst_body, ChcExpr::Bool(false)) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} (query) passed via mod-substitution (trivially false)",
                                    clause_idx
                                );
                            }
                            return None;
                        }
                        self.smt.reset();
                        let verify_retry_timeout =
                            self.current_verify_retry_timeout(budget_start, budget);
                        match self
                            .smt
                            .check_sat_with_timeout(&subst_body, verify_retry_timeout)
                        {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model: clause {} (query) passed via mod-substitution",
                                        clause_idx
                                    );
                                }
                                return None;
                            }
                            _ => {}
                        }
                    }
                }

                // OR/DISEQ/ITE fallback: use the recursive case-split checker to try
                // to prove UNSAT when the SMT backend returns Unknown (common on LIA
                // with disjunctions or disequalities, e.g., three_dots_moving_2).
                if !Self::contains_mod_or_div(body)
                    && !body.contains_array_ops()
                    && Self::has_verification_case_split_surface(body)
                {
                    let split_timeout = self.current_verify_step_timeout(
                        VERIFY_CASE_SPLIT_TIMEOUT,
                        budget_start,
                        budget,
                    );
                    let split_result = Self::try_verification_case_split(
                        &mut self.smt,
                        self.config.verbose,
                        body,
                        split_timeout,
                    );
                    if matches!(
                        split_result,
                        SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_)
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model: clause {} (query) passed via recursive case-split",
                                clause_idx
                            );
                        }
                        return None;
                    }
                }
                // MOD/DIV fallback (sound): if SMT is Unknown on a mod/div-heavy body,
                // try proving UNSAT on the mod-free fragment. If that fragment is SAT,
                // we cannot prove the query unreachable (conservatively fail verification).
                let mod_free_timeout =
                    self.current_verify_step_timeout(verify_timeout, budget_start, budget);
                if mod_div::mod_free_fragment_is_unsat(&mut self.smt, body, mod_free_timeout) {
                    return None;
                }
                // Mod-substitution fallback (#3211): if the body contains equalities
                // of the form (= (mod X k) Y), substitute (mod X k) → Y throughout
                // the body and add range constraints 0 ≤ Y < k. This resolves the
                // common pattern where the invariant (= (mod counter 2) toggle) makes
                // the error unreachable but the SMT solver can't handle the mod.
                if Self::contains_mod_or_div(body) {
                    if let Some(subst_body) = mod_div::substitute_mod_equalities_in_body(body) {
                        if matches!(subst_body, ChcExpr::Bool(false)) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} (query) passed via mod-substitution (trivially false)",
                                    clause_idx
                                );
                            }
                            return None;
                        }
                        self.smt.reset();
                        match self.smt.check_sat_with_timeout(
                            &subst_body,
                            self.current_verify_step_timeout(verify_timeout, budget_start, budget),
                        ) {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model: clause {} (query) passed via mod-substitution",
                                        clause_idx
                                    );
                                }
                                return None;
                            }
                            _ => {}
                        }
                    }
                }
                // #2477/#5970/#7109/#7165: Executor fallback for QF_LIA queries.
                // The internal DPLL(T) lacks theory propagation and is
                // incomplete on QF_LIA with many disequalities. Route through
                // the full ay-dpll Executor which has bound propagation + CEGQI.
                // #5595: BV problems are NOT pure QF_LIA — Unknown is expected.
                // #7165: mod/div gate removed — executor handles mod/div via
                // theory propagation after CHC-level Euclidean decomposition.
                if !self.problem.has_bv_sorts() && !body.contains_array_ops() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: query clause {} UNKNOWN — retrying via executor fallback",
                            clause_idx
                        );
                    }
                    self.smt.reset();
                    let verify_retry_timeout =
                        self.current_verify_retry_timeout(budget_start, budget);
                    match self
                        .smt
                        .check_sat_with_executor_fallback_timeout(body, verify_retry_timeout)
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} (query) passed via executor fallback",
                                    clause_idx
                                );
                            }
                            return None;
                        }
                        _ => {}
                    }
                }
                return Some((
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                ));
            }
        }
        None
    }
}
