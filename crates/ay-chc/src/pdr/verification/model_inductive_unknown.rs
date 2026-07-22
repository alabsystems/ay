// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallback chain for transition clauses that return `SmtResult::Unknown`.
//!
//! Extracted from `model_inductive.rs`. Handles: fixed-int substitution,
//! head conjunct splitting, mod/div elimination, blocking lemma filtering,
//! case-split, algebraic verification, and executor fallback.

mod head_conjunct;

use super::*;

impl PdrSolver {
    /// Handle `SmtResult::Unknown` for a transition clause.
    ///
    /// Runs the full fallback chain. Returns `Some(failure_tuple)` on
    /// verification failure, `None` if any fallback proves the clause.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn handle_unknown_transition_clause(
        &mut self,
        clause: &crate::HornClause,
        clause_idx: usize,
        body: &ChcExpr,
        query: &ChcExpr,
        head: &ChcExpr,
        head_pred: &PredicateId,
        verify_timeout: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
        used_filtered_invariant: &mut bool,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        if self.config.verbose {
            safe_eprintln!(
                "PDR: verify_model: clause {} implication unknown",
                clause_idx
            );
            safe_eprintln!("  body={}", body);
            safe_eprintln!("  head={}", head);
        }
        // Budget check: if budget expired on a transition clause that
        // returned Unknown, reject the model.
        if let (Some(start), Some(b)) = (budget_start, budget) {
            if start.elapsed() > b {
                let has_bv = self
                    .problem
                    .predicates()
                    .iter()
                    .any(|p| p.arg_sorts.iter().any(|s| matches!(s, ChcSort::BitVec(_))));
                if has_bv {
                    // SOUNDNESS (#C1, sound-by-default): budget exceeded with an
                    // Unknown SMT result on this BV transition clause — we cannot
                    // certify it is inductive. Reject the model UNCONDITIONALLY
                    // (prefer `unknown` over an unverified Safe). Previously this
                    // fell open to `None` unless `strict_proofs`, a latent
                    // false-SAFE the public discharge gate cannot catch (it skips
                    // transition clauses).
                    self.telemetry.bv_soft_degradation_skips += 1;
                    tracing::warn!(
                        clause_idx,
                        budget_ms = b.as_millis() as u64,
                        total_skips = self.telemetry.bv_soft_degradation_skips,
                        "BV transition clause verification budget exceeded with \
                         Unknown — rejecting model (sound: prefer unknown)"
                    );
                    return Some((*head_pred, body.clone(), *head_pred, head.clone()));
                }
                // Mod/div: fall through to fallback paths instead of rejecting
                if Self::contains_mod_or_div(query) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} mod/div — budget {:?} exceeded but falling through to mod/div fallback paths",
                            clause_idx, b
                        );
                    }
                    // Don't reject — let mod/div fallback paths below handle it
                } else {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} REJECTED (budget {:?} exceeded, Unknown on transition is unsound)",
                            clause_idx, b
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
        }
        // #5510 soundness fix: reject model when transition clause
        // with nonlinear multiplication returns Unknown.
        if query.contains_nonlinear_mul() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} rejected (nonlinear multiplication, Unknown)",
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
        // #6047: Removed array fallback. Executor adapter handles natively.
        // MOD/DIV fallback (sound): try proving UNSAT on mod-free fragment.
        let fixed_int_subst = Self::fixed_int_subst_from_conjuncts(body);
        if !fixed_int_subst.is_empty() {
            let simplified_query = query.substitute(&fixed_int_subst).simplify_constants();
            if simplified_query != *query && self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} retrying with fixed-int substitution",
                    clause_idx
                );
            }
            self.smt.reset();
            let simplify_timeout = std::time::Duration::from_millis(200);
            let mut simplified_result = self
                .smt
                .check_sat_with_timeout(&simplified_query, simplify_timeout);
            if matches!(simplified_result, SmtResult::Unknown)
                && !Self::contains_mod_or_div(&simplified_query)
                && !simplified_query.contains_array_ops()
            {
                self.smt.reset();
                simplified_result = self.smt.check_sat_with_timeout(
                    &simplified_query,
                    self.current_verify_step_timeout(verify_timeout, budget_start, budget),
                );
            }
            match simplified_result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} passed after fixed-int substitution",
                            clause_idx
                        );
                    }
                    return None;
                }
                SmtResult::Sat(_) => {
                    // Fall back to the normal "implication failed" path below.
                }
                SmtResult::Unknown => {}
            }
        }

        // If the head is a conjunction, verify each conjunct separately.
        if let Some(result) = self.try_head_conjunct_splitting(
            clause_idx,
            body,
            query,
            head,
            head_pred,
            verify_timeout,
            budget_start,
            budget,
            used_filtered_invariant,
        ) {
            return result;
        }

        if Self::contains_mod_or_div(query) {
            let mod_free_timeout =
                self.current_verify_step_timeout(verify_timeout, budget_start, budget);
            if mod_div::mod_free_fragment_is_unsat(&mut self.smt, query, mod_free_timeout) {
                return None;
            }
            // #7048: Full mod elimination
            let mod_eliminated = query.eliminate_mod();
            if mod_eliminated != *query {
                self.smt.reset();
                let verify_retry_timeout = self.current_verify_retry_timeout(budget_start, budget);
                let elim_result = self
                    .smt
                    .check_sat_with_timeout(&mod_eliminated, verify_retry_timeout);
                match elim_result {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model: clause {} passed via full mod elimination (#7048)",
                                clause_idx
                            );
                        }
                        return None;
                    }
                    _ => {}
                }
            }
            // Mod/div transition: SMT incomplete (#3211, #5653)
            // SOUNDNESS FIX (#4919): unverified mod/div in budget mode must
            // REJECT the model, not silently accept it.
            if budget.is_some() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} REJECTED (mod/div Unknown, budget-mode, all fallbacks exhausted)",
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
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} rejected (mod/div Unknown, no budget)",
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
        // Blocking lemma fallback: try with only core invariants.
        let body_filtered = Self::filter_blocking_lemmas_aggressive(body);
        let head_filtered = Self::filter_blocking_lemmas(head);
        let query_filtered =
            ChcExpr::and(body_filtered.clone(), ChcExpr::not(head_filtered.clone()));
        self.smt.reset();
        let mut filtered_result = self.smt.check_sat_with_timeout(
            &query_filtered,
            self.current_verify_step_timeout(verify_timeout, budget_start, budget),
        );
        if matches!(filtered_result, SmtResult::Unknown) && !query_filtered.contains_array_ops() {
            if !Self::contains_mod_or_div(&query_filtered) {
                self.smt.reset();
                let verify_retry_timeout = self.current_verify_retry_timeout(budget_start, budget);
                filtered_result = self
                    .smt
                    .check_sat_with_timeout(&query_filtered, verify_retry_timeout);
            } else {
                let mod_free = query_filtered.eliminate_mod();
                self.smt.reset();
                filtered_result = self.smt.check_sat_with_timeout(
                    &mod_free,
                    self.current_verify_step_timeout(
                        std::time::Duration::from_secs(5),
                        budget_start,
                        budget,
                    ),
                );
            }
        }
        match filtered_result {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} passed via aggressive filter (unknown case)",
                        clause_idx
                    );
                }
                *used_filtered_invariant = true;
                return None;
            }
            _ => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} aggressive filtered query also failed/unknown",
                        clause_idx
                    );
                }
            }
        }

        // Case-split fallback: if body contains OR constraints
        let or_cases = Self::extract_or_cases_from_constraint(&body_filtered);
        if or_cases.len() > 1 {
            let mut all_cases_pass = true;
            for (case_idx, case_body) in or_cases.iter().enumerate() {
                let case_query =
                    ChcExpr::and(case_body.clone(), ChcExpr::not(head_filtered.clone()));
                self.smt.reset();
                match self.smt.check_sat_with_timeout(
                    &case_query,
                    self.current_verify_step_timeout(verify_timeout, budget_start, budget),
                ) {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model: clause {} case {} passed via case-split",
                                clause_idx,
                                case_idx
                            );
                        }
                    }
                    _ => {
                        if Self::verify_model_clause_algebraically(
                            clause,
                            &body_filtered,
                            &head_filtered,
                            case_body,
                        ) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} case {} passed via algebraic verification",
                                    clause_idx, case_idx
                                );
                            }
                            continue;
                        }

                        if Self::verify_implication_algebraically(case_body, &head_filtered) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} case {} passed via algebraic implication",
                                    clause_idx, case_idx
                                );
                            }
                            continue;
                        }

                        let case_split_timeout =
                            self.current_verify_step_timeout(verify_timeout, budget_start, budget);
                        if mod_div::verify_case_via_ite_case_split(
                            &mut self.smt,
                            self.config.verbose,
                            clause_idx,
                            Some(case_idx),
                            case_body,
                            &head_filtered,
                            case_split_timeout,
                        ) {
                            continue;
                        }

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model: clause {} case {} failed/unknown",
                                clause_idx,
                                case_idx
                            );
                        }
                        all_cases_pass = false;
                        break;
                    }
                }
            }
            if all_cases_pass {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} passed via case-split (all {} cases)",
                        clause_idx,
                        or_cases.len()
                    );
                }
                *used_filtered_invariant = true;
                return None;
            }
        }

        // ITE fallback even without OR case-splits
        if mod_div::verify_case_via_ite_case_split(
            &mut self.smt,
            self.config.verbose,
            clause_idx,
            None,
            &body_filtered,
            &head_filtered,
            verify_timeout,
        ) {
            *used_filtered_invariant = true;
            return None;
        }

        // Algebraic implication fallback
        if Self::verify_implication_algebraically(&body_filtered, &head_filtered) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} passed via algebraic implication",
                    clause_idx
                );
            }
            *used_filtered_invariant = true;
            return None;
        }

        // Best-effort: try again with a longer timeout
        let longer_timeout = std::time::Duration::from_secs(5);
        self.smt.reset();
        match self
            .smt
            .check_sat_with_timeout(&query_filtered, longer_timeout)
        {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                return None
            }
            SmtResult::Sat(mut m) => {
                if m.is_empty() {
                    Self::extract_equalities_from_formula(&query_filtered, &mut m);
                }
                cube::augment_model_from_equalities(&query_filtered, &mut m);
                if let Some((body_pred, body_args)) = clause.body.predicates.first() {
                    if let Some(pre) = self.extract_state_from_args(*body_pred, body_args, &m) {
                        return Some((*body_pred, pre, *head_pred, ChcExpr::Bool(false)));
                    }
                }
            }
            SmtResult::Unknown => {}
        }

        // #2477/#5970/#7109/#7165: Executor fallback for QF_LIA queries.
        if !self.problem.has_bv_sorts() && !query.contains_array_ops() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: implication clause {} UNKNOWN — retrying via executor fallback",
                    clause_idx
                );
            }
            self.smt.reset();
            let verify_retry_timeout = self.current_verify_retry_timeout(budget_start, budget);
            match self
                .smt
                .check_sat_with_executor_fallback_timeout(query, verify_retry_timeout)
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} implication passed via executor fallback",
                            clause_idx
                        );
                    }
                    return None;
                }
                _ => {}
            }
        }
        Some((
            PredicateId::new(0),
            ChcExpr::Bool(false),
            PredicateId::new(0),
            ChcExpr::Bool(false),
        ))
    }
}
