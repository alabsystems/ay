// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Head-conjunct fallback for unknown transition verification.

use super::*;

impl PdrSolver {
    /// Try verifying a transition clause by splitting head conjuncts.
    ///
    /// Returns `Some(Some(..))` for failure, `Some(None)` for success,
    /// `None` if head conjunct splitting is not applicable.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::pdr::verification) fn try_head_conjunct_splitting(
        &mut self,
        clause_idx: usize,
        body: &ChcExpr,
        _query: &ChcExpr,
        head: &ChcExpr,
        _head_pred: &PredicateId,
        verify_timeout: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
        _used_filtered_invariant: &mut bool,
    ) -> Option<Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)>> {
        let mut head_conjuncts = head.collect_conjuncts();
        head_conjuncts.retain(|c| !matches!(c, ChcExpr::Bool(true)));
        if head_conjuncts.len() <= 1 {
            return None;
        }

        let body_for_split = Self::filter_blocking_lemmas(body);

        self.smt.reset();
        match self.smt.check_sat_with_timeout(
            &body_for_split,
            self.current_verify_step_timeout(verify_timeout, budget_start, budget),
        ) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} passed (body is UNSAT/unreachable, early check)",
                        clause_idx
                    );
                }
                return Some(None);
            }
            _ => {}
        }

        let split_subst = Self::fixed_int_subst_from_conjuncts(&body_for_split);
        let mut all_conjuncts_unsat = true;
        let conj_timeout = self.current_verify_step_timeout(
            std::time::Duration::from_millis(200),
            budget_start,
            budget,
        );

        for (conj_idx, conjunct) in head_conjuncts.iter().enumerate() {
            let violation = match conjunct {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => args[0].as_ref().clone(),
                _ => ChcExpr::not(conjunct.clone()),
            };
            let mut conj_query = ChcExpr::and(body_for_split.clone(), violation.clone())
                .normalize_negations()
                .propagate_equalities()
                .simplify_constants();
            if !split_subst.is_empty() {
                conj_query = conj_query
                    .substitute(&split_subst)
                    .normalize_negations()
                    .propagate_equalities()
                    .simplify_constants();
            }
            if matches!(conj_query, ChcExpr::Bool(false))
                || cube::is_trivial_contradiction(&conj_query)
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: clause {} conjunct {} passed via syntactic contradiction",
                        clause_idx, conj_idx
                    );
                }
                continue;
            }

            self.smt.reset();
            let mut conj_result = self.smt.check_sat_with_timeout(&conj_query, conj_timeout);
            if matches!(conj_result, SmtResult::Unknown)
                && Self::has_verification_case_split_surface(&conj_query)
            {
                let split_result = Self::try_verification_case_split(
                    &mut self.smt,
                    self.config.verbose,
                    &conj_query,
                    conj_timeout,
                );
                if matches!(
                    split_result,
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: clause {} conjunct {} passed via recursive case-split",
                            clause_idx, conj_idx
                        );
                    }
                    continue;
                }
            }
            if matches!(conj_result, SmtResult::Unknown)
                && Self::contains_mod_or_div(&conj_query)
                && !Self::contains_mod_or_div(&violation)
            {
                let projected_query = mod_div::drop_mod_div_conjuncts(&conj_query)
                    .normalize_negations()
                    .normalize_strict_int_comparisons()
                    .propagate_equalities()
                    .simplify_constants();
                if projected_query != ChcExpr::Bool(true) && projected_query != conj_query {
                    if matches!(projected_query, ChcExpr::Bool(false))
                        || cube::is_trivial_contradiction(&projected_query)
                    {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: verify_model: clause {} conjunct {} passed via mod-free projection",
                                clause_idx, conj_idx
                            );
                        }
                        continue;
                    }

                    self.smt.reset();
                    let projection_timeout =
                        self.cap_timeout(std::time::Duration::from_millis(500));
                    if !projection_timeout.is_zero() {
                        let projected_result = self
                            .smt
                            .check_sat_with_timeout(&projected_query, projection_timeout);
                        if matches!(
                            projected_result,
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        ) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: clause {} conjunct {} passed via mod-free projection",
                                    clause_idx, conj_idx
                                );
                            }
                            continue;
                        }
                    }
                }
            }
            if matches!(conj_result, SmtResult::Unknown) && !conj_query.contains_array_ops() {
                if !Self::contains_mod_or_div(&conj_query) {
                    self.smt.reset();
                    conj_result = self.smt.check_sat_with_timeout(
                        &conj_query,
                        self.current_verify_step_timeout(verify_timeout, budget_start, budget),
                    );
                } else {
                    let mod_free = conj_query.eliminate_mod();
                    self.smt.reset();
                    let mod_timeout = self.current_verify_step_timeout(
                        std::time::Duration::from_secs(5),
                        budget_start,
                        budget,
                    );
                    let mod_timeout = if mod_timeout.is_zero() {
                        self.cap_timeout(std::time::Duration::from_millis(500))
                    } else {
                        mod_timeout
                    };
                    conj_result = self.smt.check_sat_with_timeout(&mod_free, mod_timeout);
                }
            }

            match conj_result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                other => {
                    if self.config.verbose {
                        let status = match &other {
                            SmtResult::Sat(_) => "SAT",
                            SmtResult::Unknown => "UNKNOWN",
                            _ => "NON-UNSAT",
                        };
                        safe_eprintln!(
                            "PDR: verify_model: clause {} conjunct {} ({} of {}) failed ({})",
                            clause_idx,
                            conj_idx,
                            conj_idx + 1,
                            head_conjuncts.len(),
                            status
                        );
                    }
                    all_conjuncts_unsat = false;
                    break;
                }
            }
        }

        if all_conjuncts_unsat {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: verify_model: clause {} passed via head conjunct splitting",
                    clause_idx
                );
            }
            return Some(None);
        }

        None
    }
}
