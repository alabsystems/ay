// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcVar, PredicateId};

impl PdrSolver {
    /// Check if a scaled difference `(vi - vj = coeff * vk)` is preserved by all transitions.
    pub(in crate::pdr::solver) fn is_scaled_diff_preserved(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
        var_k: &ChcVar,
        coeff: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let (idx_i, idx_j, idx_k) = match (idx_i, idx_j, idx_k) {
            (Some(i), Some(j), Some(k)) => (i, j, k),
            _ => return false,
        };

        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];
            let head_k = &head_args[idx_k];

            if clause.body.predicates.len() != 1 {
                return false;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];
            let body_k = &body_args[idx_k];

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let pre_lhs = ChcExpr::sub(body_i.clone(), body_j.clone());
            let pre_rhs = ChcExpr::mul(ChcExpr::Int(coeff), body_k.clone());
            let pre_invariant = ChcExpr::eq(pre_lhs, pre_rhs);

            let post_lhs = ChcExpr::sub(head_i.clone(), head_j.clone());
            let post_rhs = ChcExpr::mul(ChcExpr::Int(coeff), head_k.clone());
            let post_invariant_violated = ChcExpr::or(
                ChcExpr::lt(post_lhs.clone(), post_rhs.clone()),
                ChcExpr::gt(post_lhs, post_rhs),
            );

            let mut parts: Vec<ChcExpr> = vec![clause_constraint, pre_invariant];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(base, post_invariant_violated);

            let _timeout_guard = self
                .smt
                .scoped_check_timeout(Some(std::time::Duration::from_millis(500)));
            let (smt_result, _) =
                Self::check_sat_with_ite_case_split(&mut self.smt, self.config.verbose, &query);
            match smt_result {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Scaled diff ({} - {} = {} * {}) NOT preserved",
                            var_i.name,
                            var_j.name,
                            coeff,
                            var_k.name
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Scaled diff ({} - {} = {} * {}) preservation check returned Unknown after case-split",
                            var_i.name, var_j.name, coeff, var_k.name
                        );
                    }
                    return false;
                }
            }
        }

        if !checked_any_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Scaled diff ({} - {} = {} * {}) preserved by all transitions",
                var_i.name,
                var_j.name,
                coeff,
                var_k.name
            );
        }
        true
    }

    /// Check if `vi = coeff * vk` is preserved by all self-loop transitions.
    pub(super) fn is_zero_init_coeff_preserved(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_k: &ChcVar,
        coeff: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_k = canonical_vars.iter().position(|v| v.name == var_k.name);
        let (idx_i, idx_k) = match (idx_i, idx_k) {
            (Some(i), Some(k)) => (i, k),
            _ => return false,
        };

        let max_frame = self.frames.len().saturating_sub(1);
        let f1_constraint = if max_frame >= 1 {
            self.cumulative_frame_constraint(max_frame, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        if self.config.verbose {
            safe_eprintln!(
                "PDR: is_zero_init_coeff_preserved {} = {} * {}: f1_constraint={}, frames.len={}",
                var_i.name,
                coeff,
                var_k.name,
                f1_constraint
                    .as_ref()
                    .map(|c| format!("{c}"))
                    .unwrap_or_else(|| "NONE".to_string()),
                self.frames.len()
            );
        }

        let mut checked_any = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                return false;
            }
            if clause.body.predicates.len() != 1 {
                return false;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any = true;

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let pre_inv = ChcExpr::eq(
                body_args[idx_i].clone(),
                ChcExpr::mul(ChcExpr::Int(coeff), body_args[idx_k].clone()),
            );

            let post_lhs = head_args[idx_i].clone();
            let post_rhs = ChcExpr::mul(ChcExpr::Int(coeff), head_args[idx_k].clone());
            let post_violated = ChcExpr::or(
                ChcExpr::lt(post_lhs.clone(), post_rhs.clone()),
                ChcExpr::gt(post_lhs, post_rhs),
            );

            let mut parts: Vec<ChcExpr> = vec![clause_constraint, pre_inv];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(base, post_violated);

            self.smt.reset();
            let smt_result = self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500));
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: zero-init coeff check {} = {} * {}: {}, clause_vars={}",
                    var_i.name,
                    coeff,
                    var_k.name,
                    match &smt_result {
                        SmtResult::Sat(_) => "SAT(NOT preserved)",
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => "UNSAT(preserved)",
                        SmtResult::Unknown => "UNKNOWN",
                    },
                    clause
                        .body
                        .constraint
                        .as_ref()
                        .map(|c| c.vars().len())
                        .unwrap_or(0)
                );
            }
            match smt_result {
                SmtResult::Sat(_) => return false,
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        checked_any
    }
}
