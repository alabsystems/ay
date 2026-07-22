// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Affine invariant transition preservation checks.
//!
//! Contains `is_affine_preserved_by_transitions` (coefficient-based),
//! `is_chc_expr_preserved_by_transitions` (expression-based), and
//! `is_chc_expr_preserved_by_transitions_with_hyps` (with extra hypotheses).

use super::super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};

impl PdrSolver {
    /// Check if an affine equality `c1*vi = c2*vj` is preserved by all self-transitions.
    pub(in crate::pdr::solver) fn is_affine_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        c1: i128,
        c2: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        if idx_i >= canonical_vars.len() || idx_j >= canonical_vars.len() {
            return false;
        }

        // Cache per-predicate invariants at level 1 to allow relative inductiveness checks.
        // This is needed for cases like dillig12_m where `D = 2*E` is only preserved assuming
        // the already-learned equality `A = B`.
        //
        // Filter F1 to only relevant lemma types to avoid SMT Unknown from large/complex queries.
        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        // Identify constant arguments (e.g., mode flags) and their init values, so we can
        // simplify ITE-heavy transition constraints before querying the SMT engine.
        let constant_arg_positions = self.detect_constant_arguments(predicate);
        let init_values = self.get_init_values(predicate);

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            // For now, only handle single-body transitions (no hyperedges)
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            // Skip inter-predicate transitions - they establish the initial invariant
            // but don't need preservation checking (the source invariant already holds).
            // Only self-transitions need preservation verification.
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];

            let pre_lhs = if c1 == 1 {
                body_i.clone()
            } else {
                ChcExpr::mul(ChcExpr::Int(c1), body_i.clone())
            };
            let pre_rhs = if c2 == 1 {
                body_j.clone()
            } else {
                ChcExpr::mul(ChcExpr::Int(c2), body_j.clone())
            };
            let pre_relation = ChcExpr::eq(pre_lhs, pre_rhs);

            let post_lhs = if c1 == 1 {
                head_i.clone()
            } else {
                ChcExpr::mul(ChcExpr::Int(c1), head_i.clone())
            };
            let post_rhs = if c2 == 1 {
                head_j.clone()
            } else {
                ChcExpr::mul(ChcExpr::Int(c2), head_j.clone())
            };
            let mut clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Substitute constant arguments to simplify ITEs like:
            //   I = ite(J=1, E+F, E)
            // into a straight-line assignment when J is a constant mode flag.
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for &pos in &constant_arg_positions {
                if pos >= canonical_vars.len() || pos >= body_args.len() {
                    continue;
                }
                let canon_name = &canonical_vars[pos].name;
                let val = match init_values.get(canon_name) {
                    Some(b) if b.min == b.max => b.min,
                    _ => continue,
                };
                let body_var = match &body_args[pos] {
                    ChcExpr::Var(v) => v.clone(),
                    _ => continue,
                };
                subst.push((body_var, ChcExpr::Int(val)));
            }
            if !subst.is_empty() {
                clause_constraint = clause_constraint.substitute(&subst).simplify_constants();
            }

            // Query: pre_relation AND f1(body_args) AND clause_constraint AND NOT(post_relation).
            //
            // Instead of encoding `NOT(post_relation)` as a disequality (which triggers expensive
            // expression splitting in the CHC SMT backend), split it explicitly into the two
            // strict cases: post_lhs < post_rhs OR post_lhs > post_rhs, and check both.
            let mut parts: Vec<ChcExpr> = vec![pre_relation, clause_constraint];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }

            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));

            for violation in [
                ChcExpr::lt(post_lhs.clone(), post_rhs.clone()),
                ChcExpr::gt(post_lhs.clone(), post_rhs.clone()),
            ] {
                let query = ChcExpr::and(base.clone(), violation);
                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(200))
                {
                    SmtResult::Sat(_) => return false,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                    SmtResult::Unknown => return false,
                }
            }
        }

        true
    }

    /// Check if a CHC expression is preserved by all self-transitions.
    ///
    /// Used for kernel-discovered equalities where we have a ChcExpr rather than
    /// variable indices and coefficients.
    pub(in crate::pdr::solver) fn is_chc_expr_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> bool {
        self.is_chc_expr_preserved_by_transitions_with_hyps(predicate, expr, canonical_vars, &[])
    }

    /// Check transition preservation with extra intra-batch hypotheses (#5399).
    ///
    /// Some kernel-discovered equalities are only relatively inductive: D=2C requires
    /// A=B as a hypothesis. The standard check uses frame[1] but that may not contain
    /// the batch-mate equality in its original form (it may be weakened to an inequality).
    /// This variant adds explicit extra hypotheses (substituted onto body args) to the
    /// SMT query, enabling layered inductive verification within a single kernel batch.
    pub(in crate::pdr::solver) fn is_chc_expr_preserved_by_transitions_with_hyps(
        &mut self,
        predicate: PredicateId,
        expr: &ChcExpr,
        canonical_vars: &[ChcVar],
        extra_hypotheses: &[ChcExpr],
    ) -> bool {
        // Get F1 constraint for relative inductiveness.
        // Filter F1 to only relevant lemma types to avoid SMT Unknown from large/complex queries.
        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        // #1362 D1: Two-phase check for self-transition clauses.
        // Phase 1: per-clause check (fast path). If any clause individually preserves
        // the expression, pass immediately.
        // Phase 2: disjunctive check. For nondeterministic branching (e.g., s_multipl_14
        // with or-split clauses), the expression may only be preserved by the disjunction
        // of all self-transitions, not by any single clause.

        // Collect self-transition clause data for potential disjunctive check.
        struct ClauseData {
            pre_relation: ChcExpr,
            post_relation: ChcExpr,
            clause_constraint: ChcExpr,
            f1_on_body: Option<ChcExpr>,
            hyps_on_body: Vec<ChcExpr>,
        }
        let mut failed_clauses: Vec<ClauseData> = Vec::new();

        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // For now, only handle single-body transitions (no hyperedges)
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            // Skip inter-predicate transitions - they establish the initial invariant
            // but don't need preservation checking (the source invariant already holds).
            // Only self-transitions need preservation verification.
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // Build substitutions: canonical vars -> body/head args
            let body_subst: Vec<(ChcVar, ChcExpr)> = canonical_vars
                .iter()
                .zip(body_args.iter())
                .map(|(canon, arg)| (canon.clone(), arg.clone()))
                .collect();

            let head_subst: Vec<(ChcVar, ChcExpr)> = canonical_vars
                .iter()
                .zip(head_args.iter())
                .map(|(canon, arg)| (canon.clone(), arg.clone()))
                .collect();

            // Pre-condition: expr holds on body args
            let pre_relation = expr.substitute(&body_subst);

            // Post-condition: expr holds on head args
            let post_relation = expr.substitute(&head_subst);

            // Clause constraint. Eliminate ite terms so the LIA SMT solver can
            // reason about both branches (#5399). Without this, clauses with
            // `(= I (ite (= J 1) X Y))` produce spurious SAT because the solver
            // can't evaluate the ite and finds a model that ignores it.
            let raw_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            // Rewrite mixed-sort equalities before ITE elimination (#5925).
            let clause_constraint = if raw_constraint.contains_mixed_sort_eq() {
                raw_constraint.eliminate_mixed_sort_eq().eliminate_ite()
            } else {
                raw_constraint.eliminate_ite()
            };

            let f1_on_body = f1_constraint
                .as_ref()
                .and_then(|f1| self.apply_to_args(predicate, f1, body_args));

            let hyps_on_body: Vec<ChcExpr> = extra_hypotheses
                .iter()
                .map(|hyp| hyp.substitute(&body_subst))
                .collect();

            // Phase 1: per-clause check (fast path)
            let mut parts: Vec<ChcExpr> = vec![pre_relation.clone(), clause_constraint.clone()];
            if let Some(ref f1b) = f1_on_body {
                parts.push(f1b.clone());
            }
            for hyp in &hyps_on_body {
                parts.push(hyp.clone());
            }

            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));

            // Split NOT(post_relation) into strict inequalities to avoid expensive
            // disequality processing in the SMT backend.
            let violations = match &post_relation {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let lhs = args[0].as_ref().clone();
                    let rhs = args[1].as_ref().clone();
                    vec![ChcExpr::lt(lhs.clone(), rhs.clone()), ChcExpr::gt(lhs, rhs)]
                }
                _ => {
                    vec![ChcExpr::not(post_relation.clone())]
                }
            };

            let mut clause_preserved = true;
            for violation in &violations {
                let query = ChcExpr::and(base.clone(), violation.clone());
                self.smt.reset();
                let result = self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(200));
                match result {
                    SmtResult::Sat(_) | SmtResult::Unknown => {
                        clause_preserved = false;
                        break;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {}
                }
            }

            if !clause_preserved {
                // Collect for Phase 2 disjunctive check
                failed_clauses.push(ClauseData {
                    pre_relation,
                    post_relation,
                    clause_constraint,
                    f1_on_body,
                    hyps_on_body,
                });
            }
            // If clause_preserved, this clause passes — continue to next
        }

        // If no clauses failed, all pass
        if failed_clauses.is_empty() {
            return true;
        }

        // Phase 2: disjunctive check for failed clauses (#1362 D1).
        // For or-split nondeterministic branching, build:
        //   pre AND f1 AND hyps AND (constraint_1 AND post_1 OR ... OR constraint_n AND post_n) => post
        // which is equivalent to checking:
        //   pre AND f1 AND hyps AND (OR_i (constraint_i AND post_i)) AND NOT(post) is UNSAT
        //
        // Since each clause may rename variables differently, we check:
        //   pre_0 AND f1 AND hyps AND (OR_i (constraint_i AND implies_post_i)) AND NOT(post_0) is UNSAT
        // where implies_post_i = (constraint_i => post_0) expressed as (constraint_i AND post_0).
        //
        // Simplification: all or-split clauses from the same original clause share the same
        // body_args and head_args pattern (they differ only in the constraint). Build a single
        // query: pre AND f1 AND hyps AND (constraint_1 OR constraint_2 OR ...) AND NOT(post).
        // This works because post is determined by head_args which are the same across splits.

        // Verify all failed clauses share the same pre/post (from same or-split origin).
        let ref_pre = &failed_clauses[0].pre_relation;
        let ref_post = &failed_clauses[0].post_relation;
        let same_structure = failed_clauses
            .iter()
            .all(|c| c.pre_relation == *ref_pre && c.post_relation == *ref_post);

        if !same_structure || failed_clauses.len() < 2 {
            // Different pre/post means different clause origins — can't merge.
            // Single failed clause already checked in Phase 1.
            return false;
        }

        // Build disjunction of clause constraints
        let constraint_disjunction = failed_clauses
            .iter()
            .map(|c| c.clause_constraint.clone())
            .reduce(ChcExpr::or)
            .unwrap();

        let mut parts: Vec<ChcExpr> = vec![ref_pre.clone(), constraint_disjunction];
        if let Some(ref f1b) = failed_clauses[0].f1_on_body {
            parts.push(f1b.clone());
        }
        for hyp in &failed_clauses[0].hyps_on_body {
            parts.push(hyp.clone());
        }

        let base = parts
            .into_iter()
            .reduce(ChcExpr::and)
            .unwrap_or(ChcExpr::Bool(true));

        let violations = match ref_post {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let lhs = args[0].as_ref().clone();
                let rhs = args[1].as_ref().clone();
                vec![ChcExpr::lt(lhs.clone(), rhs.clone()), ChcExpr::gt(lhs, rhs)]
            }
            _ => {
                vec![ChcExpr::not(ref_post.clone())]
            }
        };

        for violation in &violations {
            let query = ChcExpr::and(base.clone(), violation.clone());
            self.smt.reset();
            let result = self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(200));
            match result {
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            }
        }

        true
    }
}
