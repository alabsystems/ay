// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Horn-clause lowering and relational normalization.
//!
//! This module reasons about Horn-clause semantics: converting parsed
//! expressions into clauses, extracting body predicates and constraints,
//! and normalizing relational-encoding patterns into functional form.

use super::ChcParser;
use crate::{
    ActionId, ChcExpr, ChcOp, ChcResult, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl ChcParser {
    /// Convert an expression to a Horn clause and add it
    pub(super) fn add_expr_as_clause(&mut self, expr: ChcExpr) -> ChcResult<()> {
        self.add_expr_as_clause_with_optional_action(expr, None)
    }

    /// Convert an expression to an action-tagged Horn clause and add it.
    pub(super) fn add_expr_as_clause_with_action(
        &mut self,
        expr: ChcExpr,
        action: ActionId,
    ) -> ChcResult<()> {
        self.add_expr_as_clause_with_optional_action(expr, Some(action))
    }

    fn add_expr_as_clause_with_optional_action(
        &mut self,
        expr: ChcExpr,
        action: Option<ActionId>,
    ) -> ChcResult<()> {
        // Pattern: (=> body head) or (forall (...) (=> body head))
        match &expr {
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                let body = &*args[0];
                let head = &*args[1];
                self.add_implication(body, head, action)?;
            }
            _ => {
                // Treat as a fact: constraint => true (or constraint itself as head)
                // This handles forall-wrapped expressions or bare predicates
                self.add_fact(expr, action)?;
            }
        }
        Ok(())
    }

    /// Add an assertion as a clause (for (assert ...) commands)
    pub(super) fn add_assertion_as_clause(&mut self, expr: ChcExpr) -> ChcResult<()> {
        self.add_expr_as_clause(expr)
    }

    /// Add an implication body => head as a Horn clause
    fn add_implication(
        &mut self,
        body: &ChcExpr,
        head: &ChcExpr,
        action: Option<ActionId>,
    ) -> ChcResult<()> {
        // Extract predicates and constraints from body
        let (preds, constraint) = self.extract_body_parts(body);

        // Check if head is a predicate application
        let is_head_predicate =
            matches!(head, ChcExpr::PredicateApp(..)) || self.try_extract_predicate(head).is_some();
        let is_head_false = matches!(head, ChcExpr::Bool(false));
        let is_head_true = matches!(head, ChcExpr::Bool(true));

        // If head is true, the clause is trivially satisfied - skip it
        if is_head_true {
            tracing::debug!("Skipping trivially satisfied clause: body => true");
            return Ok(());
        }

        // If head is a constraint (not predicate, not false), transform:
        // body => constraint  -->  body ∧ NOT(constraint) => false
        if !is_head_predicate && !is_head_false {
            tracing::debug!(
                "Transforming non-predicate head: body => {head} --> body ∧ NOT({head}) => false"
            );

            // Add NOT(head) to the body constraints
            let negated_head = ChcExpr::not(head.clone());
            let new_constraint = match constraint {
                Some(c) => Some(ChcExpr::and(c, negated_head)),
                None => Some(negated_head),
            };

            let clause_body = if new_constraint.is_some() || !preds.is_empty() {
                ClauseBody::new(preds, new_constraint)
            } else {
                ClauseBody::constraint(ChcExpr::Bool(true))
            };

            let clause = HornClause::new(clause_body, ClauseHead::False);
            self.add_clause_with_optional_action(clause, action);
        } else {
            // Normal case: head is a predicate or false
            // Apply relational encoding normalization: substitute primed variables
            // from body equalities into the head predicate
            let (normalized_constraint, substitutions) =
                self.normalize_relational_encoding(&preds, constraint, head);

            // Apply substitutions to head if any were found
            let normalized_head = if substitutions.is_empty() {
                head.clone()
            } else {
                self.apply_substitutions_to_head(head, &substitutions)
            };

            let clause_head = self.determine_head(&normalized_head)?;

            let clause_body = if normalized_constraint.is_some() || !preds.is_empty() {
                ClauseBody::new(preds, normalized_constraint)
            } else {
                ClauseBody::constraint(ChcExpr::Bool(true))
            };

            let clause = HornClause::new(clause_body, clause_head);
            self.add_clause_with_optional_action(clause, action);
        }

        Ok(())
    }

    /// Add a fact (head predicate that's always true)
    fn add_fact(&mut self, expr: ChcExpr, action: Option<ActionId>) -> ChcResult<()> {
        // A *predicate-free* assertion `(assert C)` (e.g. `true`, `(and true
        // true)`, or any ground/quantified constraint whose matrix mentions no
        // uninterpreted predicate — the parser strips the `forall`) is NOT a
        // reachable fact: it is a constraint that must simply hold. The old code
        // fed it to determine_head(), which maps EVERY non-predicate expression
        // — including a *valid* one — to ClauseHead::False, i.e. a `true =>
        // false` query that is unconditionally UNSAT. That made
        // `(set-logic HORN)(assert true)` (and `(and true true)`, `(forall ((x))
        // true)`, …) answer `unsat` where z3 correctly says `sat` — a wrong
        // verdict, and one AY's own trace validator flagged ("Expected 1 used
        // predicate, found 0") but only demoted to a warning.
        //
        // Encode a predicate-free assertion the sound way instead, mirroring the
        // non-predicate-head transform in add_implication: `NOT(C) => false`.
        // Then a satisfiable C yields an *unsatisfiable* query body (the error
        // state is unreachable ⇒ SAFE ⇒ sat), and only a genuinely-false C
        // yields `true => false` (correctly UNSAT). `(assert false)` still maps
        // to `NOT(false) => false` ≡ `true => false` ⇒ unsat, unchanged.
        //
        // Facts that DO mention a predicate (`(assert (P 0))`, `(assert (and
        // (P x) ...))`) keep the original head-fact encoding untouched.
        let (preds, _) = self.extract_body_parts(&expr);
        if preds.is_empty() {
            let negated = ChcExpr::not(expr);
            let clause = HornClause::new(ClauseBody::constraint(negated), ClauseHead::False);
            self.add_clause_with_optional_action(clause, action);
            return Ok(());
        }
        let clause_head = self.determine_head(&expr)?;
        let clause = HornClause::new(ClauseBody::constraint(ChcExpr::Bool(true)), clause_head);
        self.add_clause_with_optional_action(clause, action);
        Ok(())
    }

    fn add_clause_with_optional_action(&mut self, clause: HornClause, action: Option<ActionId>) {
        if let Some(action) = action {
            self.problem.add_clause_with_action(clause, action);
        } else {
            self.problem.add_clause(clause);
        }
    }

    /// Extract predicate applications and constraints from body
    pub(super) fn extract_body_parts(
        &self,
        body: &ChcExpr,
    ) -> (Vec<(PredicateId, Vec<ChcExpr>)>, Option<ChcExpr>) {
        let mut preds = Vec::new();
        let mut constraints = Vec::new();

        self.collect_body_parts(body, &mut preds, &mut constraints);

        let constraint = if constraints.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(constraints))
        };

        (preds, constraint)
    }

    /// Recursively collect body parts
    fn collect_body_parts(
        &self,
        expr: &ChcExpr,
        preds: &mut Vec<(PredicateId, Vec<ChcExpr>)>,
        constraints: &mut Vec<ChcExpr>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    self.collect_body_parts(arg, preds, constraints);
                }
            }
            _ => {
                // Check if this is a predicate application
                if let Some((pred_id, args)) = self.try_extract_predicate(expr) {
                    preds.push((pred_id, args));
                } else {
                    constraints.push(expr.clone());
                }
            }
        }
    }

    /// Try to extract a predicate application from an expression
    pub(super) fn try_extract_predicate(
        &self,
        expr: &ChcExpr,
    ) -> Option<(PredicateId, Vec<ChcExpr>)> {
        match expr {
            ChcExpr::PredicateApp(_name, id, args) => {
                // Convert Arc<ChcExpr> to ChcExpr
                let arg_exprs: Vec<ChcExpr> = args.iter().map(|a| (**a).clone()).collect();
                Some((*id, arg_exprs))
            }
            _ => None,
        }
    }

    /// Determine the head of a clause from an expression
    pub(super) fn determine_head(&self, expr: &ChcExpr) -> ChcResult<ClauseHead> {
        match expr {
            ChcExpr::Bool(false) => Ok(ClauseHead::False),
            ChcExpr::Bool(true) => {
                // true head means the clause is trivially satisfied - skip it
                Ok(ClauseHead::False) // This will be filtered out
            }
            ChcExpr::PredicateApp(_name, id, args) => {
                // Predicate application in the head
                let arg_exprs: Vec<ChcExpr> = args.iter().map(|a| (**a).clone()).collect();
                Ok(ClauseHead::Predicate(*id, arg_exprs))
            }
            _ => {
                // Other expressions - check if there's a nested predicate application
                if let Some((pred_id, args)) = self.try_extract_predicate(expr) {
                    Ok(ClauseHead::Predicate(pred_id, args))
                } else {
                    // Not a predicate - treat as a constraint that should be true
                    // This is typically an error in the input
                    tracing::warn!("Non-predicate expression in clause head: {expr}");
                    Ok(ClauseHead::False)
                }
            }
        }
    }

    /// Normalize relational encoding by substituting primed variables in head predicates.
    ///
    /// For clauses with explicit primed variables like:
    ///   (Inv i) ∧ (< i 10) ∧ (= i_prime (+ i 1)) => Inv(i_prime)
    ///
    /// This transforms them to functional encoding:
    ///   (Inv i) ∧ (< i 10) => Inv((+ i 1))
    ///
    /// The transformation finds equalities `(= VAR EXPR)` or `(= EXPR VAR)` where:
    /// - VAR is a variable that appears in the head predicate arguments
    /// - VAR does NOT appear in any body predicate (it's a "next-state" variable)
    /// - VAR does NOT appear anywhere else in the constraint (except the defining equality)
    /// - EXPR is an expression defining VAR in terms of "current-state" variables
    ///
    /// It then substitutes VAR with EXPR in the head and removes the equality from the body.
    fn normalize_relational_encoding(
        &self,
        preds: &[(PredicateId, Vec<ChcExpr>)],
        constraint: Option<ChcExpr>,
        head: &ChcExpr,
    ) -> (Option<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
        // Only apply to clauses with body predicates (transition rules)
        // Fact clauses (no body predicates) should not be transformed
        if preds.is_empty() {
            return (constraint, Vec::new());
        }

        // Collect variables that appear in the head predicate arguments
        let head_vars: FxHashSet<ChcVar> = head.vars().into_iter().collect();

        if head_vars.is_empty() {
            return (constraint, Vec::new());
        }

        // Collect variables that appear in body predicates ("current-state" variables)
        // These should NOT be substituted, only "next-state" variables should be
        let mut body_pred_vars: FxHashSet<ChcVar> = FxHashSet::default();
        for (_pred_id, args) in preds {
            for arg in args {
                for v in arg.vars() {
                    body_pred_vars.insert(v);
                }
            }
        }

        // Extract equalities from the constraint
        let Some(ref cstr) = constraint else {
            return (constraint, Vec::new());
        };

        let mut substitutions: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let mut equalities_to_remove: FxHashSet<usize> = FxHashSet::default();

        // Collect all conjuncts from the constraint
        let conjuncts = cstr.collect_conjuncts();

        // Build a set of variables used in each conjunct (for checking if var is used elsewhere)
        let conjunct_vars: Vec<FxHashSet<ChcVar>> = conjuncts
            .iter()
            .map(|c| c.vars().into_iter().collect())
            .collect();

        for (idx, conjunct) in conjuncts.iter().enumerate() {
            if let Some((var, expr)) = self.extract_var_expr_equality(conjunct) {
                // Check if this variable appears in the head
                if !head_vars.contains(&var) {
                    continue;
                }

                // CRITICAL: Only substitute if the variable does NOT appear in any body predicate
                // This distinguishes relational encoding (i_prime only in head + equality)
                // from constraint encoding (x in body predicate + equality like x = 0)
                if body_pred_vars.contains(&var) {
                    continue;
                }

                // CRITICAL: Check if the variable appears in any OTHER conjunct (not just body preds)
                // This handles fact clauses where constraints like (= x 0) define values
                let var_used_elsewhere = conjunct_vars
                    .iter()
                    .enumerate()
                    .any(|(i, vars)| i != idx && vars.contains(&var));

                if var_used_elsewhere {
                    continue;
                }

                // Check that expr variables are all from body predicates (current-state)
                // This ensures we're substituting next-state = f(current-state)
                let expr_vars: FxHashSet<ChcVar> = expr.vars().into_iter().collect();

                // Accept substitution if all variables in the expression appear in body predicates
                // (we already checked preds is non-empty, so body_pred_vars should be populated)
                let expr_uses_current_state = expr_vars.iter().all(|v| body_pred_vars.contains(v));

                if expr_uses_current_state {
                    tracing::debug!("Relational encoding: substituting {var} with {expr} in head");
                    substitutions.push((var, expr));
                    equalities_to_remove.insert(idx);
                }
            }
        }

        if substitutions.is_empty() {
            return (constraint, Vec::new());
        }

        // Rebuild constraint without the removed equalities
        let remaining_conjuncts: Vec<ChcExpr> = conjuncts
            .into_iter()
            .enumerate()
            .filter(|(idx, _)| !equalities_to_remove.contains(idx))
            .map(|(_, c)| c)
            .collect();

        let new_constraint = if remaining_conjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(remaining_conjuncts))
        };

        (new_constraint, substitutions)
    }

    /// Extract (variable, expression) pair from an equality constraint.
    /// Returns Some((var, expr)) if the equality is of form (= VAR EXPR) or (= EXPR VAR)
    /// where VAR is a simple variable and EXPR is not the same variable.
    fn extract_var_expr_equality(&self, expr: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
        if let ChcExpr::Op(ChcOp::Eq, args) = expr {
            if args.len() == 2 {
                let left = args[0].as_ref();
                let right = args[1].as_ref();

                // Check (= VAR EXPR) pattern
                if let ChcExpr::Var(v) = left {
                    // Make sure right side is not the same variable
                    if !matches!(right, ChcExpr::Var(v2) if v2 == v) {
                        return Some((v.clone(), right.clone()));
                    }
                }

                // Check (= EXPR VAR) pattern
                if let ChcExpr::Var(v) = right {
                    // Make sure left side is not the same variable
                    if !matches!(left, ChcExpr::Var(v2) if v2 == v) {
                        return Some((v.clone(), left.clone()));
                    }
                }
            }
        }
        None
    }

    /// Apply substitutions to a head expression (predicate application)
    fn apply_substitutions_to_head(&self, head: &ChcExpr, subst: &[(ChcVar, ChcExpr)]) -> ChcExpr {
        if subst.is_empty() {
            return head.clone();
        }
        head.substitute(subst)
    }
}
